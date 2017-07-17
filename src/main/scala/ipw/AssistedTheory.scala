package ipw

import scala.annotation.tailrec
import inox._
import inox.trees._
import inox.trees.dsl._
import welder._
import ipw.gui.AssistantWindow
import ipw.core._
import ipw.concurrent.SynchronizedChannel
import ipw.concurrent.Utils._
import ipw.io._
import ipw.ast._
import java.util.concurrent.BlockingDeque
import java.util.concurrent.LinkedBlockingDeque
import scala.concurrent.Promise
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.Future
import scala.concurrent.duration.Duration
import scala.collection.mutable.{ Queue => MutableQueue }
import scala.collection.mutable.{ Set => MutableSet }
import ipw.io.IWFileInterface

trait AssistedTheory
  extends Theory
  with Deconstructions
  with Analysers
  with PathTreeOps
  with Suggestions
  with AssistantWindow
  with IOs { self: AssistedTheory with IWFileInterface with GenericRuleProvider =>

  type IPWResult = RuleResult
  type IPWStructuralInductionHypothesis = StructuralInductionHypothesis

  protected[ipw] type ProofState = (Expr, Seq[NamedSuggestion], Map[String, IPWResult], Boolean)
  protected[ipw] type UpdateStep = Suggestion
  protected[ipw] type ChoosingEnd = SynchronizedChannel.End[ProofState, UpdateStep]
  protected[ipw] type SuggestingEnd = SynchronizedChannel.End[UpdateStep, ProofState]
  protected[ipw] type StatusCallback = (Expr, Status) => Unit
  private type ProofContext = (ProofCase, WindowTab, Future[Unit])

  protected[ipw] sealed abstract class Status(val stage: Int, val message: String)
  protected[ipw] case object InQueue extends Status(0, "In queue")
  protected[ipw] case object Proving extends Status(1, "Trying to conclude...")
  protected[ipw] case object ProofFailed extends Status(2, "Could not conclude.")
  protected[ipw] case object ProofSucceeded extends Status(3, "Success!")

  private sealed abstract class SolveRequest
  private case class ProveConjecture(conjecture: Expr, using: IPWResult) extends SolveRequest
  private case object StopProving extends SolveRequest
  private case object RequestRestart extends SolveRequest

  sealed abstract class GUIContext
  case class NewWindow(tabTitle: String, proofDoc: ProofDocument) extends GUIContext
  private case class NewTab(title: String, win: Window) extends GUIContext
  private case class Following(ctx: ProofContext) extends GUIContext

  private val UndoSuggestion = ("Undo", Undo)
  private val BFSSuggestion = ("Breadth-first Search", BFS)

  private val RestartRequestedFailureReason = Aborted("RestartRequested")

  private final def onGUITab(ctx: GUIContext)(f: ProofContext => Attempt[IPWResult]): Attempt[IPWResult] = ctx match {
    case NewWindow(tabTitle, doc) =>
      val willTerminate = Promise[Unit] // them lies tho
      val res = onGUITab(NewTab(tabTitle, Await.result(openAssistantWindow(willTerminate.future, doc), Duration.Inf)))(f)
      willTerminate.success(())
      doc.save()
      res

    case NewTab(title, window) =>
      val (choosingEnd, suggestingEnd) = SynchronizedChannel[ProofState, UpdateStep]()
      val tab = window.openNewTab(title, choosingEnd)
      val willTerminate = Promise[Unit]
      val proofCase = window.proofDocument.getCase(title, suggestingEnd, () => window.show)
      val res = f(proofCase, Await.result(tab, Duration.Inf), willTerminate.future) match {
        case attempt @ Success(_) =>
          proofCase.setComplete
          attempt
        case other => other
      }
      willTerminate.success(())
      res

    case Following(ctx) => f(ctx)
  }
  /*
  private final def proveBFS(from: Expr, step: Expr, thms: Map[String, IPWResult], ihs: Seq[StructuralInductionHypotheses],
    prover: BlockingDeque[SolveRequest], acc: IPWResult, willTerminate: Future[Unit]): Unit = {
    type Element = (Expr, Map[String, IPWResult], Suggestion, IPWResult)

    @tailrec
    def waitForProver(n: Int = -1): Unit = if (prover.size() > 1000) {
      println(s"Waiting for prover... (${prover.size()} left to prove)")
      Thread.sleep(1000)
      waitForProver()
    }

    val queue = MutableQueue[Element]()
    val seen = MutableSet[Expr]()
    val (suggestions, newThms) = analyse(step, thms, ihs)

    suggestions foreach (s => queue.enqueue((step, newThms, s._2, acc)))

    @tailrec
    def process(count: Int, alreadySeen: Int): Unit = {
      val (expr, thms, sugg, acc) = queue.dequeue()

      if (count % 100 == 0) {
        println(s"Processed $count Suggestions (already seen is $alreadySeen and seen is ${seen.size})")
      }

      sugg match {
        case RewriteSuggestion(_, RewriteResult(next, proof)) if !seen(next) =>
          seen.add(next)

          val newAcc = prove(from === next, acc, proof)
          prover.putLast(ProveConjecture(next, newAcc))
          println(s"Added (${prover.size()}): $next")

          val (suggestions, newThms) = analyse(next, thms, ihs)

          waitForProver()

          if (!willTerminate.isCompleted) {
            suggestions foreach (s => queue.enqueue((next, newThms, s._2, newAcc)))
            process(count + 1, alreadySeen)
          }

        case _ => process(count + 1, alreadySeen + 1)
      }
    }

    process(0, 0)
  }*/

  private final def IPWproveInner(expr: Expr, thms: Map[String, IPWResult], ihses: Map[String, IPWStructuralInductionHypothesis], guiCtx: GUIContext): Attempt[IPWResult] = onGUITab(guiCtx) {
    case (suggestingEnd, tab, willTerminate) =>

      val proofAttempts = new LinkedBlockingDeque[SolveRequest]

      def updateStatus(e: Expr, status: Status): Unit = {
        tab.statusCallback(e, status)
      }

      @tailrec
      def deepen(history: List[(Expr, IPWResult, Map[String, IPWResult])], step: Expr, accumulatedProof: IPWResult, thms: Map[String, IPWResult], undo: Boolean = false): Unit = {
        proofAttempts.putFirst(ProveConjecture(step, accumulatedProof))
        updateStatus(step, InQueue)

        val (suggestions, newThms) = analyse(step, thms, ihses)
        val extraSuggestions = (if (!history.isEmpty) Seq(UndoSuggestion) else Nil) :+ BFSSuggestion

        suggestingEnd.write((step, suggestions ++ extraSuggestions, newThms, undo))

        val choice = suggestingEnd.read

        choice match {
          case RewriteSuggestion(_, RewriteResult(next, proof)) =>
            deepen((step, accumulatedProof, thms) :: history, next, proveGen(expr === next, Seq(accumulatedProof, proof)), newThms)
          case Undo => history match {
            case h :: hs => deepen(hs, h._1, h._2, h._3, true)
            case _ =>
              println("Cannot undo: history is empty")
              deepen(history, step, accumulatedProof, thms)
          }
          case Abort => proofAttempts.putFirst(StopProving)
          case Restart => proofAttempts.putFirst(RequestRestart)
          case BFS => ??? //proveBFS(expr, step, thms, ihs, proofAttempts, accumulatedProof, willTerminate)
          case other =>
            println(s"Suggestion $other cannot be used in this context")
            deepen(history, step, accumulatedProof, thms) // try again
        }
      }

      @tailrec
      def proveForever(): Attempt[IPWResult] = {
        proofAttempts.takeFirst() match {
          case ProveConjecture(step, accumulatedProof) =>
            updateStatus(step, Proving)
            prove(step) match {
              case Success(thm) =>
                updateStatus(step, ProofSucceeded)
                proveGen(expr, Seq(accumulatedProof, proveGen(step)))

              case _ =>
                updateStatus(step, ProofFailed)
                proveForever()
            }

          case StopProving => Attempt.fail(s"Could not prove $expr")

          case RequestRestart => Failure(RestartRequestedFailureReason)
        }
      }

      async {
        deepen(Nil, expr, truthGen, thms)
      }

      proveForever()
  }

  private final def handleMetaSuggestions(s: Suggestion): Attempt[IPWResult] = s match {
    case Abort => Attempt.fail("Operation aborted")
    case Restart => Failure(RestartRequestedFailureReason)
    case other => throw new IllegalStateException(s"Suggestion ${other} is illegal in this context")
  }

  private final def IPWproveTopLevel(expr: Expr, thms: Map[String, IPWResult], ihses: Map[String, IPWStructuralInductionHypothesis], guiCtx: GUIContext): Attempt[IPWResult] = expr match {
    case Not(Not(e)) =>
      IPWproveTopLevel(e, thms, ihses, guiCtx)

    case And(exprs) => onGUITab(guiCtx) {
      case (_, tab, _) =>
        andIGen(exprs.zipWithIndex map { case (e, i) => IPWproveTopLevel(e, thms, ihses, NewTab(s"${tab.title}[$i]", tab.window)).get })
    }

    case Forall(v :: vals, body) => onGUITab(guiCtx) {
      case proofCtx @ (suggestingEnd, tab, _) =>
        val suggs = analyseForall(v, body)
        suggestingEnd.write((expr, suggs, thms, false))

        suggestingEnd.read match {
          case FixVariable =>
            forallIGen(v)(_ => IPWproveTopLevel(if (vals.isEmpty) body else Forall(vals, body), thms, ihses, Following(proofCtx)))

          case StructuralInduction =>
            structuralInductionGen(v, forallToPredicate(expr, v.tpe), "ihs") {
              case (tihs, goal) =>
                IPWproveTopLevel(goal, thms, ihses + ("test" -> tihs), NewTab(s"${tab.title} case '${tihs.constr.name}'", tab.window))
            }

          case other => handleMetaSuggestions(other)
        }
    }

    case Implies(hyp, body) => onGUITab(guiCtx) {
      case proofCtx @ (suggestingEnd, tab, _) =>
        suggestingEnd.write((expr, Seq((s"Assume '${prettyPrint(hyp, PrinterOptions())}'", AssumeHypothesis)), thms, false))

        suggestingEnd.read match {
          case AssumeHypothesis =>
            def namePremise(e: Expr): String = suggestingEnd.name(promptTheoremName(e, "assumption"))

            hyp match {
              case And(exprs) if suggestingEnd.split(promptTheoremSplit(exprs)) => implIGen("prem", hyp) { (_, p) =>
                andEGen(p, exprs map namePremise)(ps => IPWproveTopLevel(body, thms ++ ps, ihses, Following(proofCtx)))
              }
              case _ =>
                implIGen(namePremise(hyp), hyp)((name, p) => IPWproveTopLevel(body, thms + (name -> p), ihses, Following(proofCtx)))
            }

          case other => handleMetaSuggestions(other)
        }
    }

    case _ => IPWproveInner(expr, thms, ihses, guiCtx)
  }

  protected final def isRestartRequest(reason: FailureReason): Boolean = reason match {
    case r if r == RestartRequestedFailureReason => true
    case other => other.underlying exists isRestartRequest
  }

  def IPWprove(expr: Expr, source: String, thms: Map[String, IPWResult] = Map.empty,
    ihses: Map[String, IPWStructuralInductionHypothesis] = Map.empty, title: String = "Proof"): Attempt[IPWResult] = {
    val doc = readProofDocument(source, expr)
    val guiCtx = NewWindow(title, doc)

    analysisTimer = 0
    try {
      IPWproveTopLevel(expr, thms, ihses, guiCtx).get
    } catch {
      case ex: AttemptException if isRestartRequest(ex.reason) =>
        doc.clear()
        IPWprove(expr, source, thms, ihses, title)

      case ex: AttemptException => Failure(ex.reason)
    } finally {
      println(analysisTimer + " ns")
      
    }
  }
}