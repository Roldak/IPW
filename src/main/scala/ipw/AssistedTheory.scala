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
import java.util.concurrent.BlockingDeque
import java.util.concurrent.LinkedBlockingDeque
import scala.concurrent.Promise
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.collection.mutable.{ Queue => MutableQueue }
import scala.collection.mutable.{ Set => MutableSet }
import ipw.io.IWFileInterface

trait AssistedTheory
    extends Theory
    with Analysers
    with PathTreeOps
    with Suggestions
    with AssistantWindow
    with IOs { self: AssistedTheory with IWFileInterface =>

  protected[ipw]type ProofState = (Expr, Seq[NamedSuggestion], Map[String, Theorem], Boolean)
  protected[ipw]type UpdateStep = Suggestion
  protected[ipw]type ChoosingEnd = SynchronizedChannel.End[ProofState, UpdateStep]
  protected[ipw]type SuggestingEnd = SynchronizedChannel.End[UpdateStep, ProofState]
  protected[ipw]type StatusCallback = (Expr, Status) => Unit
  private type ProofContext = (ProofCase, WindowTab)

  protected[ipw] sealed abstract class Status(val stage: Int, val message: String)
  protected[ipw] case object InQueue extends Status(0, "In queue")
  protected[ipw] case object Proving extends Status(1, "Trying to conclude...")
  protected[ipw] case object ProofFailed extends Status(2, "Could not conclude.")
  protected[ipw] case object ProofSucceeded extends Status(3, "Success!")

  private sealed abstract class SolveRequest
  private case class ProveConjecture(conjecture: Expr, using: Theorem) extends SolveRequest
  private case object StopProving extends SolveRequest
  private case object RequestRestart extends SolveRequest

  sealed abstract class GUIContext
  case class NewWindow(tabTitle: String, proofDoc: ProofDocument) extends GUIContext
  private case class NewTab(title: String, win: Window) extends GUIContext
  private case class Following(ctx: ProofContext) extends GUIContext

  private val UndoSuggestion = ("Undo", Undo)
  private val bfsSuggestion = ("Breadth-first Search", BFS)

  private val RestartRequestedFailureReason = Aborted("RestartRequested")

  private final def onGUITab(ctx: GUIContext)(f: ProofContext => Attempt[Theorem]): Attempt[Theorem] = ctx match {
    case NewWindow(tabTitle, doc) =>
      val willTerminate = Promise[Unit] // them lies tho
      val res = onGUITab(NewTab(tabTitle, Await.result(openAssistantWindow(willTerminate.future, doc), Duration.Inf)))(f)
      willTerminate.success(())
      doc.save()
      res

    case NewTab(title, window) =>
      val (choosingEnd, suggestingEnd) = SynchronizedChannel[ProofState, UpdateStep]()
      val tab = window.openNewTab(title, choosingEnd)
      val proofCase = window.proofDocument.getCase(title, suggestingEnd, () => window.show)
      f(proofCase, Await.result(tab, Duration.Inf)) match {
        case attempt @ Success(_) =>
          proofCase.setComplete
          attempt
        case other => other
      }

    case Following(ctx) => f(ctx)
  }

  private final def bfs(from: Expr, thms: Map[String, Theorem], ihs: Seq[StructuralInductionHypotheses], prover: BlockingDeque[SolveRequest], acc: Theorem): Unit = {
    type Element = (Expr, Map[String, Theorem], Suggestion, Theorem)

    @tailrec
    def waitForProver(n: Int = -1): Boolean = if (prover.size() == n) {
      true
    } else if (prover.size() > 1000) {
      val size = prover.size()
      Thread.sleep(1000)
      println(s"Waiting for prover... (${size} left to prove)")
      waitForProver(size)
    } else false

    val queue = MutableQueue[Element]()
    val seen = MutableSet[Expr]()
    val (suggestions, newThms) = analyse(from, thms, ihs)

    suggestions foreach (s => queue.enqueue((from, newThms, s._2, acc)))

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
          
          if (!waitForProver()) {
            suggestions foreach (s => queue.enqueue((next, newThms, s._2, newAcc)))
            process(count + 1, alreadySeen)
          }

        case _ => process(count + 1, alreadySeen + 1)
      }
    }

    process(0, 0)
  }

  private final def IPWproveInner(expr: Expr, thms: Map[String, Theorem], ihs: Seq[StructuralInductionHypotheses], guiCtx: GUIContext): Attempt[Theorem] = onGUITab(guiCtx) {
    case (suggestingEnd, tab) =>

      val proofAttempts = new LinkedBlockingDeque[SolveRequest]

      def updateStatus(e: Expr, status: Status): Unit = {
        tab.statusCallback(e, status)
      }

      @tailrec
      def deepen(history: List[(Expr, Theorem, Map[String, Theorem])], step: Expr, accumulatedProof: Theorem, thms: Map[String, Theorem], undo: Boolean = false): Unit = {
        proofAttempts.putFirst(ProveConjecture(step, accumulatedProof))
        updateStatus(step, InQueue)

        val (suggestions, newThms) = analyse(step, thms, ihs)
        val extraSuggestions = (if (!history.isEmpty) Seq(UndoSuggestion) else Nil) :+ bfsSuggestion

        suggestingEnd.write((step, suggestions ++ extraSuggestions, newThms, undo))

        val choice = suggestingEnd.read

        choice match {
          case RewriteSuggestion(_, RewriteResult(next, proof)) =>
            deepen((step, accumulatedProof, thms) :: history, next, prove(expr === next, accumulatedProof, proof), newThms)
          case Undo => history match {
            case h :: hs => deepen(hs, h._1, h._2, h._3, true)
            case _ =>
              println("Cannot undo: history is empty")
              deepen(history, step, accumulatedProof, thms)
          }
          case Abort   => proofAttempts.putFirst(StopProving)
          case Restart => proofAttempts.putFirst(RequestRestart)
          case BFS     => bfs(step, thms, ihs, proofAttempts, accumulatedProof)
          case other =>
            println(s"Suggestion $other cannot be used in this context")
            deepen(history, step, accumulatedProof, thms) // try again
        }
      }

      @tailrec
      def proveForever(): Attempt[Theorem] = {
        proofAttempts.takeFirst() match {
          case ProveConjecture(step, accumulatedProof) =>
            updateStatus(step, Proving)
            prove(step) match {
              case Success(thm) =>
                updateStatus(step, ProofSucceeded)
                prove(expr, accumulatedProof, thm)

              case _ =>
                updateStatus(step, ProofFailed)
                proveForever()
            }

          case StopProving    => Attempt.fail(s"Could not prove $expr")

          case RequestRestart => Failure(RestartRequestedFailureReason)
        }
      }

      async {
        deepen(Nil, expr, truth, thms)
      }

      proveForever()
  }

  private final def handleMetaSuggestions(s: Suggestion): Attempt[Theorem] = s match {
    case Abort   => Attempt.fail("Operation aborted")
    case Restart => Failure(RestartRequestedFailureReason)
    case other   => throw new IllegalStateException(s"Suggestion ${other} is illegal in this context")
  }

  private final def IPWproveTopLevel(expr: Expr, thms: Map[String, Theorem], ihs: Seq[StructuralInductionHypotheses], guiCtx: GUIContext): Attempt[Theorem] = expr match {
    case Not(Not(e)) =>
      IPWproveTopLevel(e, thms, ihs, guiCtx)

    case And(exprs) => onGUITab(guiCtx) {
      case (_, tab) =>
        andI(exprs.zipWithIndex map { case (e, i) => IPWproveTopLevel(e, thms, ihs, NewTab(s"${tab.title}[$i]", tab.window)).get })
    }

    case Forall(v :: vals, body) => onGUITab(guiCtx) {
      case proofCtx @ (suggestingEnd, tab) =>
        val suggs = analyseForall(v, body)
        suggestingEnd.write((expr, suggs, thms, false))

        suggestingEnd.read match {
          case FixVariable =>
            forallI(v)(_ => IPWproveTopLevel(if (vals.isEmpty) body else Forall(vals, body), thms, ihs, Following(proofCtx)))

          case StructuralInduction =>
            structuralInduction(expr, v) {
              case (tihs, goal) =>
                val Some((caseId, _)) = C.unapplySeq(tihs.expression)
                IPWproveTopLevel(goal.expression, thms, ihs :+ tihs, NewTab(s"${tab.title} case '${caseId}'", tab.window))
            }

          case other => handleMetaSuggestions(other)
        }
    }

    case Implies(hyp, body) => onGUITab(guiCtx) {
      case proofCtx @ (suggestingEnd, tab) =>
        suggestingEnd.write((expr, Seq((s"Assume '${prettyPrint(hyp, PrinterOptions())}'", AssumeHypothesis)), thms, false))

        suggestingEnd.read match {
          case AssumeHypothesis =>
            implI(hyp) { assumption =>
              val hyps = assumption.expression match {
                case And(exprs) if suggestingEnd.split(promptTheoremSplit(exprs)) => andE(assumption).get
                case _ => Seq(assumption)
              }
              val newThms = hyps map (h => (suggestingEnd.name(promptTheoremName(h.expression, "assumption")), h))
              IPWproveTopLevel(body, thms ++ newThms, ihs, Following(proofCtx))
            }

          case other => handleMetaSuggestions(other)
        }
    }

    case _ => IPWproveInner(expr, thms, ihs, guiCtx)
  }

  protected final def isRestartRequest(reason: FailureReason): Boolean = reason match {
    case r if r == RestartRequestedFailureReason => true
    case other                                   => other.underlying exists isRestartRequest
  }

  def IPWprove(expr: Expr, source: String, thms: Map[String, Theorem] = Map.empty,
               ihs: Seq[StructuralInductionHypotheses] = Nil, title: String = "Proof"): Attempt[Theorem] = {
    val doc = readProofDocument(source, expr)
    val guiCtx = NewWindow(title, doc)

    analysisTimer = 0
    try {
      IPWproveTopLevel(expr, thms, ihs, guiCtx).get
    } catch {
      case ex: AttemptException if isRestartRequest(ex.reason) =>
        doc.clear()
        IPWprove(expr, source, thms, ihs, title)

      case ex: AttemptException => Failure(ex.reason)
    } finally {
      println(analysisTimer + " ns")
    }
  }
}