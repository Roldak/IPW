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
import java.util.concurrent.BlockingDeque
import java.util.concurrent.LinkedBlockingDeque
import scala.concurrent.Promise
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import ipw.io.IWFileInterface

trait AssistedTheory
    extends Theory
    with Analysers
    with PathTreeOps
    with Suggestions
    with AssistantWindow { self: AssistedTheory with IWFileInterface =>

  protected[ipw] type ProofState = (Expr, Seq[NamedSuggestion], Map[String, Theorem], Boolean)
  protected[ipw] type UpdateStep = Suggestion
  protected[ipw] type ChoosingEnd = SynchronizedChannel.End[ProofState, UpdateStep]
  protected[ipw] type SuggestingEnd = SynchronizedChannel.End[UpdateStep, ProofState]
  protected[ipw] type StatusCallback = (Expr, Status) => Unit
  private type ProofContext = (SuggestingEnd, WindowTab)

  protected[ipw] sealed abstract class Status(val stage: Int, val message: String)
  protected[ipw] case object InQueue extends Status(0, "In queue")
  protected[ipw] case object Proving extends Status(1, "Trying to conclude...")
  protected[ipw] case object ProofFailed extends Status(2, "Could not conclude.")
  protected[ipw] case object ProofSucceeded extends Status(3, "Success!")

  sealed abstract class GUIContext
  case class NewWindow(tabTitle: String) extends GUIContext
  private case class NewTab(title: String, win: Window) extends GUIContext
  private case class Following(ctx: ProofContext) extends GUIContext

  private val UndoSuggestion = ("Undo", Undo)

  private def onGUITab[T](ctx: GUIContext)(f: ProofContext => T): T = ctx match {
    case NewWindow(tabTitle) =>
      val willTerminate = Promise[Unit] // them lies tho
      val res = onGUITab(NewTab(tabTitle, Await.result(openAssistantWindow(willTerminate.future), Duration.Inf)))(f)
      willTerminate.success(())
      res

    case NewTab(title, window) =>
      val (choosingEnd, suggestingEnd) = SynchronizedChannel[ProofState, UpdateStep]()
      val tab = window.openNewTab(title, choosingEnd)
      window.show
      f(suggestingEnd, Await.result(tab, Duration.Inf))

    case Following(ctx) => f(ctx)
  }

  private def IPWproveInner(expr: Expr, source: String, thms: Map[String, Theorem],
                            ihs: Seq[StructuralInductionHypotheses] = Nil, guiCtx: GUIContext = NewWindow("Proof")): Attempt[Theorem] = onGUITab(guiCtx) {
    case (suggestingEnd, tab) =>

      val proofAttempts = new LinkedBlockingDeque[Option[(Expr, Theorem)]]

      def updateStatus(e: Expr, status: Status): Unit = {
        tab.statusCallback(e, status)
      }

      @tailrec
      def deepen(history: List[(Expr, Theorem, Map[String, Theorem])], step: Expr, accumulatedProof: Theorem, thms: Map[String, Theorem], undo: Boolean = false): Unit = {
        proofAttempts.putFirst(Some((step, accumulatedProof)))
        updateStatus(step, InQueue)

        val (suggestions, newThms) = analyse(step, thms, ihs)
        val extraSuggestions = if (!history.isEmpty) Seq(UndoSuggestion) else Nil

        suggestingEnd.write((step, suggestions ++ extraSuggestions, newThms, undo))

        val choice = suggestingEnd.read
        
        writeIWFDocument(source, (expr, thms.values.toSeq), List(choice))

        choice match {
          case RewriteSuggestion(_, RewriteResult(next, proof)) =>
            deepen((step, accumulatedProof, thms) :: history, next, prove(expr === next, accumulatedProof, proof), newThms)
          case Undo => history match {
            case h :: hs => deepen(hs, h._1, h._2, h._3, true)
            case _ =>
              println("Cannot undo: history is empty")
              deepen(history, step, accumulatedProof, thms)
          }
          case Abort =>
          case other =>
            println(s"Suggestion $other cannot be used in this context")
            deepen(history, step, accumulatedProof, thms) // try again
        }
      }

      @tailrec
      def proveForever(): Attempt[Theorem] = {
        proofAttempts.takeFirst() match {
          case Some((step, accumulatedProof)) =>
            updateStatus(step, Proving)
            prove(step) match {
              case Success(thm) =>
                updateStatus(step, ProofSucceeded)
                prove(expr, accumulatedProof, thm)

              case _ =>
                updateStatus(step, ProofFailed)
                proveForever()
            }

          case _ => Attempt.fail(s"Could not prove $expr")
        }
      }

      async {
        deepen(Nil, expr, truth, thms)
        proofAttempts.addFirst(None) // abort :'(
      }

      proveForever()
  }

  def IPWprove(expr: Expr, source: String, thms: Map[String, Theorem],
               ihs: Seq[StructuralInductionHypotheses] = Nil, guiCtx: GUIContext = NewWindow("Proof")): Attempt[Theorem] = expr match {
    case Not(Not(e)) =>
      IPWprove(e, source, thms, ihs, guiCtx)

    case And(exprs) => onGUITab(guiCtx) {
      case (_, tab) =>
        andI(exprs.zipWithIndex map { case (e, i) => IPWprove(e, source, thms, ihs, NewTab(s"${tab.title}[$i]", tab.window)).get })
    }

    case Forall(v :: vals, body) => onGUITab(guiCtx) {
      case proofCtx @ (suggestingEnd, tab) =>
        val suggs = analyseForall(v, body)
        suggestingEnd.write((expr, suggs, thms, false))

        suggestingEnd.read match {
          case FixVariable =>
            forallI(v)(_ => IPWprove(if (vals.isEmpty) body else Forall(vals, body), source, thms, ihs, Following(proofCtx)))

          case StructuralInduction =>
            structuralInduction(expr, v) {
              case (tihs, goal) =>
                val Some((caseId, _)) = C.unapplySeq(tihs.expression)
                IPWprove(goal.expression, source, thms, ihs :+ tihs, NewTab(s"${tab.title} case '${caseId}'", tab.window))
            }

          case Abort => Attempt.fail("Operation aborted")

          case other => throw new IllegalStateException(s"Suggestion ${other} is illegal in this context")
        }
    }

    case Implies(hyp, body) => onGUITab(guiCtx) {
      case proofCtx @ (suggestingEnd, tab) =>
        suggestingEnd.write((expr, Seq((s"Assume '${prettyPrint(hyp, PrinterOptions())}'", AssumeHypothesis)), thms, false))

        suggestingEnd.read match {
          case AssumeHypothesis =>
            implI(hyp) { assumption =>
              val hyps = assumption.expression match {
                case And(exprs) if promptTheoremSplit(exprs) => andE(assumption).get
                case _                                       => Seq(assumption)
              }
              val newThms = hyps map (h => (promptTheoremName(h.expression, "assumption"), h))
              IPWprove(body, source, thms ++ newThms, ihs, Following(proofCtx))
            }

          case other => throw new IllegalStateException(s"Suggestion ${other} is illegal in this context")
        }
    }

    case _ =>
      IPWproveInner(expr, source, thms, ihs, guiCtx)
  }
}