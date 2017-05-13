package ipw

import java.io.{ File => JFile }
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

trait AssistedTheory
    extends Theory
    with Analysers
    with PathTreeOps
    with Suggestions
    with AssistantWindow { self =>

  protected[ipw]type ProofState = (Expr, Expr, Seq[Suggestion], Map[String, Theorem])
  protected[ipw]type UpdateStep = Suggestion
  protected[ipw]type ChoosingEnd = SynchronizedChannel.End[ProofState, UpdateStep]
  protected[ipw]type SuggestingEnd = SynchronizedChannel.End[UpdateStep, ProofState]
  protected[ipw]type StatusCallback = (Expr, Status) => Unit
  private type ProofContext = (SuggestingEnd, Promise[Unit], WindowTab)

  protected[ipw] sealed abstract class Status(val stage: Int, val message: String)
  protected[ipw] case object InQueue extends Status(0, "In queue")
  protected[ipw] case object Proving extends Status(1, "Trying to conclude...")
  protected[ipw] case object ProofFailed extends Status(2, "Could not conclude.")
  protected[ipw] case object ProofSucceeded extends Status(3, "Success!")

  sealed abstract class GUIContext
  case object NewWindow extends GUIContext
  private case class NewTab() extends GUIContext
  private case class Following(ctx: ProofContext) extends GUIContext

  private def onGUITab[T](ctx: GUIContext)(f: ProofContext => T): T = ctx match {
    case NewWindow =>
      val (choosingEnd, suggestingEnd) = SynchronizedChannel[ProofState, UpdateStep]()
      val willTerminate = Promise[Unit] // them lies tho
      val tab = openAssistantWindow(choosingEnd, willTerminate.future)
      val res = f(suggestingEnd, willTerminate, Await.result(tab, Duration.Inf))
      willTerminate.success(())
      res

    case Following(ctx) => f(ctx)
  }

  def IPWproveEq(lhs: Expr, rhs: Expr, source: JFile, thms: Map[String, Theorem],
                 ihs: Seq[StructuralInductionHypotheses] = Nil, guiCtx: GUIContext = NewWindow): Attempt[Theorem] = onGUITab(guiCtx) {
    case (suggestingEnd, willTerminate, tab) =>

      val proofAttempts = new LinkedBlockingDeque[Option[(Expr, Theorem)]]

      def updateStatus(e: Expr, status: Status): Unit = {
        tab.statusCallback(e, status)
      }

      @tailrec
      def deepen(step: Expr, accumulatedProof: Theorem, thms: Map[String, Theorem]): Unit = {
        proofAttempts.putFirst(Some((step, accumulatedProof)))
        updateStatus(step, InQueue)

        val (suggestions, newThms) = analyse(step, thms, ihs)

        suggestingEnd.write((step, rhs, suggestions, newThms))

        val choice = suggestingEnd.read

        if (choice != Abort) {
          choice(step) match {
            case Success((next, stepProof)) =>
              deepen(next, prove(lhs === next, accumulatedProof, stepProof), newThms)

            case Failure(reason) =>
              println("Error while applying suggestion: " + reason)
              deepen(step, accumulatedProof, thms) // try again
          }
        }
      }

      @tailrec
      def proveForever(): Attempt[Theorem] = {
        proofAttempts.takeFirst() match {
          case Some((expr, accumulatedProof)) =>
            updateStatus(expr, Proving)
            prove(expr === rhs) match {
              case Success(thm) =>
                updateStatus(expr, ProofSucceeded)
                prove(lhs === rhs, accumulatedProof, thm)

              case _ =>
                updateStatus(expr, ProofFailed)
                proveForever()
            }

          case _ => Attempt.fail(s"Could not prove $lhs == $rhs")
        }
      }

      async {
        deepen(lhs, truth, thms)
        proofAttempts.addFirst(None) // abort :'(
      }

      proveForever()
  }

  def IPWprove(expr: Expr, source: JFile, thms: Map[String, Theorem],
               ihs: Seq[StructuralInductionHypotheses] = Nil, guiCtx: GUIContext = NewWindow): Attempt[Theorem] = onGUITab(guiCtx) {
    case proofCtx @ (suggestingEnd, willTerminate, tab) => expr match {
      case Equals(lhs, rhs) => IPWproveEq(lhs, rhs, source, thms, ihs, Following(proofCtx))
      case Forall(v :: vals, body) =>
        val structInd = v.tpe match {
          case adt: ADTType => adt.lookupADT match {
            case Some(adtDef) =>
              if (adtDef.definition.isInductive) Seq(StructuralInduction(v))
              else Seq()
            case _ => Seq()
          }
          case _ => Seq()
        }

        val suggs = structInd :+ FixVariable(v)
        suggestingEnd.write((expr, E(42), suggs, thms))

        suggestingEnd.read match {
          case FixVariable(_) =>
            forallI(v)(_ => IPWprove(if (vals.isEmpty) body else Forall(vals, body), source, thms, ihs, Following(proofCtx)))

          case StructuralInduction(_) =>
            structuralInduction(expr, v) {
              case (tihs, goal) => IPWprove(goal.expression, source, thms, ihs :+ tihs, Following(proofCtx))
            }

          case other => throw new IllegalStateException(s"Suggestion ${other} is illegal in this context")
        }
    }

  }
}