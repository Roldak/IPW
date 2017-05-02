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
import java.util.concurrent.LinkedBlockingDeque
import scala.concurrent.Promise
import scala.concurrent.ExecutionContext.Implicits.global

trait AssistedTheory
    extends Theory
    with Analysers
    with PathTreeOps
    with Suggestions
    with AssistantWindow { self =>

  protected[ipw] type ProofState = (Expr, Seq[Suggestion], Map[String, Theorem])
  protected[ipw] type UpdateStep = Suggestion
  protected[ipw] type ChoosingEnd = SynchronizedChannel.End[ProofState, UpdateStep]
  protected[ipw] type SuggestingEnd = SynchronizedChannel.End[UpdateStep, ProofState]
  protected[ipw] type StatusCallback = (Expr, Status) => Unit

  protected[ipw] sealed abstract class Status(val stage: Int, val message: String)
  protected[ipw] case object InQueue extends Status(0, "In queue")
  protected[ipw] case object Proving extends Status(1, "Trying to conclude...")
  protected[ipw] case object ProofFailed extends Status(2, "Could not conclude.")
  protected[ipw] case object ProofSucceeded extends Status(3, "Success!")

  def IPWprove(expr: Equals, source: JFile, thms: Map[String, Theorem], ihs: Option[StructuralInductionHypotheses] = None): Attempt[Theorem] = {
    val Equals(lhs, rhs) = expr
    val (choosingEnd, suggestingEnd) = SynchronizedChannel[ProofState, UpdateStep]()
    val willTerminate = Promise[Unit] // them lies tho
    val proofAttempts = new LinkedBlockingDeque[Option[(Expr, Theorem)]]

    val statusCallback = openAssistantWindow(choosingEnd, rhs, willTerminate.future)

    def updateStatus(e: Expr, status: Status): Unit = {
      statusCallback.foreach { _(e, status) }
    }

    @tailrec
    def deepen(step: Expr, accumulatedProof: Theorem, thms: Map[String, Theorem]): Unit = {
      proofAttempts.putFirst(Some((step, accumulatedProof)))
      updateStatus(step, InQueue)

      val (suggestions, newThms) = analyse(step, thms, ihs)

      suggestingEnd.write((step, suggestions, newThms))

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

    val res = proveForever()
    willTerminate.success(())
    res
  }
}