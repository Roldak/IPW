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

trait AssistedTheory
    extends Theory
    with Analysers
    with PathTreeOps
    with Suggestions
    with AssistantWindow { self =>

  protected type ProofState = (Expr, Seq[Suggestion], Map[String, Theorem])
  protected type UpdateStep = Suggestion
  protected type ChoosingEnd = SynchronizedChannel.End[ProofState, UpdateStep]
  protected type SuggestingEnd = SynchronizedChannel.End[UpdateStep, ProofState]

  def IPWprove(expr: Equals, source: JFile, thms: Map[String, Theorem], ihs: Option[StructuralInductionHypotheses] = None): Attempt[Theorem] = {
    val Equals(lhs, rhs) = expr
    val (choosingEnd, suggestingEnd) = SynchronizedChannel[ProofState, UpdateStep]()
    val willTerminate = Promise[Unit] // them lies tho

    openAssistantWindow(choosingEnd, rhs, willTerminate.future)

    val proofAttempts = new LinkedBlockingDeque[Option[(Expr, Theorem)]]

    @tailrec
    def deepen(step: Expr, accumulatedProof: Theorem, thms: Map[String, Theorem]): Unit = {
      proofAttempts.putFirst(Some((step, accumulatedProof)))

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
        case Some((expr, accumulatedProof)) => prove(expr === rhs) match {
          case Success(thm) => prove(lhs === rhs, accumulatedProof, thm)
          case _            => proveForever()
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