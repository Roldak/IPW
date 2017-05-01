package ipw

import java.io.{ File => JFile }

import scala.annotation.tailrec

import inox._
import inox.trees._
import inox.trees.dsl._

import welder._

import ipw.gui.AssistantWindow
import ipw.core._
import ipw.io.SynchronizedChannel

trait AssistedTheory 
  extends Theory
    with Analysers
    with PathTreeOps
    with Suggestions
    with AssistantWindow { self =>

  type ProofState = (Expr, Seq[Suggestion], Map[String, Theorem])
  type UpdateStep = Suggestion
  type ChoosingEnd = SynchronizedChannel.End[ProofState, UpdateStep]
  type SuggestingEnd = SynchronizedChannel.End[UpdateStep, ProofState]

  def IPWprove(expr: Equals, source: JFile, thms: Map[String, Theorem], ihs: Option[StructuralInductionHypotheses] = None): Attempt[Theorem] = {
    val Equals(lhs, rhs) = expr
    val (choosingEnd, suggestingEnd) = SynchronizedChannel[ProofState, UpdateStep]()
    
    openAssistantWindow(choosingEnd)

    @tailrec
    def deepen(step: Expr, rhs: Expr, accumulatedProof: Theorem, thms: Map[String, Theorem]): Attempt[Theorem] = {      
      prove(step === rhs) match {
        case thm @ Success(_) => prove(lhs === rhs, accumulatedProof, thm)
        case _ =>
          val (suggestions, newThms) = analyse(step, thms, ihs)
          
          suggestingEnd.write((step, suggestions, newThms))

          val choice = suggestingEnd.read

          choice(step) match {
            case Success((next, stepProof)) => 
              deepen(next, rhs, prove(lhs === next, accumulatedProof, stepProof), newThms)
              
            case Failure(reason) =>
              println("Error while applying suggestion: " + reason)
              deepen(step, rhs, accumulatedProof, thms) // try again
          }
      }
    }

    deepen(lhs, rhs, truth, thms)
  }
}