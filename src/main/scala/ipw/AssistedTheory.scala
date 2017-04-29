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
    with Suggestions
    with AssistantWindow { self =>

  type ChoosingEnd = SynchronizedChannel.End[(Seq[Suggestion], Expr), Suggestion]
  type SuggestingEnd = SynchronizedChannel.End[Suggestion, (Seq[Suggestion], Expr)]

  def IPWprove(expr: Equals, source: JFile, thms: Map[String, Theorem], ihs: Option[StructuralInductionHypotheses]): Attempt[Theorem] = {
    val Equals(lhs, rhs) = expr
    val (choosingEnd, suggestingEnd) = SynchronizedChannel[(Seq[Suggestion], Expr), Suggestion]()
    
    openAssistantWindow(choosingEnd, thms)

    @tailrec
    def deepen(step: Expr, rhs: Expr, accumulatedProof: Theorem): Attempt[Theorem] = {      
      prove(step === rhs) match {
        case thm @ Success(_) => prove(lhs === rhs, accumulatedProof, thm)
        case _ =>
          val suggestions = analyse(step, thms, ihs)
          
          suggestingEnd.write((suggestions, step))

          val choice = suggestingEnd.read

          choice(step) match {
            case Success((next, stepProof)) => 
              deepen(next, rhs, prove(lhs === next, accumulatedProof, stepProof))
              
            case Failure(reason) =>
              println("Error while applying suggestion: " + reason)
              deepen(step, rhs, accumulatedProof) // try again
          }
      }
    }

    deepen(lhs, rhs, truth)
  }
}