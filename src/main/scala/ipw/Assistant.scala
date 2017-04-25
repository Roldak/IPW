package ipw

import scala.annotation.tailrec
import inox._
import inox.trees._
import inox.trees.dsl._
import java.io.{ File => JFile }
import welder._
import ipw.gui.AssistantWindow
import ipw.core._

trait Assistant 
  extends Analysers 
    with Suggestions { self =>
      
  val theory: Theory

  import theory._

  def IPWprove(expr: Equals, source: JFile, thms: Map[String, Theorem]): Attempt[Theorem] = {
    //AssistantWindow.open()
    val Equals(lhs, rhs) = expr

    @tailrec
    def deepen(step: Expr, rhs: Expr, accumulatedProof: Theorem): Attempt[Theorem] = {
      println("CURRENT STEP: " + step)
      
      prove(step === rhs) match {
        case thm @ Success(_) => prove(lhs === rhs, accumulatedProof, thm)
        case _ =>
          // analyse lhs knowing rhs
          val suggestions = analyse(step)
          // wait for user choice

          println("Suggestions: " + suggestions + " : ")

          val choice = if (suggestions.isEmpty) Pass else suggestions.head //chooseAmong(suggestions, source)

          // apply transformation
          choice(step) match {
            case Success((next, stepProof)) => 
              deepen(next, rhs, prove(lhs === next, accumulatedProof, stepProof))
          }
      }
    }

    deepen(lhs, rhs, truth)
    //Failure(Unspecified("not implemented yet"))
  }
}