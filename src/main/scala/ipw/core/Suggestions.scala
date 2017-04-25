package ipw.core

import inox.trees._
import welder._
import inox.evaluators.RecursiveEvaluator
import ipw.Assistant

trait Suggestions { assistant: Assistant =>
  
  import assistant.theory._

  sealed abstract class Suggestion(val descr: String) {
    def apply(e: Expr): Attempt[(Expr, Theorem)]
  }

  case object Pass extends Suggestion("Do nothing") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = Success((e, truth))
  }

  case class ExpandInvocation(val inv: FunctionInvocation) extends Suggestion(s"Expand invocation of ${inv.id}") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = {
      evaluated(e) flatMap { thm =>
        thm.expression match {
          case Equals(unev, ev) => (ev, thm)
        }
      }
    }
  }
}