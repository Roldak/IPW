package ipw.core

import inox.trees._
import welder._
import ipw.utils.FunctionEvaluator
import ipw.AssistedTheory

trait Suggestions { theory: AssistedTheory =>
  sealed abstract class Suggestion(val descr: String) {
    def apply(e: Expr): Attempt[(Expr, Theorem)]
  }

  case object Pass extends Suggestion("Do nothing") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = Success((e, truth))
  }

  case class ExpandInvocation(val inv: FunctionInvocation) extends Suggestion(s"Expand invocation of ${inv.id}") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = {
      val evaluator = FunctionEvaluator.default(program)
      println("MY EVAL: " + evaluator.eval(e))
      evaluated(e) flatMap { thm =>
        thm.expression match {
          case Equals(unev, ev) => (ev, thm)
        }
      }
    }
  }
}