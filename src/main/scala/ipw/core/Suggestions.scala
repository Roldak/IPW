package ipw.core

import inox._
import inox.trees._
import inox.evaluators.EvaluationResults._

import welder._

import ipw.eval.PartialEvaluator
import ipw.AssistedTheory

trait Suggestions { theory: AssistedTheory =>
  import trees._
  
  sealed abstract class Suggestion(val descr: String) {
    def apply(e: Expr): Attempt[(Expr, Theorem)]
  }

  case object Pass extends Suggestion("Do nothing") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = Success((e, truth))
  }

  case class ExpandInvocation(val inv: FunctionInvocation) extends Suggestion(s"Expand invocation of ${inv.id}") {
    val evaluator = PartialEvaluator.default(program, Some(inv))
    
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = {
      evaluator.eval(e) match {
        case Successful(ev) => Success((ev, prove(Equals(e, ev))))
        case RuntimeError(msg) => Failure(Aborted("RuntimeError: " + msg))
        case EvaluatorError(msg) => Failure(Unspecified("EvalError: " + msg))
      }
    }
  }
  
  case class ApplyTheorem(val name: String, val thm: Theorem, val res: Expr) extends Suggestion(s"Apply theorem $name") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = {
      Success((res, thm))
    }
  }
}