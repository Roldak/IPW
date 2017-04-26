package ipw.core

import inox._
import inox.trees._
import inox.evaluators.EvaluationResults._

import welder._

import ipw.eval.PartialEvaluator
import ipw.eval.optInvokeFirst
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
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = {
      val evaluator = PartialEvaluator(program, Options(Seq(optInvokeFirst(true))))
      evaluator.eval(e) match {
        case Successful(ev) => Success((ev, prove(Equals(e, ev))))
        case RuntimeError(msg) => Failure(Aborted("RuntimeError: " + msg))
        case EvaluatorError(msg) => Failure(Unspecified("EvalError: " + msg))
      }
    }
  }
}