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
  
  object ExprTransformingSuggestion {
    def unapply(s: Suggestion): Option[Expr] = s match {
      case ExpandInvocation(inv) => Some(inv)
      case ApplyTheorem(_, _, subj, _) => Some(subj)
      case _ => None
    }
  }
  
  object PreviewableSuggestion {
    def unapply(s: Suggestion): Option[Expr] = s match {
      case ApplyTheorem(_, _, _, res) => Some(res)
      case _ => None
    }
  }
  
  case object Abort extends Suggestion("Abort proof") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = throw new IllegalStateException("Should not even try to call this")
  }

  case object Pass extends Suggestion("Do nothing") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = Success((e, truth))
  }
  
  case class FixVariable(v: ValDef) extends Suggestion(s"Fix variable ${v.id}") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = throw new IllegalStateException("Should not even try to call this")
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
  
  case class ApplyTheorem(val name: String, val thm: Theorem, val subject: Expr, val res: Expr) extends Suggestion(s"Apply theorem $name") {
    override def apply(e: Expr): Attempt[(Expr, Theorem)] = {
      Success((res, thm))
    }
  }
}