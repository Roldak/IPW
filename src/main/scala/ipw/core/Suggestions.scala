package ipw.core

import inox._
import inox.trees._
import inox.evaluators.EvaluationResults._

import welder._

import ipw.eval.PartialEvaluator
import ipw.AssistedTheory

trait Suggestions { theory: AssistedTheory =>
  import trees._
  
  protected[ipw] class RewriteResult private (computeRes: () => (Expr, Theorem)) {
    private lazy val result = computeRes()
    
    def apply(): (Expr, Theorem) = result
  }
  
  protected[ipw] object RewriteResult {
    def apply(expr: Expr, proof: Theorem) = new RewriteResult(() => (expr, proof))
    def apply(res: () => (Expr, Theorem)) = new RewriteResult(res)
    
    def unapply(res: RewriteResult): Option[(Expr, Theorem)] = Some(res())
  }
  
  protected[ipw] sealed abstract class Suggestion
  protected[ipw] case class RewriteSuggestion(subject: Expr, result: RewriteResult) extends Suggestion
  protected[ipw] case object FixVariable extends Suggestion
  protected[ipw] case object StructuralInduction extends Suggestion
  protected[ipw] case object AssumeHypothesis extends Suggestion
  protected[ipw] case object Abort extends Suggestion
  
  protected[ipw] type NamedSuggestion = (String, Suggestion)
}