package ipw.core

import inox._
import inox.trees._
import inox.evaluators.EvaluationResults._

import welder._

import ipw.eval.PartialEvaluator
import ipw.AssistedTheory

protected[ipw] trait Suggestions { theory: AssistedTheory =>
  import trees._
  
  protected[ipw] class RewriteResult private (computeRes: () => (Expr, IPWResult)) {
    private lazy val result = computeRes()
    
    def apply(): (Expr, IPWResult) = result
    
    override def toString(): String = s"RewriteResult(${result._1}, ${result._2})"
  }
  
  protected[ipw] object RewriteResult {
    def apply(expr: Expr, proof: IPWResult) = new RewriteResult(() => (expr, proof))
    def apply(res: () => (Expr, IPWResult)) = new RewriteResult(res)
    
    def unapply(res: RewriteResult): Option[(Expr, IPWResult)] = Some(res())
  }
  
  protected[ipw] sealed abstract class Suggestion
  protected[ipw] case class RewriteSuggestion(subject: Expr, result: RewriteResult) extends Suggestion
  protected[ipw] case object FixVariable extends Suggestion
  protected[ipw] case object StructuralInduction extends Suggestion
  protected[ipw] case object AssumeHypothesis extends Suggestion
  
  protected[ipw] case object Abort extends Suggestion
  protected[ipw] case object Undo extends Suggestion
  protected[ipw] case object Restart extends Suggestion
  protected[ipw] case object BFS extends Suggestion
  
  protected[ipw] type NamedSuggestion = (String, Suggestion)
}