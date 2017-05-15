package ipw.core

import inox._
import inox.trees._
import inox.evaluators.EvaluationResults._

import welder._

import ipw.eval.PartialEvaluator
import ipw.AssistedTheory

trait Suggestions { theory: AssistedTheory =>
  import trees._
  
  protected[ipw] sealed abstract class Suggestion
  protected[ipw] case class RewriteSuggestion(subject: Expr, result: Expr, proof: Theorem) extends Suggestion
  protected[ipw] case object FixVariable extends Suggestion
  protected[ipw] case object StructuralInduction extends Suggestion
  protected[ipw] case object AssumeHypothesis extends Suggestion
  protected[ipw] case object Abort extends Suggestion
  
  protected[ipw] type NamedSuggestion = (String, Suggestion)
}