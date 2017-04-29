package ipw.core

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._
import welder._
import ipw.AssistedTheory

trait Analysers { theory: AssistedTheory =>
  implicit class StructUtils(hyp: StructuralInductionHypotheses) {
    lazy val variablesSet = hyp.variables.toSet

    private def isInnerOrSelf(inner: Expr): Boolean = inner == hyp.expression || isInner(inner)

    def isInner(inner: Expr): Boolean = inner match {
      case v: Variable           => variablesSet.contains(v)
      case ADTSelector(adt, _)   => isInnerOrSelf(adt)
      case TupleSelect(tuple, _) => isInnerOrSelf(tuple)
      case MapApply(map, _)      => isInnerOrSelf(map)
      case _                     => false
    }
  }
  
  private def collectInvocations(e: Expr): Seq[Suggestion] = functionCallsOf(e).map(new ExpandInvocation(_)).toSeq 

  private def findInductiveHypothesisApplication(e: Expr, ihs: StructuralInductionHypotheses): Seq[Suggestion] = {
    val ihsType = ihs.expression.getType

    val col = collectPreorder[Expr] { e: Expr =>
      if (ihs.isInner(e)) {
        ihs.hypothesis(e) match {
          case Success(hyp) => {
            Seq(e)
          }
          case Failure(_) => Seq()
        }
      } else Seq()
    }(e)
    
    println(col)

    Seq()
  }
  
  private def topLevelForallE(e: Expr): Expr = e

  def analyse(e: Expr, thms: Map[String, Theorem], ihs: Option[StructuralInductionHypotheses]): Seq[Suggestion] =
    collectInvocations(e) ++ ihs.map(findInductiveHypothesisApplication(e, _)).getOrElse(Seq())
}