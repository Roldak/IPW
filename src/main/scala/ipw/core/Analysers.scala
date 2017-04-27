package ipw.core

import inox._
import inox.trees._
import inox.trees.dsl._
import welder._
import ipw.utils.TreeCollector
import ipw.AssistedTheory

trait Analysers { theory: AssistedTheory =>
  private lazy val analyser = new TreeCollector[Suggestion] {
    override def collect(e: Expr): Seq[Suggestion] = e match {
      case inv: FunctionInvocation => Seq(new ExpandInvocation(inv))
      case _ => Seq()
    }
  }
  
  def analyse(e: Expr) = analyser(e)
}