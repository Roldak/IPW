package ipw

import inox._
import inox.trees._
import inox.trees.dsl._

import java.io.{File => JFile}
import welder._

trait Assistant {
  val theory: Theory
  
  import theory._
  
  def IPWprove(expr: Expr, source: JFile, thms: Map[String, Theorem]): Attempt[Theorem] = {
    prove(expr)
  }
}