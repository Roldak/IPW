package ipw.utils

import scala.collection.mutable.ListBuffer

import inox._
import inox.trees._
import inox.trees.dsl._

trait TreeCollector[T] extends TreeTraverser {
  private var result: ListBuffer[T] = _
  
  def collect(e: Expr): Seq[T]
  
  def apply(e: Expr) = {
    result = new ListBuffer[T]
    traverse(e)
    result
  }
  
  override def traverse(e: Expr): Unit = {
    result ++= collect(e)
    super.traverse(e)
  }
}