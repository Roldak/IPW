package ipw.gui

import scalafx.scene.text._
import scalafx.scene.paint.Color._
import ipw.AssistedTheory
import inox._
import inox.trees._
import inox.trees.dsl._
import scalafx.scene.paint.Color


protected[gui] object Consts {
  def OpeningBracket = Code.Operator("(")
  def ClosingBracket = Code.Operator(")")
  def CommaSpace = Code.Operator(", ")
  
  lazy val ConsolasFont = Font.font("consolas", 13)
}

protected[gui] object Code {
  private implicit class TextOps(x: Text) {
    def withFont(f: Font) = {
      x.font = f
      x
    }
    def withColor(c: Color) = {
      x.fill = c
      x
    }
  }
  
  private def Raw(text: String) = new Text(text) withFont Consts.ConsolasFont
  
  def Operator(text: String) = Raw(text) withColor Black
  def TreeName(text: String) = Raw(text) withColor rgb(181, 58, 103)
  def Literal(text: String) = Raw(text) withColor rgb(226, 160, 255)
}
protected[gui] class Keyword

trait Rendering { theory: AssistedTheory =>  
  import Consts._
  
  protected object BinaryOperator {
    def unapply(e: Expr): Option[(Expr, Expr, String)] = e match {
      case Equals(a, b) => Some((a, b, "=="))
      case _ => None
    }
  }
  
  protected def buildFlow(e: Expr): Seq[Text] = {
    e match {
      case FractionLiteral(a, b) => Seq(Code.Literal(a.toString), Code.Operator("/"), Code.Literal(b.toString))
      case x: Literal[AnyRef] => Seq(Code.Literal(x.value.toString))
      case BinaryOperator(a, b, op) => buildFlow(a) ++ Seq(Code.Operator(op)) ++ buildFlow(b)
      case other =>
        val Operator(exprs, _) = e
        val subexprs = exprs map buildFlow
        Seq(Code.TreeName(other.getClass.getSimpleName), OpeningBracket) ++ 
          subexprs.init.map(_ :+ CommaSpace).flatten ++ subexprs.last :+ 
          ClosingBracket
    }
  }

  class ASTRenderer(expr: Expr) extends TextFlow {
    children = Code.Operator(prettyPrint(expr, PrinterOptions())) //buildFlow(expr)
  }
}