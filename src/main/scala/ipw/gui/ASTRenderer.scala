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
  def OpeningSquareBracket = Code.Operator("[")
  def ClosingSquareBracket = Code.Operator("]")
  def OpeningBrace = Code.Operator("{")
  def ClosingBrace = Code.Operator("}")
  def CommaSpace = Code.Operator(", ")
  def Dot = Code.Operator(".")
  
  lazy val ConsolasFont = Font.font("consolas", 13)
  lazy val ConsolasBoldFont = Font.font("consolas", FontWeight.Bold, 13)
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
  def Identifier(text: String) = Raw(text) withColor rgb(94, 94, 255)
  def Type(text: String) = Raw(text) withColor Black
  def ADTType(text: String) = Raw(text) withColor rgb(210, 87, 0) withFont Consts.ConsolasBoldFont
  def Keyword(text: String) = Raw(text) withColor rgb(193, 58, 85) withFont Consts.ConsolasBoldFont
  def Space = Raw(" ")
  def LineBreak = Raw("\n")
  def Indent(n: Int) = Raw("  " * n)
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
  
  protected case class FlowContext(indent: Int) {
    def indented = FlowContext(indent + 1)
  }
  
  protected def buildFlow(e: Expr)(implicit ctx: FlowContext): Seq[Text] = {
    e match {
      case FractionLiteral(a, b) => Seq(Code.Literal(a.toString), Code.Operator("/"), Code.Literal(b.toString))
      
      case x: Literal[AnyRef] => Seq(Code.Literal(x.value.toString))
      
      case BinaryOperator(a, b, op) => buildFlow(a) ++ Seq(Code.Operator(op)) ++ buildFlow(b)
      
      case Variable(v, _, _) => Seq(Code.Identifier(v.toString))
      
      case FunctionInvocation(f, tps, args) => 
        val btps = tps map (tp => Code.Type(prettyPrint(tp, PrinterOptions())))
        val bargs = args map buildFlow
        (Seq(Code.Identifier(f.toString), OpeningSquareBracket) ++
          (if (tps.isEmpty) Seq() else btps.init.flatMap(Seq(_, CommaSpace)) :+ btps.last) :+
          ClosingSquareBracket :+ OpeningBracket) ++
          (if (bargs.isEmpty) Seq() else bargs.init.flatMap(_ :+ CommaSpace) ++ bargs.last) :+
          ClosingBracket
      
      case ADT(ADTType(id, tps), args) => 
        val btps = tps map (tp => Code.Type(prettyPrint(tp, PrinterOptions())))
        val bargs = args map buildFlow
        (Seq(Code.ADTType(id.toString), OpeningSquareBracket) ++
          (if (tps.isEmpty) Seq() else btps.init.flatMap(Seq(_, CommaSpace)) :+ btps.last) :+
          ClosingSquareBracket :+ OpeningBracket) ++
          (if (bargs.isEmpty) Seq() else bargs.init.flatMap(_ :+ CommaSpace) ++ bargs.last) :+
          ClosingBracket
        
      case Application(f, args) =>
        val bargs = args map buildFlow
        Seq(Code.Identifier(f.toString), OpeningBracket) ++
          (if (bargs.isEmpty) Seq() else bargs.init.flatMap(_ :+ CommaSpace) ++ bargs.last) :+
          ClosingBracket
          
      case ADTSelector(e, id) =>
        buildFlow(e) ++ Seq(Dot, Code.Identifier(id.toString))
        
      case IsInstanceOf(e, tp) =>
        Seq(OpeningBracket) ++ buildFlow(e) ++ Seq(Code.Keyword(" is "), Code.Type(prettyPrint(tp, PrinterOptions())), ClosingBracket)
        
      case AsInstanceOf(e, tp) =>
        Seq(OpeningBracket) ++ buildFlow(e) ++ Seq(Code.Keyword(" as "), Code.Type(prettyPrint(tp, PrinterOptions())), ClosingBracket)
        
      case IfExpr(cond, then, elze) =>
        Seq(Code.Keyword("if "), OpeningBracket) ++ buildFlow(cond) ++ Seq(ClosingBracket, Code.Space, OpeningBrace, Code.LineBreak,
            Code.Indent(ctx.indent + 1)) ++ buildFlow(then)(ctx indented) ++ Seq(Code.LineBreak,
            Code.Indent(ctx.indent), ClosingBrace, Code.Keyword(" else "), OpeningBrace, Code.LineBreak,
            Code.Indent(ctx.indent + 1)) ++ buildFlow(elze)(ctx indented) ++ Seq(Code.LineBreak,
            Code.Indent(ctx.indent), ClosingBrace)
          
      case other =>
        val Operator(exprs, _) = e
        val subexprs = exprs map buildFlow
        Seq(Code.TreeName(other.getClass.getSimpleName), OpeningBracket) ++ 
          (if (subexprs.isEmpty) Seq() else subexprs.init.flatMap(_ :+ CommaSpace) ++ subexprs.last) :+ 
          ClosingBracket
    }
  }

  class ASTRenderer(expr: Expr) extends TextFlow {
    children = buildFlow(expr)(FlowContext(0))
  }
}