package ipw.gui

import scalafx.Includes._
import scalafx.scene.text._
import scalafx.scene.paint.Color._
import ipw.AssistedTheory
import inox._
import inox.trees._
import inox.trees.dsl._
import scalafx.scene.paint.Color
import scala.language.postfixOps
import javafx.event._
import javafx.scene.input.MouseEvent
import scalafx.beans.property.ObjectProperty

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
  class Node(text: String) extends Text(text) {
    var expression: Expr = null
    
    def withFont(f: Font) = {
      font = f
      this
    }
    def withColor(c: Color) = {
      fill = c
      this
    }
    def withTest(str: String) = {
      onMouseMoved = handle { println(str) }
      this
    }
    onMouseClicked = handle {
      println(expression)
    }
  }

  private def Raw(text: String) = new Node(text) withFont Consts.ConsolasFont

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

trait Rendering { theory: AssistedTheory =>
  import Consts._

  protected object BinaryOperator {
    def unapply(e: Expr): Option[(Expr, Expr, String)] = e match {
      case Equals(a, b) => Some((a, b, "=="))
      case _            => None
    }
  }

  protected case class FlowContext(indent: Int, parents: List[Expr]) {
    def indented = FlowContext(indent + 1, parents)
    def withParent(e: Expr) = FlowContext(indent, e :: parents)
  }

  protected abstract class TextClickEvent extends EventHandler[MouseEvent]

  protected def buildFlowImpl(e: Expr)(implicit ctx: FlowContext): Seq[Code.Node] = e match {
    case FractionLiteral(a, b)         => Seq(Code.Literal(a.toString), Code.Operator("/"), Code.Literal(b.toString))

    case x: Literal[AnyRef] @unchecked => Seq(Code.Literal(x.value.toString))

    case BinaryOperator(a, b, op)      => buildFlow(a) ++ Seq(Code.Operator(op)) ++ buildFlow(b)

    case Variable(v, _, _)             => Seq(Code.Identifier(v.toString))

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
      buildFlow(e) ++ Seq(Dot, Code.Keyword("is"), OpeningSquareBracket, Code.Type(prettyPrint(tp, PrinterOptions())), ClosingSquareBracket)

    case AsInstanceOf(e, tp) =>
      buildFlow(e) ++ Seq(Dot, Code.Keyword("as"), OpeningSquareBracket, Code.Type(prettyPrint(tp, PrinterOptions())), ClosingSquareBracket)

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

  protected def buildFlow(e: Expr)(implicit ctx: FlowContext): Seq[Code.Node] = {
    val nodes = buildFlowImpl(e)(ctx withParent e)
    nodes.foreach { n =>
      println(n.expression)
      if (n.expression == null) {
        n.expression = e
      }
    }
    nodes
  }

  class ASTRenderer(expr: Expr) extends TextFlow {
    children = buildFlow(expr)(FlowContext(0, Nil))
  }
}