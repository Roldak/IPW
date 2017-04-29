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
import scalafx.scene.Node

protected[gui] object Consts {
  def OpeningBracket = Code.Operator("(")
  def ClosingBracket = Code.Operator(")")
  def OpeningSquareBracket = Code.Operator("[")
  def ClosingSquareBracket = Code.Operator("]")
  def OpeningBrace = Code.Operator("{")
  def ClosingBrace = Code.Operator("}")
  def CommaSpace = Code.Operator(", ")
  def Dot = Code.Operator(".")
  def Colon = Code.Operator(":")

  lazy val ConsolasFont = Font.font("consolas", 13)
  lazy val ConsolasBoldFont = Font.font("consolas", FontWeight.Bold, 13)
}

protected[gui] object Code {
  class Node(text: String) extends Text(text) { self =>
    var expression: Expr = null
    var neighbors: Seq[Node] = null
    
    private var finalized = false
    private var resetState: () => Unit = null

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
    
    def finalize(exp: Expr, neighborz: Seq[Node]) = {
      expression = exp
      neighbors = neighborz
      resetState = new Function0[Unit] {
        val font = self.font.value
        val fill = self.fill.value
        val style = self.style.value
        val underline = self.underline.value

        def apply() = {
          self.font = font
          self.fill = fill
          self.style = style
          self.underline = underline
        }
      }
      finalized = true
    }
    
    def isFinalized = finalized

    onMouseEntered = handle {
      neighbors.foreach { n =>
        n.underline = true
      }
    }
    onMouseExited = handle {
      neighbors.foreach(_.resetState())
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

  protected def nary(exprs: Seq[Seq[Code.Node]], sep: String = ", ", init: String = "", closing: String = ""): Seq[Code.Node] = {
    val initNode = if (init.isEmpty()) Seq() else Seq(Code.Operator(init))
    val exprNodes = if (exprs.isEmpty) Seq() else exprs.init.flatMap(_ :+ Code.Operator(sep)) ++ exprs.last
    val closingNode = if (closing.isEmpty()) Seq() else Seq(Code.Operator(closing))
    initNode ++ exprNodes ++ closingNode
  }
  
  protected def typeNode(tpe: Type): Seq[Code.Node] = Seq(Code.Type(prettyPrint(tpe, PrinterOptions())))
  
  protected def buildFlowImpl(e: Expr)(implicit ctx: FlowContext): Seq[Code.Node] = e match {
    case FractionLiteral(a, b)         => Seq(Code.Literal(a.toString), Code.Operator("/"), Code.Literal(b.toString))

    case x: Literal[AnyRef] @unchecked => Seq(Code.Literal(x.value.toString))

    case BinaryOperator(a, b, op)      => buildFlow(a) ++ Seq(Code.Operator(op)) ++ buildFlow(b)

    case Variable(v, _, _)             => Seq(Code.Identifier(v.toString))

    case FunctionInvocation(f, tps, args) =>
      Seq(Code.Identifier(f.toString)) ++ nary(tps map typeNode, ", ", "[", "]") ++ nary(args map buildFlow, ", ", "(", ")")

    case ADT(ADTType(id, tps), args) =>
      Seq(Code.ADTType(id.toString)) ++ nary(tps map typeNode, ", ", "[", "]") ++ nary(args map buildFlow, ", ", "(", ")")

    case Application(f, args) =>
      Seq(Code.Identifier(f.toString)) ++ nary(args map buildFlow, ", ", "(", ")")

    case ADTSelector(e, id) =>
      buildFlow(e) ++ Seq(Dot, Code.Identifier(id.toString))

    case IsInstanceOf(e, tp) =>
      buildFlow(e) ++ Seq(Dot, Code.Keyword("is"), OpeningSquareBracket) ++ typeNode(tp) :+ ClosingSquareBracket

    case AsInstanceOf(e, tp) =>
      buildFlow(e) ++ Seq(Dot, Code.Keyword("as"), OpeningSquareBracket) ++ typeNode(tp) :+ ClosingSquareBracket

    case IfExpr(cond, then, elze) =>
      Seq(Code.Keyword("if "), OpeningBracket) ++ buildFlow(cond) ++ Seq(ClosingBracket, Code.Space, OpeningBrace, Code.LineBreak,
        Code.Indent(ctx.indent + 1)) ++ buildFlow(then)(ctx indented) ++ Seq(Code.LineBreak,
          Code.Indent(ctx.indent), ClosingBrace, Code.Keyword(" else "), OpeningBrace, Code.LineBreak,
          Code.Indent(ctx.indent + 1)) ++ buildFlow(elze)(ctx indented) ++ Seq(Code.LineBreak,
            Code.Indent(ctx.indent), ClosingBrace)
            
    case Forall(vals, expr) => 
      Seq(Code.Operator("\u2200")) ++ nary(vals.map { v => Seq(Code.Identifier(v.id.toString), Colon) ++ typeNode(v.tpe) }) ++ Seq(Dot) ++ buildFlow(expr)

    case Operator(exprs, _) =>
      Seq(Code.TreeName(e.getClass.getSimpleName)) ++ nary(exprs map buildFlow, ", ", "(", ")")
  }

  protected def buildFlow(e: Expr)(implicit ctx: FlowContext): Seq[Code.Node] = {
    val nodes = buildFlowImpl(e)(ctx withParent e)
    nodes filter { !_.isFinalized } foreach { _.finalize(e, nodes) }
    nodes
  }

  class ASTRenderer(expr: Expr) extends TextFlow {
    children = buildFlow(expr)(FlowContext(0, Nil))
  }
}