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
import scalafx.scene.paint.Paint

trait Rendering { window: AssistantWindow =>

  protected object Consts {
    def OpeningBracket(implicit ctx: FlowContext) = Code.Operator("(")
    def ClosingBracket(implicit ctx: FlowContext) = Code.Operator(")")
    def OpeningSquareBracket(implicit ctx: FlowContext) = Code.Operator("[")
    def ClosingSquareBracket(implicit ctx: FlowContext) = Code.Operator("]")
    def OpeningBrace(implicit ctx: FlowContext) = Code.Operator("{")
    def ClosingBrace(implicit ctx: FlowContext) = Code.Operator("}")
    def CommaSpace(implicit ctx: FlowContext) = Code.Operator(", ")
    def Dot(implicit ctx: FlowContext) = Code.Operator(".")
    def Colon(implicit ctx: FlowContext) = Code.Operator(":")
    def Space(implicit ctx: FlowContext) = Code.Operator(" ")
    def LineBreak(implicit ctx: FlowContext) = Code.Operator("\n")

    def ConsolasFont(implicit ctx: FlowContext) = Font.font("consolas", ctx.fontSize)
    def ConsolasBoldFont(implicit ctx: FlowContext) = Font.font("consolas", FontWeight.Bold, ctx.fontSize)
    def ConsolasItalicFont(implicit ctx: FlowContext) = Font.font("consolas", FontPosture.Italic, ctx.fontSize)
  }

  protected[gui] object Code {
    class Node(text: String)(implicit ctx: FlowContext) extends Text(text) { self =>
      val renderer = ctx.renderer

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
      def withUnderline = {
        underline = true
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
          val cursor = self.cursor.value

          def apply() = {
            self.font = font
            self.fill = fill
            self.style = style
            self.underline = underline
            self.cursor = cursor
          }
        }
        finalized = true
      }

      def isFinalized = finalized

      def reset: Unit = resetState()

      onMouseEntered = handle {
        renderer.pane.getMode.onMouseEnteredNode(this)
      }

      onMouseExited = handle {
        renderer.pane.getMode.onMouseExitedNode(this)
      }

      onMouseClicked = handle {
        renderer.pane.getMode.onMouseClickedNode(this)
      }
    }

    private def Raw(text: String)(implicit ctx: FlowContext) = new Node(text) withFont Consts.ConsolasFont

    def Operator(text: String)(implicit ctx: FlowContext) = Raw(text) withColor Black
    def TreeName(text: String)(implicit ctx: FlowContext) = Raw(text) withColor rgb(181, 58, 103)
    def Literal(text: String)(implicit ctx: FlowContext) = Raw(text) withColor rgb(226, 160, 255)
    def Identifier(text: String)(implicit ctx: FlowContext) = Raw(text) withColor rgb(94, 94, 255)
    def BoundVar(text: String)(implicit ctx: FlowContext) = Raw(text) withColor Color.DarkGray withFont Consts.ConsolasItalicFont
    def Type(text: String)(implicit ctx: FlowContext) = Raw(text) withColor Black
    def ADTType(text: String)(implicit ctx: FlowContext) = Raw(text) withColor rgb(210, 87, 0) withFont Consts.ConsolasBoldFont
    def Keyword(text: String)(implicit ctx: FlowContext) = Raw(text) withColor rgb(193, 58, 85) withFont Consts.ConsolasBoldFont
    def Indent(n: Int)(implicit ctx: FlowContext) = Raw("  " * n)
  }

  protected case class FlowContext(
      indent: Int, parents: List[Expr], boundVars: Set[ValDef], fontSize: Double, renderer: ASTRenderer) {
    def indented = FlowContext(indent + 1, parents, boundVars, fontSize, renderer)
    def withParent(e: Expr) = FlowContext(indent, e :: parents, boundVars, fontSize, renderer)
    def withBoundVars(v: Iterable[ValDef]) = FlowContext(indent, parents, boundVars ++ v, fontSize, renderer)
  }

  import Consts._

  protected object BinaryOperator {
    def unapply(e: Expr): Option[(Expr, Expr, String)] = e match {
      case Equals(a, b)  => Some((a, b, "=="))
      case Implies(a, b) => Some((a, b, "==>"))
      case _             => None
    }
  }

  protected abstract class TextClickEvent extends EventHandler[MouseEvent]

  protected def nary(exprs: Seq[Seq[Code.Node]], sep: String = ", ", init: String = "", closing: String = "",
                     hideIfEmptyExprs: Boolean = false)(implicit ctx: FlowContext): Seq[Code.Node] = {
    val initNode = if (init.isEmpty()) Nil else Seq(Code.Operator(init))
    val exprNodes = if (exprs.isEmpty) Nil else exprs.init.flatMap(_ :+ Code.Operator(sep)) ++ exprs.last
    val closingNode = if (closing.isEmpty()) Nil else Seq(Code.Operator(closing))

    if (exprNodes.isEmpty && hideIfEmptyExprs) Nil
    else initNode ++ exprNodes ++ closingNode
  }

  protected def typeNode(tpe: Type)(implicit ctx: FlowContext): Seq[Code.Node] = Seq(Code.Type(prettyPrint(tpe, PrinterOptions())))

  protected def block(stmt: Seq[Code.Node])(implicit ctx: FlowContext): Seq[Code.Node] =
    Seq(OpeningBrace, LineBreak, Code.Indent(ctx.indent + 1)) ++ stmt ++ Seq(LineBreak, Code.Indent(ctx.indent), ClosingBrace)

  protected def buildFlowImpl(e: Expr)(implicit ctx: FlowContext): Seq[Code.Node] = e match {
    case FractionLiteral(a, b)         => Seq(Code.Literal(a.toString), Code.Operator("/"), Code.Literal(b.toString))

    case x: Literal[AnyRef] @unchecked => Seq(Code.Literal(x.value.toString))

    case BinaryOperator(a, b, op)      => buildFlow(a) ++ Seq(Space, Code.Operator(op), Space) ++ buildFlow(b)

    case v @ Variable(id, _, _)        => Seq(if (ctx.boundVars contains v.toVal) Code.BoundVar(id.toString) else Code.Identifier(id.toString))

    case FunctionInvocation(f, tps, args) =>
      Seq(Code.Identifier(f.toString)) ++ nary(tps map typeNode, ", ", "[", "]", true) ++ nary(args map buildFlow, ", ", "(", ")")

    case ADT(ADTType(id, tps), args) =>
      Seq(Code.ADTType(id.toString)) ++ nary(tps map typeNode, ", ", "[", "]", true) ++ nary(args map buildFlow, ", ", "(", ")")

    case Application(f, args) =>
      Seq(Code.Identifier(f.toString)) ++ nary(args map buildFlow, ", ", "(", ")")

    case ADTSelector(e, id) =>
      buildFlow(e) ++ Seq(Dot, Code.Identifier(id.toString))

    case IsInstanceOf(e, tp) =>
      buildFlow(e) ++ Seq(Dot, Code.Keyword("is"), OpeningSquareBracket) ++ typeNode(tp) :+ ClosingSquareBracket

    case AsInstanceOf(e, tp) =>
      buildFlow(e) ++ Seq(Dot, Code.Keyword("as"), OpeningSquareBracket) ++ typeNode(tp) :+ ClosingSquareBracket

    case IfExpr(cond, then, elze) =>
      Seq(Code.Keyword("if"), Space, OpeningBracket) ++ buildFlow(cond) ++ Seq(ClosingBracket, Space) ++
        block(buildFlow(then)(ctx indented)) ++ Seq(Code.Keyword(" else ")) ++ block(buildFlow(elze)(ctx indented))

    case Forall(vals, expr) =>
      Seq(Code.Operator("\u2200")) ++ nary(vals.map { v =>
        Seq(Code.BoundVar(v.id.toString), Colon) ++
          typeNode(v.tpe)
      }) ++ Seq(Dot, Space) ++ buildFlow(expr)(ctx withBoundVars (vals))

    case And(exprs) =>
      nary(exprs map buildFlow, " && ")

    case Or(exprs) =>
      nary(exprs map buildFlow, " || ")

    case Operator(exprs, _) =>
      Seq(Code.TreeName(e.getClass.getSimpleName)) ++ nary(exprs map buildFlow, ", ", "(", ")")
  }

  protected def buildFlow(e: Expr)(implicit ctx: FlowContext): Seq[Code.Node] = {
    val nodes = buildFlowImpl(e)(ctx withParent e)
    nodes filter { !_.isFinalized } foreach { _.finalize(e, nodes) }
    nodes
  }

  class ASTRenderer(val pane: ExpressionPane, expr: Expr, fontSize: Double) extends TextFlow {
    val codeNodes = buildFlow(expr)(FlowContext(0, Nil, Set.empty, fontSize, this))

    children = codeNodes

    def reset: Unit = {
      codeNodes foreach (_.reset)
    }
  }
}