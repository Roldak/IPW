package ipw.gui

import scalafx.Includes._
import inox._
import inox.trees._
import inox.trees.dsl._

trait Modes { window: AssistantWindow =>

  protected[gui] sealed abstract class InputMode {
    def onNewRenderer(renderer: ASTRenderer): Unit = {}
    def onRemoveRenderer(renderer: ASTRenderer): Unit = {
      renderer.reset
    }

    def onMouseEnteredNode(node: Code.Node): Unit = {}
    def onMouseExitedNode(node: Code.Node): Unit = {}
    def onMouseClickedNode(node: Code.Node): Unit = {}
  }

  protected[gui] case object Default extends InputMode {
    override def onMouseEnteredNode(node: Code.Node): Unit = {
      node.neighbors foreach { n =>
        n.underline = true
      }
    }

    override def onMouseExitedNode(node: Code.Node): Unit = {
      node.neighbors foreach (_.reset)
    }
  }

  protected[gui] case class SelectingInExpression(renderer: ASTRenderer, selectables: Seq[(Expr, () => Unit)]) extends InputMode {
    override def onNewRenderer(renderer: ASTRenderer): Unit = {

    }

    override def onMouseEnteredNode(node: Code.Node): Unit = {

    }

    override def onMouseExitedNode(node: Code.Node): Unit = {

    }

    override def onMouseClickedNode(node: Code.Node): Unit = {

    }
  }
}