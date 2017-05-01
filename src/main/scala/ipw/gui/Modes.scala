package ipw.gui

import scalafx.Includes._
import scalafx.scene.paint.Color
import scalafx.scene.Cursor
import inox._
import inox.trees._
import inox.trees.dsl._

trait Modes { window: AssistantWindow =>

  protected[gui] sealed abstract class InputMode {
    def onNewRenderer(renderer: ASTRenderer): Unit = {}
    def onRemoveRenderer(renderer: ASTRenderer): Unit = {
      renderer.reset
      renderer.pane.clearPreview
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
      node.neighbors foreach { n =>
        n.underline = false
      }
    }
  }

  protected[gui] case class SelectingInExpression(renderer: ASTRenderer, selectables: Seq[(Expr, Option[Expr], () => Unit)]) extends InputMode {
    override def onNewRenderer(r: ASTRenderer): Unit = {
      if (r == renderer) {
        r.codeNodes foreach { n =>
          if (selectables forall (_._1 != n.expression)) {
            n.fill = Color.DarkGray
          }
        }
      } else {
        r.codeNodes foreach { n =>
          n.fill = Color.DarkGray
        }
      }
    }

    override def onMouseEnteredNode(node: Code.Node): Unit = {
      selectables find (_._1 == node.expression) foreach { s =>
        node.neighbors foreach { n =>
          n.underline = true
          n.cursor = Cursor.Hand
        }
        s._2 foreach (renderer.pane.setPreviewExpr(_))
      }
    }

    override def onMouseExitedNode(node: Code.Node): Unit = {
      if (selectables exists (_._1 == node.expression)) {
        node.neighbors foreach { n =>
          n.underline = false
          n.cursor = Cursor.Default
        }
        renderer.pane.clearPreview
      }
    }

    override def onMouseClickedNode(node: Code.Node): Unit = {
      selectables find (_._1 == node.expression) foreach (_._3())
    }
  }
}