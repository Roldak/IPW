package ipw.gui

import scalafx.Includes._
import scalafx.scene.paint.Color
import scalafx.scene.Cursor
import inox._
import inox.trees._
import inox.trees.dsl._

protected[gui] trait Modes { window: AssistantWindow =>

  protected[gui] sealed abstract class InputMode {
    def onNewRenderer(renderer: ASTRenderer): Unit = {}
    def onRemoveRenderer(renderer: ASTRenderer): Unit = {
      renderer.reset
      renderer.pane.PreviewBox.clear()
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

  protected[gui] case class SelectingInExpression(renderer: ASTRenderer, selectables: Seq[(Expr, Expr, () => Unit)]) extends InputMode {
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
      val sel = selectables filter (_._1 == node.expression)
      sel foreach { _ =>
        node.neighbors foreach { n =>
          n.underline = true
          n.cursor = Cursor.Hand
        }
      }
      if (sel.size == 1) {
        renderer.pane.PreviewBox.setExpr(sel.head._2)
      } else {
        renderer.pane.PreviewBox.setExprs(sel map (s => (s._2, s._3)))
      }
    }

    override def onMouseExitedNode(node: Code.Node): Unit = {
      if (selectables exists (_._1 == node.expression)) {
        node.neighbors foreach { n =>
          n.underline = false
          n.cursor = Cursor.Default
        }
        renderer.pane.PreviewBox.clear
      }
    }

    override def onMouseClickedNode(node: Code.Node): Unit = {
      val sel = selectables filter (_._1 == node.expression)
      if (sel.size == 1) {
        sel.head._3()
      } else {
        renderer.pane.installMode(SelectingInPreview(renderer, sel map (x => (x._2, x._3))))
      }
    }
  }

  protected[gui] case class SelectingInPreview(initial: ASTRenderer, selectables: Seq[(Expr, () => Unit)]) extends InputMode {
    override def onNewRenderer(r: ASTRenderer): Unit = {
      r.codeNodes foreach { n =>
        n.fill = Color.DarkGray
      }
      if (r == initial) {
        // to have it done only once...
        r.pane.PreviewBox.setExprs(selectables map (s => (s._1, s._2)))
      }
    }
  }
}