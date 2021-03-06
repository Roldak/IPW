package ipw.gui

import scalafx.Includes._
import scalafx.scene.control.ScrollPane
import scalafx.scene.layout.VBox
import scalafx.scene.Node
import scalafx.scene.Cursor
import scalafx.scene.text._
import inox._
import inox.trees._
import inox.trees.dsl._
import scalafx.scene.layout.BorderPane
import scalafx.geometry.Insets
import scalafx.application.Platform
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.{ Map => MutableMap }
import scalafx.scene.layout.Pane

protected[gui] trait ExpressionPanes { window: AssistantWindow =>
  protected[gui] class ExpressionPane(val expressionFontSize: Double) extends ScrollPane { scrollPane =>
    case class Element(expr: Expr, callback: () => Unit, curs: Cursor = Cursor.Default) extends BorderPane {
      val renderer = new ASTRenderer(scrollPane, expr, expressionFontSize)

      padding = Insets(10)
      styleClass += "expression-pane"
      center = renderer
      minWidth <== scrollPane.width - 2
      cursor = curs

      onMouseClicked = handle(callback())
    }

    object PreviewBox extends VBox {
      private val previewCache = MutableMap[Expr, Node]()

      def setExpr(expr: Expr): Unit = {
        styleClass = Seq("preview-pane")
        children = previewCache.getOrElseUpdate(expr, Element(expr, () => {}))
      }

      def setExprs(exprs: Seq[(Expr, () => Unit)]): Unit = {
        styleClass = Seq("preview-pane")
        children = exprs map (e => Element(e._1, e._2, Cursor.Hand))
      }

      def clear(): Unit = {
        styleClass.clear()
        children = Nil
      }

      def clearCache(): Unit = previewCache.clear()
    }

    private val box = new VBox
    private val elements = new ArrayBuffer[Element]
    private var mode: InputMode = Default

    def lastRenderer = elements.last.renderer
    def getMode = mode

    content = new VBox {
      children = Seq(box, PreviewBox)
    }

    def addElement(expr: Expr, onClick: () => Unit = () => {}): Element = {
      val elem = Element(expr, onClick)
      elements += elem
      box.children.add(elem)
      mode.onNewRenderer(lastRenderer)
      PreviewBox.clearCache()
      Platform.runLater { scrollPane.vvalue = 1.0 }
      elem
    }

    def removeLastAndGetNewLast: Element = {
      val elemIndex = elements.size - 1
      val elemRenderer = elements.last.renderer
      elements.remove(elemIndex)
      box.children.remove(elemIndex)
      mode.onRemoveRenderer(elemRenderer)
      elements.last
    }
    
    def elementsForExpr(expr: Expr): Seq[Element] = elements filter (_.expr == expr)

    def clear: Unit = {
      elements.clear()
      box.children.clear()
      PreviewBox.clearCache()
    }

    def installMode(m: InputMode): Unit = {
      elements foreach (e => mode.onRemoveRenderer(e.renderer))
      mode = m
      elements foreach (e => mode.onNewRenderer(e.renderer))
    }
  }
}