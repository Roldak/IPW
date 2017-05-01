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
import scala.collection.mutable.{Map => MutableMap}
import scalafx.scene.layout.Pane

protected[gui] trait ExpressionPanes { window: AssistantWindow =>
  class ExpressionPane(val expressionFontSize: Double) extends ScrollPane { scrollPane =>
    case class Element(expr: Expr, callback: () => Unit, curs: Cursor = Cursor.Default) extends BorderPane {
      val renderer = new ASTRenderer(scrollPane, expr, expressionFontSize) 
      
      padding = Insets(10)
      style <== when (hover) choose Style.eqHoverStyle otherwise Style.eqStyle
      center = renderer
      minWidth <== scrollPane.width - 2
      cursor = curs
      
      onMouseClicked = handle(callback())
    }
    
    object PreviewBox extends VBox {
      private val previewCache = MutableMap[Expr, Node]()
      
      def setExpr(expr: Expr): Unit = {
        style = Style.previewStyle
        children = previewCache.getOrElseUpdate(expr, Element(expr, () => {}))
      }
      
      def setExprs(exprs: Seq[(Expr, () => Unit)]): Unit = {
        style = Style.previewStyle
        children = exprs map (e => Element(e._1, e._2, Cursor.Hand))
      }
      
      def clear(): Unit = {
        style = null
        children = Seq()
      }
      
      def clearCache(): Unit = previewCache.clear()
    }
    
    object ResultBox extends VBox {
      private val separator = new BorderPane {
        padding = Insets(30, 0, 30, 0)
        minWidth <== scrollPane.width - 2
        center = new Text {
          text = "Apply suggestions from the panel on the right until the goal below is reached"
          font = Font.font(15)
        }
      }
      
      def setExpr(expr: Expr): Unit = {
        val elem = Element(expr, () => {})
        elem.style.unbind()
        elem.style = Style.goalStyle
        children = Seq(separator, elem)
      }
      
      def clear(): Unit = {}
    }

    private val box = new VBox
    private val elements = new ArrayBuffer[Element]
    private var mode: InputMode = Default
    
    def lastRenderer = elements.last.renderer
    def getMode = mode
    
    content = new VBox {
      children = Seq(box, PreviewBox, ResultBox)
    }
    
    def addElement(expr: Expr, onClick: () => Unit = () => {}): Unit = {
      elements += Element(expr, onClick)
      box.children.add(elements.last)
      mode.onNewRenderer(lastRenderer)
      PreviewBox.clearCache()
      Platform.runLater { scrollPane.vvalue = 1.0 }
    }
    
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