package ipw.gui

import scalafx.Includes._
import scalafx.scene.control.ScrollPane
import scalafx.scene.layout.VBox
import inox._
import inox.trees._
import inox.trees.dsl._
import scalafx.scene.layout.BorderPane
import scalafx.geometry.Insets
import scalafx.application.Platform

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.{Map => MutableMap}

protected[gui] trait ExpressionPanes { window: AssistantWindow =>
  class ExpressionPane(val expressionFontSize: Double) extends ScrollPane { scrollPane =>
    case class Element(expr: Expr, callback: () => Unit) extends BorderPane {
      val renderer = new ASTRenderer(scrollPane, expr, expressionFontSize) 
      
      padding = Insets(10)
      style <== when (hover) choose Style.eqHoverStyle otherwise Style.eqStyle
      center = renderer
      minWidth <== scrollPane.width - 2
      
      onMouseClicked = handle(callback())
    }
    
    case object PreviewBox extends BorderPane {
      private val previewCache = MutableMap[Expr, ASTRenderer]()
      
      style <== when (hover) choose Style.eqHoverStyle otherwise Style.eqStyle
      minWidth <== scrollPane.width - 2
      
      def setExpr(expr: Expr): Unit = {
        padding = Insets(10)
        center = previewCache.getOrElseUpdate(expr, new ASTRenderer(scrollPane, expr, expressionFontSize))
      }
      
      def clear: Unit = {
        padding = Insets(0)
        center = null
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
    
    def setPreviewExpr(e: Expr): Unit = PreviewBox.setExpr(e)
    def clearPreview: Unit = PreviewBox.clear
  }
}