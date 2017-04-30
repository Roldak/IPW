package ipw.gui

import scalafx.Includes._
import scalafx.scene.control.ScrollPane
import scalafx.scene.layout.VBox
import ipw.AssistedTheory
import inox._
import inox.trees._
import inox.trees.dsl._
import scalafx.scene.layout.BorderPane
import scalafx.geometry.Insets
import scalafx.application.Platform

protected[gui] trait ExpressionPanes { window: AssistantWindow =>
  class ExpressionPane(val expressionFontSize: Double) extends ScrollPane { scrollPane =>
    case class Element(expr: Expr, callback: () => Unit) extends BorderPane {
      padding = Insets(10)
      style <== when (hover) choose Style.eqHoverStyle otherwise Style.eqStyle
      center = new ASTRenderer(expr, expressionFontSize)
      minWidth <== scrollPane.width - 2
      
      onMouseClicked = handle(callback())
    }

    private val box = new VBox
    
    content = box
    
    def addElement(expr: Expr, onClick: () => Unit = () => {}): Unit = {
      box.children.add(Element(expr, onClick))
      Platform.runLater { scrollPane.vvalue = 1.0 }
    }
    
    def clear: Unit = box.children.clear()
  }
}