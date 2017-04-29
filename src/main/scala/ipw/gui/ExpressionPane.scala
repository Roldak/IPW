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
  class ExpressionPane extends ScrollPane { scrollPane =>
    case class Element(expr: Expr) extends BorderPane {
      padding = Insets(10)
      style <== when (hover) choose Style.eqHoverStyle otherwise Style.eqStyle
      center = new ASTRenderer(expr)
      minWidth <== scrollPane.width
    }

    val box = new VBox
    
    content = box
    
    def addElement(expr: Expr): Unit = {
      box.children.add(Element(expr))
      Platform.runLater { scrollPane.vvalue = 1.0 }
    }
  }
}