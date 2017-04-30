package ipw.gui

import scalafx.Includes._
import scalafx.scene._
import scalafx.scene.layout._
import scalafx.scene.text._
import scalafx.scene.control._
import scalafx.scene.paint.Color._
import scalafx.stage._
import scalafx.geometry.Insets
import scalafx.application.Platform
import javafx.embed.swing.JFXPanel
import ipw._
import inox.trees.dsl._
import inox.trees._
import scalafx.collections.ObservableBuffer
import scalafx.concurrent.Task
import scalafx.scene.control.cell.TextFieldListCell
import scalafx.util.StringConverter

trait AssistantWindow 
  extends Rendering
    with Styles
    with ExpressionPanes { theory: AssistedTheory =>

  Platform.implicitExit = false

  new JFXPanel() // force init

  private def async(f: => Unit): Unit = (new Thread {
    override def run = f
  }).start()

  private def asyncForever(f: => Unit): Unit = async {
    while (true) f
  }

  def openAssistantWindow(choosingEnd: ChoosingEnd, thms: Map[String, Theorem]) = {
    Platform.runLater {
      val suggestionBuffer = new ObservableBuffer[Suggestion]
      val expressionPane = new ExpressionPane(14)
      
      val dialogStage = new Stage { outer =>
        title = "IPW Assistant Window"
        width = 1024
        height = 768
        scene = new Scene {
          root = new BorderPane { window =>
            padding = Insets(20)
            center = new BorderPane {
              style = Style.tfStyle
              margin = Insets(10, 0, 10, 0)
              center = expressionPane
              prefWidth <== window.width * 2 / 3
            }
            right = new BorderPane {
              padding = Insets(10, 0, 10, 5)
              top = new ListView[Suggestion] {
                items = suggestionBuffer
                cellFactory = TextFieldListCell.forListView(StringConverter.toStringConverter[Suggestion](s => s.descr))
                selectionModel().selectedItem.onChange { (_, _, newValue) =>
                  if (newValue != null) { // is null when suggestionBuffer.clear() triggers onChange
                    choosingEnd.write(newValue)
                    Platform.runLater { suggestionBuffer.clear() }
                  }
                }
              }
              center = new ExpressionPane(12) {
                thms.foreach {case (name, thm) => addElement(thm.expression)}
              }
              prefWidth <== window.width * 1 / 3
            }
          }
        }
      }

      asyncForever {
        val (suggs, expr) = choosingEnd.read
        Platform.runLater {
          suggestionBuffer.clear()
          suggestionBuffer ++= suggs
          expressionPane.addElement(expr)
        }
      }

      dialogStage.showAndWait()

      Platform.exit()
    }
  }
}