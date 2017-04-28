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

private[gui] object Styles {
  val tfStyle = """
      -fx-background-color: rgb(250, 250, 250);
      -fx-border-color: black;
      -fx-border-size: 1px;
    """

  val eqStyle = """
      -fx-background-color: rgb(250, 250, 250);
      -fx-border-color: black;
      -fx-border-width: 0 0 1 0;
    """
}

trait AssistantWindow extends Rendering { theory: AssistedTheory =>

  Platform.implicitExit = false

  new JFXPanel() // force init

  private def async(f: => Unit): Unit = (new Thread {
    override def run = f
  }).start()

  private def asyncForever(f: => Unit): Unit = async {
    while (true) f
  }

  def openAssistantWindow(choosingEnd: ChoosingEnd) = {
    Platform.runLater {
      val suggestionBuffer = new ObservableBuffer[Suggestion]
      val box = new VBox
      val scrollPane = new ScrollPane {
        content = box
      }

      val dialogStage = new Stage { outer =>
        title = "IPW Assistant Window"
        width = 1024
        height = 768
        scene = new Scene {
          root = new BorderPane {
            padding = Insets(20)
            center = new BorderPane {
              style = Styles.tfStyle
              margin = Insets(10, 0, 10, 0)
              center = scrollPane
            }
            right = new BorderPane {
              padding = Insets(10, 0, 10, 5)
              center = new ListView[Suggestion] {
                items = suggestionBuffer
                cellFactory = TextFieldListCell.forListView(StringConverter.toStringConverter[Suggestion](s => s.descr))
                selectionModel().selectedItem.onChange { (_, _, newValue) =>
                  if (newValue != null) { // is null when clearSelection() triggers onChange
                    choosingEnd.write(newValue)
                    Platform.runLater { selectionModel().clearSelection() }
                  }
                }
              }
            }
          }
        }
      }

      asyncForever {
        val (suggs, expr) = choosingEnd.read
        Platform.runLater {
          suggestionBuffer.clear()
          suggestionBuffer ++= suggs

          val child = new BorderPane {
            padding = Insets(10)
            style = Styles.eqStyle
            center = new ASTRenderer(expr)
            minWidth <== scrollPane.width
          }

          box.children.add(child)
        }
      }

      dialogStage.showAndWait()

      Platform.exit()
    }
  }
}