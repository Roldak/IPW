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

    val tfBackground = """
      -fx-background-color: rgb(250, 250, 250);
      -fx-border-color: black;
      -fx-border-size: 1px;
    """

    Platform.runLater {
      val box = new VBox {
        spacing = 10
      }
      val lv = new ObservableBuffer[Suggestion]

      val dialogStage = new Stage { outer =>
        title = "IPW Assistant Window"
        width = 800
        height = 600
        scene = new Scene {
          root = new BorderPane {
            padding = Insets(20)
            bottom = new Button {
              text = "Click me to close the dialog"
              onAction = handle { outer.close() }
            }
            center = new BorderPane {
              style = tfBackground
              margin = Insets(10, 0, 10, 0)
              center = new ScrollPane {
                padding = Insets(10)
                content = box
              }
            }
            right = new BorderPane {
              padding = Insets(10, 0, 10, 5)
              center = new ListView[Suggestion] {
                items = lv
                cellFactory = TextFieldListCell.forListView(StringConverter.toStringConverter[Suggestion](s => s.descr))
                selectionModel().selectedItem.onChange { (_, _, newValue) =>
                  if (newValue != null) {
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
          lv.clear()
          lv ++= suggs
          box.children.add(new ASTRenderer(expr))
        }
      }

      dialogStage.showAndWait()

      Platform.exit()
    }
  }
}