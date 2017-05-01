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
    with ExpressionPanes
    with Modes { theory: AssistedTheory =>

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
      val suggestionBuffer = new ObservableBuffer[(String, Seq[Suggestion])]
      val expressionPane = new ExpressionPane(14)
      val theoremPane = new ExpressionPane(12)
      
      val dialogStage = new Stage { outer =>
        title = "IPW Assistant Window"
        width = 1350
        height = 800
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
              top = new ListView[(String, Seq[Suggestion])] {
                items = suggestionBuffer
                cellFactory = TextFieldListCell.forListView(StringConverter.toStringConverter[(String, Seq[Suggestion])](s => s._1 + s" (${s._2.size})"))
                selectionModel().selectedItem.onChange { (_, _, newValue) =>
                  if (newValue != null) { // is null when suggestionBuffer.clear() triggers onChange
                    if (newValue._2.size > 1) {
                      val validSuggs = newValue._2 flatMap {
                        case s @ ExprTransformingSuggestion(expr) => Seq((expr, () => {}))
                        case _ => Seq()
                      }
                      expressionPane.installMode(SelectingInExpression(expressionPane.lastRenderer, validSuggs))
                    } else {
                      choosingEnd.write(newValue._2.head)
                      Platform.runLater { suggestionBuffer.clear() }
                    }
                  }
                }
              }
              center = theoremPane
              prefWidth <== window.width * 1 / 3
            }
          }
        }
      }

      asyncForever {
        val (expr, suggs, thms) = choosingEnd.read
        Platform.runLater {
          expressionPane.addElement(expr)
          
          suggestionBuffer.clear()
          suggestionBuffer ++= suggs.groupBy(_.descr).toSeq
          
          theoremPane.clear
          thms foreach {case (name, thm) => theoremPane.addElement(thm.expression)}
        }
      }

      dialogStage.showAndWait()

      Platform.exit()
    }
  }
}