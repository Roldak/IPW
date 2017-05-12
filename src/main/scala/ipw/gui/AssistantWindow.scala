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
import ipw.concurrent.Utils._
import scala.concurrent.duration.Duration
import scala.concurrent._
import scala.collection.mutable.{ Map => MutableMap }

trait AssistantWindow
    extends Rendering
    with ExpressionPanes
    with Modes { theory: AssistedTheory =>

  Platform.implicitExit = false

  new JFXPanel() // force init

  protected[ipw] case class WindowTab(statusCallback: StatusCallback)

  def openAssistantWindow(choosingEnd: ChoosingEnd, done: Future[Unit]): Future[WindowTab] = {
    val tabPromise = Promise[WindowTab]

    Platform.runLater {
      val suggestionBuffer = new ObservableBuffer[(String, Seq[Suggestion])]
      val expressionPane = new ExpressionPane(14)
      val theoremPane = new ExpressionPane(12)

      def onSelectSuggestion(s: Suggestion) = () => {
        choosingEnd.write(s)
        expressionPane.installMode(Default)
        Platform.runLater { suggestionBuffer.clear() }
      }

      val dialogStage = new Stage { outer =>
        title = "IPW Assistant Window"
        width = 1350
        height = 800
        scene = new Scene {
          stylesheets = Seq("file:resources/assistantWindow.css")
          root = new BorderPane { window =>
            padding = Insets(20)
            center = new BorderPane {
              styleClass += "main-panel"
              margin = Insets(10, 0, 10, 0)
              center = expressionPane
              prefWidth <== window.width * 2 / 3
            }
            right = new BorderPane {
              padding = Insets(10, 0, 10, 5)
              top = new ListView[(String, Seq[Suggestion])] {
                items = suggestionBuffer
                styleClass += "suggestion-view"
                cellFactory = TextFieldListCell.forListView(StringConverter.toStringConverter[(String, Seq[Suggestion])](_._1))
                selectionModel().selectedItem.onChange { (_, _, newValue) =>
                  if (newValue != null) { // is null when suggestionBuffer.clear() triggers onChange
                    if (newValue._2.size > 1) {
                      val validSuggs = newValue._2 flatMap {
                        case s @ ExprTransformingSuggestion(expr) => Seq((expr, PreviewableSuggestion.unapply(s), onSelectSuggestion(s)))
                        case _                                    => Seq()
                      }
                      expressionPane.installMode(SelectingInExpression(expressionPane.lastRenderer, validSuggs))
                    } else {
                      onSelectSuggestion(newValue._2.head)()
                    }
                  }
                }
              }
              center = theoremPane
              prefWidth <== window.width * 1 / 3
            }
          }
        }

        onCloseRequest = handle {
          choosingEnd.write(Abort)
        }
      }

      val elemStatus = MutableMap[Expr, StatusText]()

      // forever read inputs from the driver (suggestions, etc.) and update view
      asyncForever {
        val (expr, goal, suggs, thms) = choosingEnd.read
        Platform.runLater {
          val elem = expressionPane.addElement(expr)
          elemStatus.get(expr) foreach (elem.right = _)

          suggestionBuffer.clear()
          suggestionBuffer ++= suggs.groupBy(_.descr).toSeq

          theoremPane.clear
          thms foreach { case (name, thm) => theoremPane.addElement(thm.expression) }
          
          expressionPane.ResultBox.setExpr(goal)
        }
      }

      // automatically close window when notified that the theorem has been proved
      async {
        Await.ready(done, Duration.Inf)
        Platform.runLater { dialogStage.close() }
      }

      // "return" a callback to the driver which he can call to update on the status of some proof steps
      tabPromise.success {
        WindowTab { (e: Expr, status: Status) =>
          Platform.runLater {
            val statusText = elemStatus.getOrElseUpdate(e, new StatusText)
            expressionPane.elementsForExpr(e) foreach (_.right = statusText)
            statusText.updateWith(status)
          }
        }
      }

      dialogStage.showAndWait()
    }

    tabPromise.future
  }

  private class StatusText extends Text {
    private var stage: Int = -1
    def updateWith(status: Status): Unit = {
      if (status.stage > stage) {
        stage = status.stage
        text = status.message
      }
    }
  }
}