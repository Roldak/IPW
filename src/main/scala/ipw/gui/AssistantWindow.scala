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
import scalafx.scene.control.Alert.AlertType

trait AssistantWindow
    extends Rendering
    with ExpressionPanes
    with Modes { theory: AssistedTheory =>

  Platform.implicitExit = false

  new JFXPanel() // force init

  protected[ipw] class Window(protected val stage: Stage, protected val tabAppender: Tab => Unit) { theWindow =>
    def openNewTab(title: String, choosingEnd: ChoosingEnd): Future[WindowTab] = {
      val tabPromise = Promise[WindowTab]

      Platform.runLater {
        val suggestionBuffer = new ObservableBuffer[(String, Seq[Suggestion])]
        val expressionPane = new ExpressionPane(14)
        val theoremPane = new ExpressionPane(12)

        def onSelectSuggestion(s: Suggestion) = () => {
          expressionPane.installMode(Default)
          Platform.runLater {
            suggestionBuffer.clear()
            choosingEnd.write(s)
          }
        }

        val tab = new Tab {
          text = title
          content = new BorderPane { window =>
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
                      println(validSuggs)
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

          onClosed = handle {
            choosingEnd.write(Abort)
          }

          closable = false
        }

        tabAppender(tab)

        val elemStatus = MutableMap[Expr, StatusText]()

        // forever read inputs from the driver (suggestions, etc.) and update view
        asyncForever {
          val (expr, suggs, thms) = choosingEnd.read

          Platform.runLater {
            val elem = expressionPane.addElement(expr)
            elemStatus.get(expr) foreach (elem.right = _)

            suggestionBuffer.clear()
            suggestionBuffer ++= suggs.groupBy(_.descr).toSeq

            theoremPane.clear
            thms foreach {
              case (name, thm) =>
                val thmElem = theoremPane.addElement(thm.expression)
                thmElem.right = new Text(s" <$name>")
            }
          }
        }

        // "return" a callback to the driver which he can call to update on the status of some proof steps
        tabPromise.success {
          WindowTab({ (e: Expr, status: Status) =>
            Platform.runLater {
              val statusText = elemStatus.getOrElseUpdate(e, new StatusText)
              expressionPane.elementsForExpr(e) foreach (_.right = statusText)
              statusText.updateWith(status)
            }
          }, theWindow, title)
        }
      }

      tabPromise.future
    }
  }

  protected[ipw] case class WindowTab(statusCallback: StatusCallback, window: Window, title: String)

  protected[ipw] def openAssistantWindow(done: Future[Unit]): Future[Window] = {
    val windowPromise = Promise[Window]

    Platform.runLater {
      val tabsList = new ObservableBuffer[Tab]()
      val tabPane = new TabPane

      val stage = new Stage { outer =>
        title = "IPW Assistant Window"
        width = 1350
        height = 800
        scene = new Scene {
          stylesheets = Seq("file:resources/assistantWindow.css")
          root = tabPane
        }

        onCloseRequest = handle {
          tabsList.foreach { tab => tab.onClosed.value.handle(null) }
        }
      }

      def appendTab(x: Tab) = {
        tabsList.append(x)
        tabPane.tabs = tabsList
        tabPane.selectionModel.value.select(x)
      }

      // automatically close tab when notified that the theorem has been proved
      async {
        Await.ready(done, Duration.Inf)
        Platform.runLater { stage.close() }
      }

      // "return" a callback to the driver which he can call to update on the status of some proof steps
      windowPromise.success(new Window(stage, appendTab))

      stage.showAndWait()
    }

    windowPromise.future
  }

  protected[ipw] def promptTheoremName(expr: Expr, default: String): String = {
    val name = Promise[String]
    Platform.runLater {
      val dialog = new TextInputDialog(defaultValue = default) {
        title = "Assumption Name"
        headerText = prettyPrint(expr, PrinterOptions())
        contentText = "Please enter a name for the assumption:"
      }

      name.success(dialog.showAndWait().getOrElse(default))
    }
    Await.result(name.future, Duration.Inf)
  }

  protected[ipw] def promptTheoremSplit(exprs: Seq[Expr]): Boolean = {
    val choice = Promise[Boolean]
    Platform.runLater {
      val dialog = new Alert(AlertType.Confirmation) {
        title = "Split Theorem"
        headerText = exprs.zipWithIndex map { case (e, i) => s"${i + 1}. ${prettyPrint(e, PrinterOptions())}" } mkString("\n")
        contentText = s"Do you want to split the theorem in ${exprs.size}?"
      }

      choice.success(dialog.showAndWait() map (_ == ButtonType.OK) getOrElse(false))
    }
    Await.result(choice.future, Duration.Inf)
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