package ipw.gui

import scalafx.Includes._
import scalafx.application.JFXApp
import scalafx.scene.Scene
import scalafx.scene.paint.Color._
import scalafx.scene.shape.Rectangle
import scalafx.application.Platform
import scalafx.scene.layout.BorderPane
import scalafx.scene.control.Button
import scalafx.geometry.Insets
import scalafx.stage.Stage

import java.util.concurrent

import javafx.embed.swing.JFXPanel

object AssistantWindow {
  Platform.implicitExit = false

  new JFXPanel() // force init

  def open() = {
    Platform.runLater {
      val dialogStage = new Stage { outer =>
        title = "IPW Assistant Window"
        width = 800
        height = 600
        scene = new Scene {
          root = new BorderPane {
            padding = Insets(25)
            bottom = new Button {
              text = "Click me to close the dialog"
              onAction = handle { outer.close() }
            }
          }
        }
      }

      dialogStage.showAndWait()

      Platform.exit()
    }
  }
}