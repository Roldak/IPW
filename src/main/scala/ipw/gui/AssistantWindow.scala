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

import javafx.embed.swing.JFXPanel

import ipw.io.SynchronizedChannel
import ipw.AssistedTheory

trait AssistantWindow { theory: AssistedTheory =>
  
  Platform.implicitExit = false

  new JFXPanel() // force init

  def openAssistantWindow(choosingEnd: ChoosingEnd) = {
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
            top = new Button {
              text = "Choose first"
              onAction = handle {
                val suggs = choosingEnd.read
                choosingEnd.write(if (suggs.isEmpty) Pass else suggs.head)
              }
            }
          }
        }
      }

      dialogStage.showAndWait()

      Platform.exit()
    }
  }
}