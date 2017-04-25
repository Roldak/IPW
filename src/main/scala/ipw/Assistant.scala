package ipw

import inox._
import inox.trees._
import inox.trees.dsl._
import java.io.{File => JFile}
import welder._
import com.sun.media.sound.Platform
import ipw.gui.AssistantWindow

trait Assistant {
  val theory: Theory
  
  import theory._
  
  def IPWprove(expr: Equals, source: JFile, thms: Map[String, Theorem]): Attempt[Theorem] = {
    AssistantWindow.open()
    prove(expr)
  }
}