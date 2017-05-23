package ipw.io

import ipw.AssistedTheory

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Queue

protected[ipw] trait IWFileInterface { theory: AssistedTheory =>
  protected[ipw]type ProofIdentifier = Expr

  protected[ipw] def readProofDocument(source: String, id: ProofIdentifier): ProofDocument
}

protected[ipw] trait IOs { theory: AssistedTheory with IWFileInterface =>
  protected[ipw] final class ProofCase(
    val title: String,
    val steps: ArrayBuffer[String],
    private val suggestingEnd: SuggestingEnd,
    private val onStopAutoPilot: () => Unit) {

    private val writes = Queue[ProofState]()
    private var i = 0

    def read: UpdateStep = {
      val state = writes.dequeue()
      
      if (i < steps.size) { // autopilot
        state._2.find(_._2.toString == steps(i)) match {
          case Some(namedSugg) =>
            i += 1
            return namedSugg._2
          case _ =>
            steps.trimEnd(steps.size - i)
            onStopAutoPilot()
        }
      } else {
        onStopAutoPilot()
      }

      val sugg = suggestingEnd.read
      steps.append(sugg.toString)
      i += 1
      sugg
    }

    def write(p: ProofState): Unit = {
      writes.enqueue(p)
      suggestingEnd.write(p)
    }

    private def parseBool(s: String): Option[Boolean] =
      if (s == "true") Some(true)
      else if (s == "false") Some(false)
      else None

    def split(fallback: => Boolean): Boolean = {
      if (i < steps.size) {
        parseBool(steps(i)) match {
          case Some(b) =>
            i += 1
            return b
          case _ =>
            steps.trimEnd(steps.size - i)
            onStopAutoPilot()
        }
      }

      val v = fallback
      steps.append(v.toString)
      i += 1
      v
    }

    def name(fallback: => String): String = {
      if (i < steps.size) {
        i += 1
        steps(i - 1)
      } else {
        val v = fallback
        steps.append(v)
        i += 1
        v
      }
    }
  }

  protected[ipw] abstract class ProofDocument(private val source: String, private val id: ProofIdentifier) {
    def getCase(title: String, suggestingEnd: SuggestingEnd, onStopAutopilot: () => Unit): ProofCase
    def save(): Unit
  }

}