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

  type SerializedChoice = (String)

  protected[ipw] final class ProofCase(
    val title: String,
    val steps: ArrayBuffer[SerializedChoice],
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
            println(i)
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
      suggestingEnd.write(p)
      writes.enqueue(p)
    }
  }

  protected[ipw] abstract class ProofDocument(private val source: String, private val id: ProofIdentifier) {
    def getCase(title: String, suggestingEnd: SuggestingEnd, onStopAutopilot: () => Unit): ProofCase
    def save(): Unit
  }

}