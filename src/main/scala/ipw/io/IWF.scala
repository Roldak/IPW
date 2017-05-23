package ipw.io

import ipw.AssistedTheory

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Queue

protected[ipw] trait IWFileInterface { theory: AssistedTheory =>
  protected[ipw] type ProofIdentifier = (Expr, Seq[Theorem])
  
  protected[ipw] def readProofDocument(source: String, id: ProofIdentifier): ProofDocument
}

protected[ipw] trait IOs { theory: AssistedTheory with IWFileInterface =>
  
  type SerializedChoice = (Seq[String], Int)
  
  protected[ipw] final class ProofCase(
      private val suggestingEnd: SuggestingEnd, 
      private val onStopAutoPilot: () => Unit, 
      private val steps: ArrayBuffer[SerializedChoice]) {
    
    private val writes = Queue[ProofState]()
    private var i = 0
      
    private def serialized(state: ProofState): Seq[String] = state._2 map (_._2.toString)
    
    def read: UpdateStep = {
      val state = writes.dequeue()
      val serState = serialized(state)
      
      if (i < steps.size) { // autopilot
        if (serState == steps(i)._1) {
          val res = state._2(steps(i)._2)._2
          i += 1
          return res
        } else {
          steps.trimEnd(steps.size - i)
          onStopAutoPilot()
        }
      }
      
      val res = suggestingEnd.read
      steps.append((serState, state._2.indexOf(res)))
      i += 1
      res
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