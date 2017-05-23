package ipw.io

import ipw.AssistedTheory
import net.liftweb.json._
import scala.io.Source
import java.io.PrintWriter
import java.io.File

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.ArrayBuffer

/*
 * Format:
 * """
 * {
 * 	proofs: [
 * 		{
 * 			expression: "(A && B) => (B && A)"
 * 			theorems: [
 * 				"P(x)",
 * 				"Vx. f(x) < 42"
 * 			],
 * 			content: [
 * 				"FixVariable",
 * 				"Assume",
 * 				...
 * 			]
 * 		},
 * 		...
 *  ]
 * }
 * """
 */
trait JsonIWFiles extends IWFileInterface { theory: AssistedTheory =>
  private class JsonProofDocument(
      private val source: String, 
      private val id: ProofIdentifier, 
      private val serializedCases: MutableMap[String, Seq[SerializedChoice]]) extends ProofDocument(source, id) {
    
    private val cases = ArrayBuffer[ProofCase]()
    
    override def getCase(title: String, suggestingEnd: SuggestingEnd, onStopAutopilot: () => Unit): ProofCase = { 
      val newCase = new ProofCase(suggestingEnd, onStopAutopilot, ArrayBuffer() ++ serializedCases.getOrElse(title, Nil))
      cases.append(newCase)
      newCase
    }
    
    override def save(): Unit = {
      import net.liftweb.json.JsonDSL._
      
      println(cases)
      
/*
      val content = Source.fromFile(source).getLines().mkString
      val json: JValue = parse(content)

      val newJson: JValue = ("proofs" -> List(
        ("expression" -> title._1.toString) ~
          ("theorems" -> title._2.map(_.toString)) ~
          ("content" -> document.map(_.toString))))

      val merged = json merge newJson

      println(newJson)

      val writer = new PrintWriter(new File(source))
      writer.write(compact(render(newJson)))
      writer.close()*/
    }
  }

  override def readProofDocument(source: String, id: ProofIdentifier): ProofDocument = {
    val content = Source.fromFile(source).getLines().mkString
    val json = parse(content)

    val cases = for {
      JObject(child) <- json
      JField("proofs", proofs) <- child
      JField("expression", expr) <- proofs if id._1.toString == expr
      JField("dependencies", deps) <- proofs
      JString(thm) <- deps if id._2.exists(t => t.expression.toString == thm)
      JField("cases", cases) <- proofs
      JField("title", JString(title)) <- cases
      JField("steps", steps) <- cases
    } yield {
      val lst = for {
        JField("suggs", suggs) <- steps
        JField("choice", JInt(choice)) <- steps
      } yield {
        val lst = for {
          JString(suggStr) <- suggs
        } yield suggStr
        
        (lst.toSeq, choice.toInt)
      }

      (title, lst.toSeq)
    }

    new JsonProofDocument(source, id, MutableMap() ++ cases)
  }
}