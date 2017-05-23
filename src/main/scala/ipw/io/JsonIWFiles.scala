package ipw.io

import ipw.AssistedTheory
import net.liftweb.json._
import scala.io.Source
import java.io.PrintWriter
import java.io.File

import scala.collection.mutable.{ Map => MutableMap }
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
	  
    import net.liftweb.json.JsonDSL._
    
    private val cases = ArrayBuffer[ProofCase]()

    override def getCase(title: String, suggestingEnd: SuggestingEnd, onStopAutopilot: () => Unit): ProofCase = {
      val newCase = new ProofCase(title, ArrayBuffer() ++ serializedCases.getOrElse(title, Nil), suggestingEnd, onStopAutopilot)
      cases.append(newCase)
      newCase
    }
    
    private def renderCase(c: ProofCase): JValue = 
      ("title" -> c.title) ~
      ("steps" -> c.steps.toList)

    override def save(): Unit = {
      println(cases)

      val content = Source.fromFile(source).getLines().mkString
      val json: JValue = parse(content)

      val newJson: JValue = ("proofs" -> List(
        ("expression" -> id.toString) ~
          ("cases" -> cases.map(renderCase))))

      val merged = json merge newJson

      println(newJson)

      val writer = new PrintWriter(new File(source))
      writer.write(compact(render(merged)))
      writer.close()
    }
  }

  override def readProofDocument(source: String, id: ProofIdentifier): ProofDocument = {
    val content = Source.fromFile(source).getLines().mkString
    val json = parse(content)

    val cases = for {
      JObject(child) <- json
      JField("proofs", proofs) <- child
      JField("expression", JString(expr)) <- proofs if id.toString == expr
      JField("cases", cases) <- proofs
      JObject(proofCase) <- cases
      JField("title", JString(title)) <- proofCase
      JField("steps", JArray(steps)) <- proofCase
    } yield {
      (title, for {
        JString(stepStr) <- steps
      } yield stepStr)
    }
    
    new JsonProofDocument(source, id, MutableMap() ++ cases)
  }
}