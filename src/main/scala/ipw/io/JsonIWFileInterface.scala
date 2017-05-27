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
 * 			expression: "(A && B) => (B && A)",
 * 			cases: [
 * 				{
 * 					title: "main case",
 * 					complete: true
 * 					steps: [
 * 						"FixVariable",
 * 						"Assume",
 * 						...
 * 					]
 * 				},
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
      private val serializedCases: MutableMap[String, (Boolean, Seq[String])]) extends ProofDocument(source, id) {

    import net.liftweb.json.JsonDSL._

    private val cases = ArrayBuffer[ProofCase]()

    override def getCase(title: String, suggestingEnd: SuggestingEnd, onStopAutopilot: () => Unit): ProofCase = {
      val newCase = serializedCases.get(title) map {
        case (complete, steps) =>
          new ProofCase(title, complete, ArrayBuffer() ++ steps, suggestingEnd, onStopAutopilot)
      } getOrElse (new ProofCase(title, false, ArrayBuffer(), suggestingEnd, onStopAutopilot))
      cases.append(newCase)
      newCase
    }

    private def renderCase(c: ProofCase): JValue =
      ("title" -> c.title) ~
        ("complete" -> c.complete) ~
        ("steps" -> c.steps.toList)

    override def save(): Unit = {
      val content = Source.fromFile(source).getLines().mkString
      val original: JValue = parse(content)

      val withoutOld = original transform {
        case JField("proofs", proofs) => proofs transform {
          case JObject(proof) if proof contains JField("expression", id.toString) => JNothing
        }
      }

      val newProof: JValue = ("proofs" -> List(
        ("expression" -> id.toString) ~
          ("cases" -> cases.map(renderCase))))

      val merged = withoutOld merge newProof

      val writer = new PrintWriter(new File(source))
      writer.write(compact(render(merged)))
      writer.close()
    }
    
    override def clear(): Unit = {
      cases.clear()
      save()
    }
  }

  private def readJStringList(lst: List[JValue]): List[String] = for (JString(str) <- lst) yield str

  override def readProofDocument(source: String, id: ProofIdentifier): ProofDocument = {
    val content = Source.fromFile(source).getLines().mkString
    val json = parse(content)

    val cases = for {
      JField("proofs", proofs) <- json
      JObject(proof) <- proofs
      JField("expression", JString(expr)) <- proof if id.toString == expr
      JField("cases", cases) <- proof
      JObject(proofCase) <- cases
      JField("title", JString(title)) <- proofCase
      JField("complete", JBool(complete)) <- proofCase
      JField("steps", JArray(steps)) <- proofCase
    } yield {
      (title, (complete, readJStringList(steps)))
    }

    new JsonProofDocument(source, id, MutableMap() ++ cases)
  }
}