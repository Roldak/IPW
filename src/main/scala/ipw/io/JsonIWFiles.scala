package ipw.io

import ipw.AssistedTheory
import net.liftweb.json._
import scala.io.Source
import java.io.PrintWriter
import java.io.File

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
  override def readIWFDocument(source: String, title: IWFTitle): IWFDocument = {
    val content = Source.fromFile(source).getLines().mkString
    val json = parse(content)
    
    val tmp = for {
      JObject(child) <- json
      JField("proofs", proofs) <- child
      JField("expression", expr) <- proofs if title._1.toString == expr
      JField("theorems", thms) <- proofs
      JString(thm) <- thms if title._2.exists(t => t.expression.toString == thm)
      JField("content", content) <- child
    } yield (content.toString)
    
    println(tmp)
    
    Nil
  }
  
  override def writeIWFDocument(source: String, title: IWFTitle, document: IWFDocument): Unit = {
    import net.liftweb.json.JsonDSL._
    
    val content = Source.fromFile(source).getLines().mkString
    val json: JValue = parse(content)
    
    val newJson: JValue = ("proofs" -> List(
        ("expression" -> title._1.toString) ~
        ("theorems" -> title._2.map(_.toString)) ~
        ("content" -> document.map(_.toString))
    ))
    
    val merged = json merge newJson
    
    println(newJson)
    
    val writer = new PrintWriter(new File(source))
    writer.write(compact(render(newJson)))
    writer.close()
  }
}