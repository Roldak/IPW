import inox._
import inox.trees._
import inox.trees.dsl._
import welder._
import ipw._

object Main {

  // We create an identifier for the function.
  val sum = FreshIdentifier("sum")

  // We define the sum function.
  val sumFunction = mkFunDef(sum)() {
    case _ =>

      // The function takes only one argument, of type `BigInt`.
      val args: Seq[ValDef] = Seq("n" :: IntegerType)

      // It returns a `BigInt`.
      val retType: Type = IntegerType

      // Its body is defined as:
      val body: Seq[Variable] => Expr = {
        case Seq(n) =>
          if_(n === E(BigInt(0))) {
            // We return `0` if the argument is `0`.
            E(BigInt(0))
          } else_ {
            // We call the function recursively on `n - 1` in other cases.
            val predN = n - E(BigInt(1))
            E(sum)(predN) + n
          }
      }

      (args, retType, body)
  }

  // Our program simply consists of the `sum` function.
  val sumProgram = InoxProgram(Context.empty,
    NoSymbols.withFunctions(Seq(sumFunction)))

  val theory = theoryOf(sumProgram)
  val assistant = assistantOf(theory)

  import theory._
  import assistant._

  def main(args: Array[String]): Unit = {
    val thm = IPWprove(E(sum)(E(BigInt(3))) === E(BigInt(6)), new java.io.File("test.iwf"), Map.empty)
    println(thm)
  }
}