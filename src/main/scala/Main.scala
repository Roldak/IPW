import inox._
import inox.trees.dsl._
import inox.trees.{forall => _, _}
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

  def main(args: Array[String]): Unit = /*{

    val foldlID = FreshIdentifier("foldl")
    val foldrID = FreshIdentifier("foldr")

    val list = FreshIdentifier("List")
    val cons = FreshIdentifier("Cons")
    val nil = FreshIdentifier("Nil")

    val head = FreshIdentifier("head")
    val tail = FreshIdentifier("tail")

    val listADT = mkSort(list)("A")(Seq(cons, nil))
    val consADT = mkConstructor(cons)("A")(Some(list)) { case Seq(aT) =>
      Seq(ValDef(head, aT), ValDef(tail, T(list)(aT)))
    }
    val nilADT = mkConstructor(nil)("A")(Some(list))(_ => Nil)

    val foldlFunction = mkFunDef(foldlID)("A") { case Seq(aT) => (
      Seq("f" :: ((aT, aT) =>: aT), "z" :: aT, "l" :: T(list)(aT)), aT, { case Seq(f, z, l) =>
        if_ (l.isInstOf(T(cons)(aT))) {
          E(foldlID)(aT)(f, f(z, l.asInstOf(T(cons)(aT)).getField(head)), l.asInstOf(T(cons)(aT)).getField(tail))
        } else_ {
          z
        }
      })
    }

    val foldrFunction = mkFunDef(foldrID)("A") { case Seq(aT) => (
      Seq("f" :: ((aT, aT) =>: aT), "z" :: aT, "l" :: T(list)(aT)), aT, { case Seq(f, z, l) =>
        if_ (l.isInstOf(T(cons)(aT))) {
          f(l.asInstOf(T(cons)(aT)).getField(head), E(foldrID)(aT)(f, z, l.asInstOf(T(cons)(aT)).getField(tail)))
        } else_ {
          z
        }
      })
    }

    val symbols = NoSymbols
      .withADTs(Seq(listADT, consADT, nilADT))
      .withFunctions(Seq(foldlFunction, foldrFunction))

    val program = InoxProgram(Context.empty, symbols)

    val theory = theoryOf(program)
    import theory._

    val A = TypeParameter.fresh("A")

    def foldl(f: Expr, z: Expr, l: Expr) = E(foldlID)(A)(f, z, l)
    def foldr(f: Expr, z: Expr, l: Expr) = E(foldrID)(A)(f, z, l)

    val ListA = T(list)(A)
    val ConsA = T(cons)(A)
    val NilA = T(nil)(A)

    def isAssociative(f: Expr): Expr = forall("x" :: A, "y" :: A, "z" :: A)((x, y, z) => f(x, f(y, z)) === f(f(x, y), z))
    def isUnit(f: Expr, z: Expr): Expr = forall("x" :: A)(x => f(x, z) === x && f(z, x) === x)

    def isMonoid(f: Expr, z: Expr): Expr = and(isAssociative(f), isUnit(f, z))

    val theorem = forallI("f" :: ((A,A) =>: A), "z" :: A) { (f, z) =>
      implI(isMonoid(f, z)) { isMonoid => 
        val Seq(isAssoc, isUnit) = andE(isMonoid): Seq[Theorem]

        val lemma = structuralInduction((l: Expr) => forall("x" :: A) {
          x => foldl(f, x, l) === f(x, foldl(f, z, l))
        }, "l" :: ListA) { case (ihs, goal) =>
          ihs.expression match {
            case C(`cons`, h, t) =>
              forallI("x" :: A) { x =>
                foldl(f, x, ihs.expression) ==|
                trivial |
                foldl(f, f(x, h), t) ==|
                forallE(ihs.hypothesis(t))(f(x, h)) |
                f(f(x, h), foldl(f, z, t)) ==|
                forallE(isAssoc)(x, h, foldl(f, z, t)) |
                f(x, f(h, foldl(f, z, t))) ==|
                forallE(ihs.hypothesis(t))(h) |
                f(x, foldl(f, h, t)) ==|
                forallE(isUnit)(h) |
                f(x, foldl(f, f(z, h), t)) ==|
                trivial |
                f(x, foldl(f, z, ihs.expression))
              }

            case C(`nil`) => isUnit
          }
        }

        println(lemma)

        structuralInduction((l: Expr) => foldl(f, z, l) === foldr(f, z, l), "l" :: ListA) { case (ihs, goal) =>
          ihs.expression match {
            case C(`cons`, h, t) =>
              foldl(f, z, ihs.expression) ==|
              trivial |
              foldl(f, f(z, h), t) ==|
              forallE(isUnit)(h) |
              foldl(f, h, t) ==|
              forallE(forallE(lemma)(t))(h) |
              f(h, foldl(f, z, t)) ==|
              ihs.hypothesis(t) |
              f(h, foldr(f, z, t)) ==|
              trivial |
              foldr(f, z, ihs.expression)

            case C(`nil`) => trivial
          }
        }
      }
    }

    println(theorem)
  }*/
  {
    val thm = IPWprove(E(sum)(E(BigInt(3))) === E(BigInt(5)), new java.io.File("test.iwf"), Map.empty)
    println(thm)
  }
}