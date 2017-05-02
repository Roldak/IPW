import inox._
import inox.trees.dsl._
import inox.trees.{ forall => _, _ }
import welder._
import ipw._

object Main {
  val proofsFile = new java.io.File("test.iwf")
  
  def mai(args: Array[String]): Unit = {

    val foldlID = FreshIdentifier("foldl")
    val foldrID = FreshIdentifier("foldr")

    val list = FreshIdentifier("List")
    val cons = FreshIdentifier("Cons")
    val nil = FreshIdentifier("Nil")

    val head = FreshIdentifier("head")
    val tail = FreshIdentifier("tail")

    val listADT = mkSort(list)("A")(Seq(cons, nil))
    val consADT = mkConstructor(cons)("A")(Some(list)) {
      case Seq(aT) =>
        Seq(ValDef(head, aT), ValDef(tail, T(list)(aT)))
    }
    val nilADT = mkConstructor(nil)("A")(Some(list))(_ => Nil)

    val foldlFunction = mkFunDef(foldlID)("A") {
      case Seq(aT) => (
        Seq("f" :: ((aT, aT) =>: aT), "z" :: aT, "l" :: T(list)(aT)), aT, {
          case Seq(f, z, l) =>
            if_(l.isInstOf(T(cons)(aT))) {
              E(foldlID)(aT)(f, f(z, l.asInstOf(T(cons)(aT)).getField(head)), l.asInstOf(T(cons)(aT)).getField(tail))
            } else_ {
              z
            }
        })
    }

    val foldrFunction = mkFunDef(foldrID)("A") {
      case Seq(aT) => (
        Seq("f" :: ((aT, aT) =>: aT), "z" :: aT, "l" :: T(list)(aT)), aT, {
          case Seq(f, z, l) =>
            if_(l.isInstOf(T(cons)(aT))) {
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

    val theory = assistedTheoryOf(program)
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

    val theorem = forallI("f" :: ((A, A) =>: A), "z" :: A) { (f, z) =>
      implI(isMonoid(f, z)) { isMonoid =>
        val Seq(isAssoc, isUnit) = andE(isMonoid): Seq[Theorem]

        val lemma = structuralInduction((l: Expr) => forall("x" :: A) {
          x => foldl(f, x, l) === f(x, foldl(f, z, l))
        }, "l" :: ListA) {
          case (ihs, goal) =>
            ihs.expression match {
              case C(`cons`, h, t) =>
                forallI("x" :: A) { x =>
                  /*foldl(f, x, ihs.expression) ==|
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
                f(x, foldl(f, z, ihs.expression))*/
                  IPWprove(
                    foldl(f, x, ihs.expression) === f(x, foldl(f, z, ihs.expression)),
                    proofsFile,
                    Map("Associativity of `f`" -> isAssoc,
                      "Unity of `f`" -> isUnit),
                    Some(ihs))
                }

              case C(`nil`) => isUnit
            }
        }

        println(lemma)

        structuralInduction((l: Expr) => foldl(f, z, l) === foldr(f, z, l), "l" :: ListA) {
          case (ihs, goal) =>
            ihs.expression match {
              case C(`cons`, h, t) =>
                /*foldl(f, z, ihs.expression) ==|
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
              */
                IPWprove(
                  foldl(f, z, ihs.expression) === foldr(f, z, ihs.expression),
                  proofsFile,
                  Map("Lemma" -> lemma, "unity of `f`" -> isUnit, "Associativity of `f`" -> isAssoc),
                  Some(ihs))

              case C(`nil`) => trivial
            }
        }
      }
    }

    println(theorem)
  }

  def main(args: Array[String]): Unit = {
    val Nat = FreshIdentifier("Nat")
    val Z = FreshIdentifier("Z")
    val Suc = FreshIdentifier("Suc")

    val pred = FreshIdentifier("pred")

    val NatADT = mkSort(Nat)()(Seq(Z, Suc))
    val ZADT = mkConstructor(Z)()(Some(Nat)) { _ => Nil }
    val SucADT = mkConstructor(Suc)()(Some(Nat))(_ => Seq(ValDef(pred, T(Nat)())))

    // We create an identifier for the function.
    val add = FreshIdentifier("add")
    val sum = FreshIdentifier("sum")
    val divBy2 = FreshIdentifier("divBy2")
    val mul = FreshIdentifier("mul")
    
    val NatType = T(Nat)()
    val ZType = T(Z)()
    val SucType = T(Suc)()

    val addFunction = mkFunDef(add)() {
      case _ =>
        val args = Seq("m" :: NatType, "n" :: NatType)
        val retType = NatType
        val body: Seq[Variable] => Expr = {
          case Seq(m, n) =>
            if_(m.isInstOf(ZType)) {
              n
            } else_ {
              val predM = m.asInstOf(SucType).getField(pred)
              SucType(E(add)(predM, n))
            }
        }

        (args, retType, body)
    }

    // We define the sum function.
    val sumFunction = mkFunDef(sum)() {
      case _ =>

        // The function takes only one argument, of type `BigInt`.
        val args: Seq[ValDef] = Seq("n" :: T(Nat)())

        // It returns a `BigInt`.
        val retType: Type = T(Nat)()

        // Its body is defined as:
        val body: Seq[Variable] => Expr = {
          case Seq(n) =>
            if_(n.isInstOf(ZType)) {
              ZType()
            } else_ {
              val predN = n.asInstOf(SucType).getField(pred)
              SucType(E(sum)(predN)) // TODO: Change
            }
        }

        (args, retType, body)
    }
    
    val divBy2Function = mkFunDef(divBy2)() {
      case _ =>
        val args = Seq("n" :: NatType)
        val retType = NatType
        val body: Seq[Variable] => Expr = {
          case Seq(n) =>
            if_ (n.isInstOf(ZType)) {
              ZType()
            } else_ {
              val predN = n.asInstOf(SucType).getField(pred)
              if_ (predN.isInstOf(ZType)) {
                ZType()
              } else_ {
                val predPredN = predN.asInstOf(SucType).getField(pred)
                SucType(E(divBy2)(predPredN))
              }
            }
        }
        (args, retType, body)
    }
    
    val mulFunction = mkFunDef(mul)() {
      case _ => 
        val args = Seq("m" :: NatType, "n" :: NatType)
        val retType = NatType
        val body: Seq[Variable] => Expr = {
          case Seq(m, n) =>
            if_(m.isInstOf(ZType)) {
              ZType()
            } else_ {
              val predM = m.asInstOf(SucType).getField(pred)
              E(add)(E(mul)(predM, n), n)
            }
        }

        (args, retType, body)
    }

    // Our program simply consists of the `sum` function.
    val sumProgram = InoxProgram(Context.empty,
      NoSymbols
        .withADTs(Seq(NatADT, ZADT, SucADT))
        .withFunctions(Seq(sumFunction, addFunction, divBy2Function, mulFunction)))

    val theory = assistedTheoryOf(sumProgram)

    import theory._

    /*val toProve: Expr = forall("n" :: IntegerType) { n =>
      (n >= E(BigInt(0))) ==> {
        E(sum)(n) === (n * (n + E(BigInt(1)))) / E(BigInt(2))
      }
    }*/
    
    //println(evaluated(E(divBy2)(SucType(SucType(SucType(SucType(ZType())))))))
    println(evaluated(E(mul)(SucType(SucType(ZType())), SucType(SucType(SucType(ZType()))))))

    def sum_(n: Expr) = E(sum)(n)
    def add_(m: Expr, n: Expr) = E(add)(m, n)

    val thm = structuralInduction(m => forall("n" :: T(Nat)())(n => add_(m, n) === add_(n, m)), "m" :: T(Nat)()) {
      case (ihs, _) =>
        ihs.expression match {
          case C(`Suc`, mpred) =>
            val lemma = structuralInduction(n => T(Suc)()(add_(n, mpred)) === add_(n, ihs.expression), "n" :: T(Nat)()) {
              case (ihsLemma, _) =>
                ihsLemma.expression match {
                  case C(`Suc`, npred) => IPWprove(
                    T(Suc)()(add_(ihsLemma.expression, mpred)) === add_(ihsLemma.expression, T(Suc)()(mpred)),
                    proofsFile,
                    Map.empty,
                    Some(ihsLemma))
                  case C(`Z`) => trivial
                }
            }

            forallI("n" :: T(Nat)()) { n =>
              IPWprove(add_(ihs.expression, n) === add_(n, ihs.expression), proofsFile, Map("Lemma" -> lemma), Some(ihs))
            }
          case C(`Z`) =>
            val lemma = structuralInduction(n => n === add_(n, ihs.expression), "n" :: T(Nat)()) {
              case (ihsLemma, _) =>
                ihsLemma.expression match {
                  case C(`Suc`, npred) => IPWprove(
                    ihsLemma.expression === add_(ihsLemma.expression, ihs.expression),
                    proofsFile,
                    Map.empty,
                    Some(ihsLemma))
                  case C(`Z`) => trivial
                }
            }
            
            forallI("n" :: T(Nat)()) { n =>
              IPWprove(add_(ihs.expression, n) === add_(n, ihs.expression), proofsFile, Map("Lemma" -> lemma), Some(ihs))
            }
        }
    }

    println(thm)
  }
}