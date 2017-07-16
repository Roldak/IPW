package ipw.ast

import ipw.AssistedTheory
import ipw.ProofBuilder
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._

trait ProofTrees { self: AssistedTheory with ProofBuilder =>

  object AST {

    case class ProofExpr(val e: Expr)
    object ProofExprImplicits {
      import scala.language.implicitConversions
      implicit def expr2ProofExpr(e: Expr): ProofExpr = ProofExpr(e)
      implicit def exprSeq2ProofExprSeq(s: Seq[Expr]): Seq[ProofExpr] = s map expr2ProofExpr
    }

    sealed abstract class Proof

    // Intro rules
    case class ForallI(vs: Seq[ValDef], body: Proof) extends Proof
    case class AndI(trees: Seq[Proof]) extends Proof
    case class ImplI(id: String, hyp: ProofExpr, body: Proof) extends Proof

    // Elim rules
    case class ForallE(tree: Proof, exprs: Seq[ProofExpr]) extends Proof
    case class LetAndE(tree: Proof, ids: Seq[String], body: Proof) extends Proof
    case class AndESelect(tree: Proof, idx: Int) extends Proof
    case class ImplE(tree: Proof, proof: Proof) extends Proof

    // Induction

    case class Case(id: Identifier, fields: Seq[Variable], body: Proof)
    case class StructuralInduction(v: ValDef, prop: ProofExpr, ihs: String, cases: Seq[Case]) extends Proof
    case class HypothesisApplication(ihs: String, expr: ProofExpr) extends Proof

    // Others
    case class Fact(id: String) extends Proof
    case class Let(id: String, value: Proof, in: Proof) extends Proof
    case class Prove(expr: ProofExpr, facts: Seq[Proof] = Nil) extends Proof

    private def findKey[K, T](map: Map[K, T], key: K): Attempt[T] = map get key match {
      case Some(v) => Success(v)
      case _ => Attempt.fail("not found")
    }

    def eval(proof: Proof, facts: Map[String, Theorem] = Map.empty, ihses: Map[String, StructuralInductionHypotheses] = Map.empty): Attempt[Theorem] = {
      import scala.language.implicitConversions
      implicit def proofExpr2Expr(p: ProofExpr)(implicit ctx: Context): Expr = replaceFromSymbols(ctx.substs, p.e)
      implicit def seqProofExpr2SeqExpr(s: Seq[ProofExpr])(implicit ctx: Context): Seq[Expr] = s map proofExpr2Expr

      case class Context(substs: Map[Variable, Expr], facts: Map[String, Theorem], ihss: Map[String, StructuralInductionHypotheses]) {
        def withSubst(v: Variable, expr: Expr) = Context(substs + (v -> expr), facts, ihss)
        def withFact(id: String, thm: Theorem) = Context(substs, facts + (id -> thm), ihss)
        def withIhs(id: String, ihs: StructuralInductionHypotheses) = Context(substs, facts, ihss + (id -> ihs))

        def subst(v: Variable): Attempt[Expr] = findKey(substs, v)
        def fact(id: String): Attempt[Theorem] = findKey(facts, id)
        def ihs(id: String): Attempt[StructuralInductionHypotheses] = findKey(ihss, id)
      }

      def rec(proof: Proof)(implicit ctx: Context): Attempt[Theorem] = proof match {
        case ForallI(vs, body) => forallI(vs)(_ => rec(body))
        case AndI(trees) => Attempt.all(trees map rec) flatMap (andI(_))
        case ImplI(id, hyp, body) => implI(hyp)(h => rec(body)(ctx withFact (id, h)))

        case ForallE(tree, exprs) => rec(tree) flatMap (forallE(_, exprs))
        case LetAndE(tree, ids, body) => rec(tree) flatMap andE flatMap (thms =>
          rec(body)((ids zip thms).foldLeft(ctx)((ctx, kv) => ctx withFact (kv._1, kv._2))))
        case AndESelect(tree, idx) => (rec(tree) flatMap andE)(idx)
        case ImplE(tree, proof) => rec(tree) flatMap (implE(_)(goal => rec(proof) flatMap (goal.by(_))))

        case StructuralInduction(v, prop, ihsid, cases) =>
          structuralInduction(x => replaceFromSymbols(Map(v -> x), prop), v) {
            case (ihs, goal) => cases.find(_.id == ihs.constructor) match {
              case Some(c) => rec(c.body)((c.fields zip ihs.variables)
                .foldLeft(ctx withIhs (ihsid, ihs))((ctx, kv) => ctx withSubst (kv._1, kv._2)))
              case _ => Attempt.fail(s"Incomplete structural induction (no case for ${ihs.constructor})")
            }
          }
        case HypothesisApplication(ihsid, expr) => ctx ihs ihsid hypothesis expr //wow such readable

        case Fact(id) => ctx fact id
        case Let(id, v, in) => rec(v) flatMap (v => rec(in)(ctx withFact (id, v)))
        case Prove(expr, lemmas) => Attempt.all(lemmas map rec) flatMap (prove(expr, _))
      }

      rec(proof)(Context(Map.empty, facts, ihses))
    }

    def synthesize(proof: Proof): String = {
      import scala.language.postfixOps

      import scala.language.implicitConversions
      implicit def proofExpr2Expr(p: ProofExpr): Expr = p.e

      case class Context(indent: Int, inBlock: Boolean) {
        def indented = Context(indent + 1, false)
        def newBlock = Context(indent + 1, true)
        def noBlock = Context(indent, false)
      }

      def format(s: String)(implicit ctx: Context): String = {
        val lines = s.split("\n") map { line =>
          if (line.stripMargin != line) "  " * ctx.indent + line.stripMargin
          else line
        }

        lines.mkString("\n")
      }

      def lineSize(line: String): Int = (line split ("\n")).foldLeft(0)((acc, line) => Math.max(acc, line.size))

      def synthValDef(v: ValDef)(implicit ctx: Context): String = s""""${v.id.name}" :: ${v.tpe}"""

      def synthExpr(e: Expr)(implicit ctx: Context): String = e match {
        case Forall(vals, body) if vals.size <= 4 =>
          s"forall(${vals map synthValDef mkString ", "})((${vals map (_.id.name) mkString ", "}) => ${synthExpr(body)})"

        case _ => e.toString
      }

      def synthCase(c: Case)(implicit ctx: Context): String = {
        val fieldstr = if (c.fields.size > 0) ", " + (c.fields map (_.id.name) mkString (", ")) else ""
        s"""case C(`${c.id.name}`${fieldstr}) => ${rec(c.body)(ctx indented)}"""
      }

      def tryTurnIntoEqChain(p: Prove)(implicit ctx: Context): Attempt[String] = {
        sealed abstract class EqChain
        case class EqNode(expr: ProofExpr, jst: Proof, next: EqChain) extends EqChain
        case class EqLeaf(expr: ProofExpr) extends EqChain
        object EqExpr {
          def unapply(eq: EqChain): Option[ProofExpr] = eq match {
            case EqNode(expr, _, _) => Some(expr)
            case EqLeaf(expr) => Some(expr)
          }
        }

        def synthEqChain(chain: EqChain)(implicit ctx: Context): String = {
          def inner(chain: EqChain): (List[String], Int) = chain match {
            case EqNode(expr, jst, next @ EqExpr(nextExpr)) =>
              val exprstr = synthExpr(expr)(ctx noBlock)
              val jststr = if (jst == Prove(ProofExpr(Equals(expr, nextExpr)))) "trivial" else recNoBlock(jst)
              val localen = Math.max(lineSize(exprstr), lineSize(jststr))
              val (rest, globalen) = inner(next)
              (exprstr :: jststr :: rest, Math.max(localen, globalen))

            case EqLeaf(expr) =>
              val exprstr = synthExpr(expr)(ctx noBlock)
              (List(exprstr), exprstr.size)
          }

          val (strs, len) = inner(chain)

          if (strs.size == 1) strs.head
          else strs.zipWithIndex.map {
            case (str, idx) =>
              val pad = (" " * (len - str.size))
              if (idx == 0) str + pad + " ==|"
              else if (idx == strs.size - 1) "|" + str + pad
              else if (idx % 2 == 0) "|" + str + pad + " ==|"
              else "|  " + pad + str + " |"
          }.mkString("\n")
        }

        p match {
          case Prove(ProofExpr(toProve), Seq(p: Prove, _)) => p match {
            case Prove(ProofExpr(Equals(`toProve`, leaf)), Seq(next: Prove, jst)) =>
              def buildChain(p: Prove, sofar: EqChain, lastjst: Proof): Attempt[EqChain] = p match {
                case Prove(ProofExpr(Equals(`toProve`, expr)), Seq(next: Prove, jst)) =>
                  buildChain(next, EqNode(ProofExpr(expr), lastjst, sofar), jst)
                case Prove(ProofExpr(BooleanLiteral(true)), Seq()) => EqNode(ProofExpr(toProve), lastjst, sofar)
                case _ => Attempt.fail("Could not deduce EqChain")
              }

              buildChain(next, EqLeaf(ProofExpr(leaf)), jst) map synthEqChain

            case Prove(ProofExpr(BooleanLiteral(true)), Seq()) => "trivial"

            case _ => Attempt.fail("Could not deduce EqChain")
          }
          case _ => Attempt.fail("Could not deduce EqChain")
        }
      }

      object ForallIExtractor {
        def unapply(p: Proof): Option[(Seq[ValDef], Proof)] = p match {
          case f: ForallI =>
            def extractVarsAndBody(f: ForallI): (Seq[ValDef], Proof) = f match {
              case ForallI(vs, next: ForallI) => 
                val (vars, body) = extractVarsAndBody(next)
                (vs ++ vars, body)
              case ForallI(vs, body) => (vs, body)
            }
            Some(extractVarsAndBody(f))
            
          case _ => None
        }
      }

      def recIndented(proof: Proof)(implicit ctx: Context): String = rec(proof)(ctx indented)
      def recNewBlock(proof: Proof)(implicit ctx: Context): String = rec(proof)(ctx newBlock)
      def recNoBlock(proof: Proof)(implicit ctx: Context): String = rec(proof)(ctx noBlock)

      def rec(proof: Proof)(implicit ctx: Context): String = format(proof match {
        case ForallIExtractor(vs, body) =>
          s"""forallI(${vs map (synthValDef(_)(ctx noBlock)) mkString (", ")}) { case Seq(${vs map (_.id.name) mkString (", ")}) => 
          |  ${recNewBlock(body)}
          |}"""

        case AndI(trees) => s"""andI(${trees map recNoBlock mkString ", "})"""

        case ImplI(id, hyp, body) =>
          s"""implI(${synthExpr(hyp)(ctx noBlock)}) { $id =>
	      |  ${recNewBlock(body)}
	      |}"""

        case ForallE(tree, exprs) =>
          val exprstr = exprs map (synthExpr(_)(ctx noBlock))
          s"""forallE(${recNoBlock(tree)})(${exprstr.mkString(", ")})"""

        case LetAndE(tree, ids, body) =>
          if (ctx.inBlock)
            s"""val Seq(${ids mkString ", "}) = andE(${recNoBlock(tree)}) : Seq[Theorem]
            |${rec(body)}"""
          else
            s"""{
            |  val Seq(${ids mkString ", "}) = andE(${recNoBlock(tree)}) : Seq[Theorem]
            |  ${recNewBlock(body)}
            |}"""

        case AndESelect(tree, idx) => s"""andE(${recNoBlock(tree)})($idx)"""

        case ImplE(tree, proof) => s"""implE(${recNoBlock(tree)})(_.by(${recNoBlock(proof)}))"""

        case StructuralInduction(v, prop, ihs, cases) =>
          val newctx = ctx noBlock
          val casestr = (cases map (c => "|    " + synthCase(c)(newctx indented))) mkString ("\n")
          s"""structuralInduction((${v.id.name}: Expr) => ${synthExpr(prop)(newctx)}, ${synthValDef(v)(newctx)}) { case (${ihs}, goal) =>
          |  ${ihs}.expression match {
               ${casestr}
          |  }
          |}"""

        case HypothesisApplication(ihs, expr) => s"""${ihs}.hypothesis(${synthExpr(expr)(ctx noBlock)})"""

        case Fact(id) => id

        case Let(id, v, in) =>
          if (ctx.inBlock)
            s"""val $id = ${recIndented(v)}
            |${rec(in)}"""
          else
            s"""{
	        |  val $id = ${recIndented(v)}
	        |  ${recNewBlock(in)}
	        |}"""

        case p @ Prove(expr, lemmas) => tryTurnIntoEqChain(p) match {
          case Success(str) => str
          case _ =>
            val lemstr = if (lemmas.size > 0) ", " + ((lemmas map recNoBlock) mkString (", ")) else ""
            s"""prove(${synthExpr(expr)(ctx noBlock) + lemstr})"""
        }
      })

      rec(proof)(Context(0, true))
    }

  }
}