package ipw.ast

import ipw.AssistedTheory
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._

trait ProofTrees { self: AssistedTheory =>

  object AST {

    class ProofExpr(val e: Expr)
    object ProofExprImplicits {
      import scala.language.implicitConversions
      implicit def expr2ProofExpr(e: Expr): ProofExpr = new ProofExpr(e)
      implicit def exprSeq2ProofExprSeq(s: Seq[Expr]): Seq[ProofExpr] = s map expr2ProofExpr
    }

    sealed abstract class Proof

    // Intro rules
    case class ForallI(v: ValDef, body: Proof) extends Proof
    case class ImplI(id: String, hyp: ProofExpr, body: Proof) extends Proof
    case class AndI(trees: Seq[Proof]) extends Proof

    // Elim rules
    case class ForallE(tree: Proof, exprs: Seq[ProofExpr]) extends Proof
    case class LetAndE(tree: Proof, ids: List[String], body: Proof) extends Proof
    case class ImplE(tree: Proof, proof: Proof) extends Proof

    // Induction

    case class Case(id: Identifier, fields: Seq[ValDef], body: Proof)
    case class StructuralInduction(v: ValDef, prop: ProofExpr, ihs: String, cases: Seq[Case]) extends Proof
    case class HypothesisApplication(ihs: String, expr: ProofExpr) extends Proof

    // Others
    case class Fact(id: String) extends Proof
    case class Let(id: String, value: Proof, in: Proof) extends Proof
    case class Prove(expr: ProofExpr, facts: Seq[Proof] = Nil) extends Proof

    // Chains
    sealed abstract class EqChain extends Proof
    case class EqNode(expr: ProofExpr, jst: Proof, next: EqChain) extends EqChain
    case class EqLeaf(expr: ProofExpr) extends EqChain
    
    def eval(proof: Proof, facts: Map[String, Theorem] = Map.empty, ihses: Map[String, StructuralInductionHypotheses] = Map.empty): Attempt[Theorem] = {
      import scala.language.implicitConversions
      implicit def proofExpr2Expr(p: ProofExpr)(implicit ctx: Context): Expr = replaceFromSymbols(ctx.substs, p.e)
      implicit def seqProofExpr2SeqExpr(s: Seq[ProofExpr])(implicit ctx: Context): Seq[Expr] = s map proofExpr2Expr

      def findKey[K, T](map: Map[K, T], key: K): Attempt[T] = map get key match {
        case Some(v) => Success(v)
        case _ => Attempt.fail("not found")
      }

      def evalEqChain(node: EqNode)(implicit ctx: Context): (Attempt[Theorem], Expr) = node.next match {
        case next: EqNode =>
          val localthm = prove((node.expr: Expr) === next.expr, rec(node.jst))
          val (restthm, last) = evalEqChain(next)
          (prove((node.expr: Expr) === last, localthm, restthm), last)

        case EqLeaf(last) =>
          (prove((node.expr: Expr) === last, rec(node.jst)), last)
      }

      case class Context(substs: Map[Variable, Expr], facts: Map[String, Theorem], ihss: Map[String, StructuralInductionHypotheses]) {
        def withSubst(v: Variable, expr: Expr) = Context(substs + (v -> expr), facts, ihss)
        def withFact(id: String, thm: Theorem) = Context(substs, facts + (id -> thm), ihss)
        def withIhs(id: String, ihs: StructuralInductionHypotheses) = Context(substs, facts, ihss + (id -> ihs))

        def subst(v: Variable): Attempt[Expr] = findKey(substs, v)
        def fact(id: String): Attempt[Theorem] = findKey(facts, id)
        def ihs(id: String): Attempt[StructuralInductionHypotheses] = findKey(ihss, id)
      }

      def rec(proof: Proof)(implicit ctx: Context): Attempt[Theorem] = proof match {
        case ForallI(v, body) => forallI(v)(_ => rec(body))
        case ImplI(id, hyp, body) => implI(hyp)(h => rec(body)(ctx withFact (id, h)))
        case AndI(trees) => Attempt.all(trees map rec) flatMap (andI(_))

        case ForallE(tree, exprs) => rec(tree) flatMap (forallE(_, exprs))
        case LetAndE(tree, ids, body) => rec(tree) flatMap andE flatMap (thms =>
          rec(body)((ids zip thms).foldLeft(ctx)((ctx, kv) => ctx withFact (kv._1, kv._2))))
        case ImplE(tree, proof) => rec(tree) flatMap (implE(_)(goal => rec(proof) flatMap (goal.by(_))))

        case StructuralInduction(v, prop, ihsid, cases) =>
          structuralInduction(x => replaceFromSymbols(Map(v -> x), prop), v) {
            case (ihs, goal) =>
              val Some((caseId, exprs)) = C.unapplySeq(ihs.expression)
              cases.find(_.id == caseId) match {
                case Some(c) => rec(c.body)((c.fields zip exprs)
                  .foldLeft(ctx withIhs (ihsid, ihs))((ctx, kv) => ctx withSubst (kv._1.toVariable, kv._2)))
                case _ => Attempt.fail(s"Incomplete structural induction (no case for ${caseId})")
              }
          }
        case HypothesisApplication(ihsid, expr) => ctx ihs ihsid hypothesis expr //wow such readable

        case Fact(id) => ctx fact id
        case Let(id, v, in) => rec(v) flatMap (v => rec(in)(ctx withFact (id, v)))
        case Prove(expr, lemmas) => Attempt.all(lemmas map rec) flatMap (prove(expr, _))

        case n: EqNode => evalEqChain(n)._1
        case EqLeaf(_) => Attempt.fail("Invalid equality chain")
      }

      rec(proof)(Context(Map.empty, Map.empty, Map.empty))
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

      def synthEqChain(chain: EqChain)(implicit ctx: Context): String = {
        def inner(chain: EqChain): (List[String], Int) = chain match {
          case EqNode(expr, jst, next) =>
            val exprstr = synthExpr(expr)(ctx noBlock)
            val jststr = recNoBlock(jst)
            val localen = Math.max(exprstr.size, jststr.size)
            val (rest, globalen) = inner(next)
            (exprstr :: jststr :: rest, Math.max(localen, globalen))

          case EqLeaf(expr) =>
            val exprstr = synthExpr(expr)(ctx noBlock)
            (List(exprstr), exprstr.size)
        }

        val (strs, len) = inner(chain)
        strs.zipWithIndex.map {
          case (str, idx) =>
            val pad = (" " * (len - str.size))
            if (idx == 0) str + pad + " ==|"
            else if (idx == strs.size - 1) "|" + str + pad
            else if (idx % 2 == 0) "|" + str + pad + " ==|"
            else "|  " + pad + str + " |"
        }.mkString("\n")
      }

      def recIndented(proof: Proof)(implicit ctx: Context): String = rec(proof)(ctx indented)
      def recNewBlock(proof: Proof)(implicit ctx: Context): String = rec(proof)(ctx newBlock)
      def recNoBlock(proof: Proof)(implicit ctx: Context): String = rec(proof)(ctx noBlock)

      def rec(proof: Proof)(implicit ctx: Context): String = format(proof match {
        case ForallI(v, body) =>
          s"""forallI(${synthValDef(v)(ctx noBlock)}) { ${v.id.name} => 
          |  ${recNewBlock(body)}
          |}"""

        case ImplI(id, hyp, body) =>
          s"""implI(${synthExpr(hyp)(ctx noBlock)}) { $id =>
	      |  ${recNewBlock(body)}
	      |}"""

        case AndI(trees) => s"""andI(${trees map recNoBlock mkString ", "})"""

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

        case Prove(expr, lemmas) =>
          val lemstr = if (lemmas.size > 0) ", " + ((lemmas map recNoBlock) mkString (", ")) else ""
          s"""prove(${synthExpr(expr)(ctx noBlock) + lemstr})"""

        case chain: EqChain => synthEqChain(chain)
      })

      rec(proof)(Context(0, true))
    }

  }
}