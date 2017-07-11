package ipw.ast

import ipw.AssistedTheory
import inox._
import inox.trees._
import inox.trees.dsl._

trait ProofTrees { self: AssistedTheory =>

  object AST {

    sealed abstract class Proof

    // Intro rules
    case class ForallI(v: ValDef, body: Proof) extends Proof
    case class ImplI(id: String, hyp: Expr, body: Proof) extends Proof
    case class AndI(trees: Seq[Proof]) extends Proof

    // Elim rules
    case class AndE(tree: Proof, ids: List[String], body: Proof) extends Proof

    // Induction

    // Others
    case class Fact(id: String) extends Proof
    case class Let(id: String, value: Proof, in: Proof) extends Proof

    def eval(proof: Proof): Attempt[Theorem] = {
      def findKey[T](map: Map[String, T], key: String): Attempt[T] = map get key match {
        case Some(v) => Success(v)
        case _ => Attempt.fail("not found")
      }

      case class Context(vals: Map[String, Variable], facts: Map[String, Theorem], ihss: Map[String, StructuralInductionHypotheses]) {
        def withVar(id: String, v: Variable) = Context(vals + (id -> v), facts, ihss)
        def withFact(id: String, thm: Theorem) = Context(vals, facts + (id -> thm), ihss)
        def withIhs(id: String, ihs: StructuralInductionHypotheses) = Context(vals, facts, ihss + (id -> ihs))

        def variable(id: String): Attempt[Variable] = findKey(vals, id)
        def fact(id: String): Attempt[Theorem] = findKey(facts, id)
        def ihs(id: String): Attempt[StructuralInductionHypotheses] = findKey(ihss, id)
      }

      def rec(proof: Proof)(implicit ctx: Context): Attempt[Theorem] = proof match {
        case ForallI(v, body) => forallI(v)(v => rec(body)(ctx withVar (v.id.name, v)))
        case ImplI(id, hyp, body) => implI(hyp)(h => rec(body)(ctx withFact (id, h)))
        case AndI(trees) => Attempt.all(trees map rec) flatMap (andI(_))

        case AndE(tree, ids, body) => rec(tree) flatMap (andE(_)) flatMap (thms =>
          rec(body)((ids zip thms).foldLeft(ctx)((ctx, keyval) => ctx withFact (keyval._1, keyval._2))))

        case Fact(id) => ctx fact id
        case Let(id, v, in) => rec(v) flatMap (v => rec(in)(ctx withFact (id, v)))
      }

      rec(proof)(Context(Map.empty, Map.empty, Map.empty))
    }

    def synthesize(proof: Proof): String = {
      def synthValDef(v: ValDef): String = s""""${v.id.name}" :: ${v.tpe}"""

      def synthExpr(e: Expr): String = e match {
        case Forall(vals, body) if vals.size <= 4 =>
          s"forall(${vals map synthValDef mkString ", "})((${vals map (_.id.name) mkString ", "}) => ${synthExpr(body)})"

        case _ => e.toString
      }

      def rec(proof: Proof): String = proof match {
        case ForallI(v, body) =>
          s"""forallI(${synthValDef(v)})(${v.id.name} => {
            ${rec(body)}
          })"""

        case ImplI(id, hyp, body) =>
          s"""implI(${synthExpr(hyp)})($id => {
	        ${rec(body)}
	      })"""

        case AndI(trees) => s"""andI(${trees map rec mkString ", "})"""

        case AndE(tree, ids, body) =>
          s"""{
            val Seq(${ids mkString ", "}) = andE(${rec(tree)}) : Seq[Theorem]
            ${rec(body)}
          }"""

        case Fact(id) => id

        case Let(id, v, in) =>
          s"""{
	        val $id = ${rec(v)}
	        ${rec(in)}
	      }"""
      }

      rec(proof)
    }

  }
}