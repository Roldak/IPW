package ipw.ast

import ipw.AssistedTheory
import ipw.ProofBuilder
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._

trait ProofEvaluators { theory: AssistedTheory with ProofBuilder =>
  import AST._
  import scala.language.implicitConversions
  private implicit def proofExpr2Expr(p: ProofExpr)(implicit ctx: Context): Expr = replaceFromSymbols(ctx.substs, p.e)
  private implicit def seqProofExpr2SeqExpr(s: Seq[ProofExpr])(implicit ctx: Context): Seq[Expr] = s map proofExpr2Expr

  private case class Context(substs: Map[Variable, Expr], facts: Map[String, Theorem], ihss: Map[String, StructuralInductionHypotheses]) {
    def withSubst(v: Variable, expr: Expr) = Context(substs + (v -> expr), facts, ihss)
    def withFact(id: String, thm: Theorem) = Context(substs, facts + (id -> thm), ihss)
    def withIhs(id: String, ihs: StructuralInductionHypotheses) = Context(substs, facts, ihss + (id -> ihs))

    def subst(v: Variable): Attempt[Expr] = findKey(substs, v)
    def fact(id: String): Attempt[Theorem] = findKey(facts, id)
    def ihs(id: String): Attempt[StructuralInductionHypotheses] = findKey(ihss, id)
  }

  private def findKey[K, T](map: Map[K, T], key: K): Attempt[T] = map get key match {
    case Some(v) => Success(v)
    case _ => Attempt.fail("not found")
  }

  private def rec(proof: Proof)(implicit ctx: Context): Attempt[Theorem] = proof match {
    case ForallI(vs, body) => forallI(vs)(_ => rec(body))
    case AndI(trees) => Attempt.all(trees map rec) flatMap (andI(_))
    case ImplI(id, hyp, body) => implI(hyp)(h => rec(body)(ctx withFact (id, h)))

    case ForallE(tree, exprs) => rec(tree) flatMap (forallE(_, exprs))
    case LetAndE(tree, ids, body) => rec(tree) flatMap andE flatMap (thms =>
      rec(body)((ids zip thms).foldLeft(ctx)((ctx, kv) => ctx withFact (kv._1, kv._2))))
    case AndESelect(tree, idx) => (rec(tree) flatMap andE)(idx)
    case ImplE(tree, proof) => rec(tree) flatMap (implE(_)(goal => rec(proof) flatMap (goal.by(_))))

    case AST.StructuralInduction(v, prop, ihsid, cases) =>
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

  def evalProof(proof: Proof, facts: Map[String, Theorem] = Map.empty, ihses: Map[String, StructuralInductionHypotheses] = Map.empty): Attempt[Theorem] =
    rec(proof)(Context(Map.empty, facts, ihses))
}