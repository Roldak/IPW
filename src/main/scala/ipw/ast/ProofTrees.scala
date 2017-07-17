package ipw.ast

import ipw.AssistedTheory
import ipw.ProofBuilder
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._

trait ProofTrees 
	extends ProofEvaluators 
	with ProofSynthetizers { self: AssistedTheory with ProofBuilder =>
	  
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
    
  }
}