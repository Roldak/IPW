package ipw

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._
import welder._

trait GenericRuleProvider { self: AssistedTheory =>
  
  type RuleResult
  
  /*
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
   */
  
  def toTheorem(t: Attempt[RuleResult]): Attempt[Theorem]
  
  def forallIGen(v: ValDef)(f: Variable => Attempt[RuleResult]): Attempt[RuleResult]
  def forallEGen(b: RuleResult, exprs: Seq[Expr]): Attempt[RuleResult]
  def proveGen(expr: Expr): Attempt[RuleResult]
}

trait TheoremBuilder extends GenericRuleProvider { self: AssistedTheory => 
  override type RuleResult = Theorem
  
  override def toTheorem(t: Attempt[Theorem]) = t
  
  override def forallIGen(vd: ValDef)(f: Variable => Attempt[Theorem]): Attempt[Theorem] = forallI(vd)(f)
  override def forallEGen(thm: Theorem, exprs: Seq[Expr]): Attempt[Theorem] = forallE(thm, exprs)
  override def proveGen(expr: Expr): Attempt[Theorem] = prove(expr)
}

trait ProofBuilder extends GenericRuleProvider { self: AssistedTheory =>
  import AST.ProofExprImplicits._
  
  override type RuleResult = AST.Proof
  
  override def toTheorem(p: Attempt[AST.Proof]): Attempt[Theorem] = p flatMap (AST.eval(_))
  
  override def forallIGen(vd: ValDef)(f: Variable => Attempt[AST.Proof]): Attempt[AST.Proof] = f(vd.toVariable) flatMap (AST.ForallI(vd, _))
  override def forallEGen(p: AST.Proof, exprs: Seq[Expr]): Attempt[AST.Proof] = AST.ForallE(p, exprs)
  override def proveGen(expr: Expr): Attempt[AST.Proof] = AST.Prove(expr)
}