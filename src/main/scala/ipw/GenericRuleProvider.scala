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

  protected[GenericRuleProvider] def allCases(tpe: ADTType): Seq[(ADT, Seq[Variable], Identifier)] = {
    // taken from Welder
    val constructors = tpe.getADT match {
      case sort: TypedADTSort => sort.constructors
      case cons: TypedADTConstructor => Seq(cons)
    }

    constructors map { (constructor: TypedADTConstructor) =>
      val variables = constructor.fields map { (field: ValDef) =>
        val name = field.toVariable.id.name
        Variable.fresh(name, field.tpe)
      }

      val expr = ADT(constructor.toType, variables)

      (expr, variables, constructor.definition.id)
    }
  }

  def eval(t: Attempt[RuleResult], thms: Map[String, Theorem] = Map.empty): Attempt[Theorem]

  // introduction rules
  def forallIGen(v: ValDef)(f: Variable => Attempt[RuleResult]): Attempt[RuleResult]
  def andIGen(xs: Seq[RuleResult]): RuleResult
  def implIGen(name: String, prem: Expr)(concl: RuleResult => Attempt[RuleResult]): Attempt[RuleResult]

  // elimination rules
  def forallEGen(x: RuleResult, exprs: Seq[Expr]): Attempt[RuleResult]
  def andEGen(x: RuleResult, ids: Seq[String])(f: Seq[RuleResult] => Attempt[RuleResult]): Attempt[RuleResult]
  def implEGen(x: RuleResult, proof: RuleResult): Attempt[RuleResult]

  // structural induction

  def structuralInductionGen(v: ValDef, prop: Expr => Expr, ihs: String)
    (f: (String, Expr => Attempt[RuleResult], Expr, Seq[Variable]) => Attempt[RuleResult]): Attempt[RuleResult]

  // others
  def proveGen(expr: Expr, facts: Seq[RuleResult]): Attempt[RuleResult]
}

trait TheoremBuilder extends GenericRuleProvider { self: AssistedTheory =>
  override type RuleResult = Theorem

  override def eval(t: Attempt[Theorem], thms: Map[String, Theorem] = Map.empty): Attempt[Theorem] = t

  // introduction rules
  override def forallIGen(vd: ValDef)(f: Variable => Attempt[Theorem]): Attempt[Theorem] = forallI(vd)(f)
  override def andIGen(thms: Seq[Theorem]): Theorem = andI(thms)
  override def implIGen(name: String, prem: Expr)(concl: Theorem => Attempt[Theorem]): Attempt[Theorem] = implI(prem)(concl)

  // elimination rules
  override def forallEGen(thm: Theorem, exprs: Seq[Expr]): Attempt[Theorem] = forallE(thm, exprs)
  override def andEGen(thm: Theorem, ids: Seq[String])(f: Seq[Theorem] => Attempt[Theorem]): Attempt[Theorem] = andE(thm) flatMap f
  override def implEGen(thm: Theorem, proof: Theorem): Attempt[Theorem] = implE(thm)(_.by(proof))

  // structural induction

  override def structuralInductionGen(v: ValDef, prop: Expr => Expr, ihs: String)
  	(f: (String, Expr => Attempt[Theorem], Expr, Seq[Variable]) => Attempt[Theorem]): Attempt[Theorem] = structuralInduction(prop, v) {
    case (ihs, goal) => f(ihs.constructor.name, ihs.hypothesis, ihs.expression, ihs.variables)
  }

  // others
  override def proveGen(expr: Expr, facts: Seq[Theorem]): Attempt[Theorem] = prove(expr, facts)
}

trait ProofBuilder extends GenericRuleProvider { self: AssistedTheory =>
  import AST.ProofExprImplicits._

  override type RuleResult = AST.Proof

  override def eval(p: Attempt[AST.Proof], thms: Map[String, Theorem] = Map.empty): Attempt[Theorem] = p flatMap (AST.eval(_, thms))

  // introduction rules
  override def forallIGen(vd: ValDef)(f: Variable => Attempt[AST.Proof]): Attempt[AST.Proof] = f(vd.toVariable) flatMap (AST.ForallI(vd, _))
  override def andIGen(ps: Seq[AST.Proof]): AST.Proof = AST.AndI(ps)
  override def implIGen(name: String, prem: Expr)(concl: AST.Proof => Attempt[AST.Proof]): Attempt[AST.Proof] =
    AST.ImplI(name, prem, concl(AST.Fact(name)))

  // elimination rules
  override def forallEGen(p: AST.Proof, exprs: Seq[Expr]): Attempt[AST.Proof] = AST.ForallE(p, exprs)
  override def andEGen(p: AST.Proof, ids: Seq[String])(f: Seq[AST.Proof] => Attempt[AST.Proof]): Attempt[AST.Proof] =
    AST.LetAndE(p, ids, f(ids map (AST.Fact(_))))
  override def implEGen(p: AST.Proof, proof: AST.Proof): Attempt[AST.Proof] = AST.ImplE(p, proof)

  // structural induction

  def structuralInductionGen(v: ValDef, prop: Expr => Expr, ihs: String)
    (f: (String, Expr => Attempt[AST.Proof], Expr, Seq[Variable]) => Attempt[AST.Proof]): Attempt[AST.Proof] = {
    val cases = allCases(v.tpe.asInstanceOf[ADTType]) map {
      case (adt, vars, id) => AST.Case(id, vars, f(id.name, AST.HypothesisApplication(ihs, _), adt, vars))
    }

    AST.StructuralInduction(v, prop(v.toVariable), ihs, cases)
  }

  // others
  override def proveGen(expr: Expr, facts: Seq[AST.Proof]): Attempt[AST.Proof] = AST.Prove(expr, facts)
}