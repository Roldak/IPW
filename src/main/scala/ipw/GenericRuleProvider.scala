package ipw

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._
import ipw.ast.ProofTrees
import welder._

trait GenericRuleProvider { self: AssistedTheory =>

  type RuleResult
  case class StructuralInductionHypothesis(constr: Identifier, expr: Expr, hyp: Expr => Attempt[RuleResult], vars: Seq[Variable])

  implicit class RuleResultOps(val r: RuleResult) {
    def expression: Expr = self.expression(r)
  }

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

  def eval(t: Attempt[RuleResult], thms: Map[String, Theorem], ihses: Map[String, StructuralInductionHypotheses]): Attempt[Theorem]
  def expression(t: RuleResult): Expr

  // introduction rules
  def forallIGen(v: ValDef)(f: Variable => Attempt[RuleResult]): Attempt[RuleResult] = forallIGen(Seq(v)) { case Seq(v) => f(v) }
  def forallIGen(vs: Seq[ValDef])(f: Seq[Variable] => Attempt[RuleResult]): Attempt[RuleResult]
  def andIGen(xs: Seq[RuleResult]): RuleResult
  def implIGen(name: String, prem: Expr)(concl: (String, RuleResult) => Attempt[RuleResult]): Attempt[RuleResult]

  // elimination rules
  def forallEGen(x: RuleResult, exprs: Seq[Expr]): Attempt[RuleResult]
  def andEGen(x: RuleResult, ids: Seq[String])(f: Seq[(String, RuleResult)] => Attempt[RuleResult]): Attempt[RuleResult]
  def andEGenSelect(x: RuleResult, i: Int): Attempt[RuleResult]
  def implEGen(x: RuleResult, proof: RuleResult): Attempt[RuleResult]

  // structural induction

  def structuralInductionGen(v: ValDef, prop: Expr => Expr, ihs: String)(f: (StructuralInductionHypothesis, Expr) => Attempt[RuleResult]): Attempt[RuleResult]

  // others
  def proveGen(expr: Expr, facts: Seq[RuleResult] = Nil): Attempt[RuleResult]

  def truthGen = proveGen(E(true))
}

trait TheoremBuilder extends GenericRuleProvider { self: AssistedTheory =>
  override type RuleResult = Theorem

  override def eval(t: Attempt[Theorem], thms: Map[String, Theorem], ihses: Map[String, StructuralInductionHypotheses]): Attempt[Theorem] = t
  override def expression(t: Theorem): Expr = t.expression

  // introduction rules
  override def forallIGen(vs: Seq[ValDef])(f: Seq[Variable] => Attempt[Theorem]): Attempt[Theorem] = forallI(vs)(f)
  override def andIGen(thms: Seq[Theorem]): Theorem = andI(thms)
  override def implIGen(name: String, prem: Expr)(concl: (String, Theorem) => Attempt[Theorem]): Attempt[Theorem] = implI(prem)(concl(name, _))

  // elimination rules
  override def forallEGen(thm: Theorem, exprs: Seq[Expr]): Attempt[Theorem] = forallE(thm, exprs)
  override def andEGen(thm: Theorem, ids: Seq[String])(f: Seq[(String, Theorem)] => Attempt[Theorem]): Attempt[Theorem] =
    andE(thm) map (ids zip _) flatMap f
  override def andEGenSelect(x: Theorem, i: Int): Attempt[RuleResult] = andE(x) flatMap (_ match {
    case thms if thms.size > i => Success(thms(i))
    case _ => Attempt.fail("Out of bounds")
  })
  override def implEGen(thm: Theorem, proof: Theorem): Attempt[Theorem] = implE(thm)(_.by(proof))

  // structural induction

  override def structuralInductionGen(v: ValDef, prop: Expr => Expr, ihs: String)(f: (StructuralInductionHypothesis, Expr) => Attempt[Theorem]): Attempt[Theorem] = structuralInduction(prop, v) {
    case (ihs, goal) => f(StructuralInductionHypothesis(ihs.constructor, ihs.expression, ihs.hypothesis, ihs.variables), goal.expression)
  }

  // others
  override def proveGen(expr: Expr, facts: Seq[Theorem]): Attempt[Theorem] = prove(expr, facts)
}

trait ProofBuilder extends GenericRuleProvider with ProofTrees { self: AssistedTheory =>
  import AST.ProofExprImplicits._

  override type RuleResult = (AST.Proof, Expr)

  override def eval(p: Attempt[RuleResult], thms: Map[String, Theorem], ihses: Map[String, StructuralInductionHypotheses]): Attempt[Theorem] =
    p flatMap { case (proof, _) => AST.eval(proof, thms, ihses) }
  override def expression(p: RuleResult): Expr = p._2

  // introduction rules
  override def forallIGen(vs: Seq[ValDef])(f: Seq[Variable] => Attempt[RuleResult]): Attempt[RuleResult] =
    f(vs map (_.toVariable)) flatMap { case (proof, expr) => (AST.ForallI(vs, proof), Forall(vs, expr)) }

  override def andIGen(ps: Seq[RuleResult]): RuleResult = (AST.AndI(ps map (_._1)), And(ps map (_._2)))

  override def implIGen(name: String, prem: Expr)(concl: (String, RuleResult) => Attempt[RuleResult]): Attempt[RuleResult] =
    concl(name, (AST.Fact(name), prem)) flatMap { case (proof, expr) => (AST.ImplI(name, prem, proof), Implies(prem, expr)) }

  // elimination rules
  override def forallEGen(p: RuleResult, exprs: Seq[Expr]): Attempt[RuleResult] = p._2 match {
    case Forall(params, e) if exprs.size == params.size => (AST.ForallE(p._1, exprs), replaceFromSymbols((params zip exprs).toMap, e))
  }

  override def andEGen(p: RuleResult, ids: Seq[String])(f: Seq[(String, RuleResult)] => Attempt[RuleResult]): Attempt[RuleResult] = p._2 match {
    case And(exprs) if ids.size == exprs.size =>
      f((ids zip exprs) map { case (id, e) => (id, (AST.Fact(id), e)) }) flatMap { case (proof, expr) => (AST.LetAndE(p._1, ids, proof), expr) }
  }
  
  override def andEGenSelect(p: RuleResult, i: Int): Attempt[RuleResult] = p._2 match {
    case And(exprs) if exprs.size > i => (AST.AndESelect(p._1, i), exprs(i))
  }
  
  override def implEGen(p: RuleResult, proof: RuleResult): Attempt[RuleResult] = p._2 match {
    case Implies(prem, concl) => (AST.ImplE(p._1, proof._1), concl)
  }

  // structural induction

  override def structuralInductionGen(v: ValDef, prop: Expr => Expr, ihs: String)(f: (StructuralInductionHypothesis, Expr) => Attempt[RuleResult]): Attempt[RuleResult] = {
    val cases = allCases(v.tpe.asInstanceOf[ADTType]) map {
      case (adt, vars, id) =>
        AST.Case(id, vars, f(StructuralInductionHypothesis(id, adt, e => (AST.HypothesisApplication(ihs, e), prop(e)), vars), prop(adt))._1)
    }

    (AST.StructuralInduction(v, prop(v.toVariable), ihs, cases), Forall(Seq(v), prop(v.toVariable)))
  }

  // others
  override def proveGen(expr: Expr, facts: Seq[RuleResult]): Attempt[RuleResult] = (AST.Prove(expr, facts map (_._1)), expr)
}