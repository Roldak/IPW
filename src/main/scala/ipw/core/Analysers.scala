package ipw.core

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._
import welder._
import ipw.AssistedTheory
import inox.ast.TreeDeconstructor
import inox.ast.TreeExtractor
import ipw.eval.PartialEvaluator
import inox.evaluators.EvaluationResults._

private object Utils {
  implicit class BoolToOption(val self: Boolean) extends AnyVal {
    def toOption[A](value: => A): Option[A] = if (self) Some(value) else None
  }

  def asADTType(tpe: Type): Option[ADTType] = tpe match {
    case t: ADTType => Some(t)
    case _          => None
  }
}

trait Analysers { theory: AssistedTheory =>
  private implicit class IHUtils(hyp: StructuralInductionHypotheses) {
    lazy val variablesSet = hyp.variables.toSet

    private def isInnerOrSelf(inner: Expr): Boolean = inner == hyp.expression || isInner(inner)

    def isInner(inner: Expr): Boolean = inner match {
      case v: Variable           => variablesSet.contains(v)
      case ADTSelector(adt, _)   => isInnerOrSelf(adt)
      case TupleSelect(tuple, _) => isInnerOrSelf(tuple)
      case MapApply(map, _)      => isInnerOrSelf(map)
      case _                     => false
    }
  }

  private sealed abstract class Path
  private case class NotE(next: Path) extends Path
  private case class AndE(clauseIndex: Int, next: Path) extends Path
  private case class ForallE(vals: Seq[ValDef], next: Path) extends Path
  private case class ImplE(assumption: Expr, next: Path) extends Path
  private case object EndOfPath extends Path

  private case class Conclusion(expr: Expr, freeVars: Set[Variable], path: Path) {
    def notE = Conclusion(expr, freeVars, NotE(path))
    def andE(index: Int) = Conclusion(expr, freeVars, AndE(index, path))
    def forallE(vals: Seq[ValDef]) = Conclusion(expr, freeVars ++ vals.map(_.toVariable), ForallE(vals, path))
    def implE(assumption: Expr) = Conclusion(expr, freeVars, ImplE(assumption, path))
  }

  /**
   * Generates all the conclusions of an expression (normally coming from a theorem)
   * Basically conclusions of a given theorem are all the theorems that you could possibly generate from the 
   * initial theorem (expression) by applying elimination rules, such as forallE, implE, etc.
   * 
   * Example: 
   * input:  Vx. Vy. f(x) => (g(y) && Vz. h(z))
   * output: [
   * 	Vx. Vy. f(x) => (g(y) && Vz. h(z)) 		(no rules applied)
   *  Vy. f(x) => (g(y) && Vz. h(z)) 				(forallE(x))
   *  f(x) => (g(y) && Vz. h(z)) 						(forallE(x), forallE(y))
   *  g(y) && Vz. h(z) 											(forallE(x), forallE(y), implE(f(x)))
   *  g(y) 																	(forallE(x), forallE(y), implE(f(x)), andE(0))
   *  Vz. h(z) 															(forallE(x), forallE(y), implE(f(x)), andE(1))
   *  h(z)																	(forallE(x), forallE(y), implE(f(x)), andE(1), forallE(z))
   * ]
   */
  private def conclusionsOf(thm: Expr): Seq[Conclusion] = {
    val paths = thm match {
      case Not(Not(e)) =>
        conclusionsOf(e) map (_.notE)

      case And(exprs) =>
        exprs.zipWithIndex flatMap { case (e, i) => conclusionsOf(e) map (_.andE(i)) }

      case Forall(vals, body) =>
        conclusionsOf(body) map (_.forallE(vals))

      case Implies(assumption, rhs) =>
        conclusionsOf(rhs) map (_.implE(assumption))

      case _ => Nil
    }

    paths :+ Conclusion(thm, Set.empty, EndOfPath)
  }

  /**
   * Collect function calls in the expression and generates suggestion for expanding them (using partial evaluation)
   */
  private def collectInvocations(e: Expr): Seq[NamedSuggestion] = functionCallsOf(e).map { inv =>
    def result(): (Expr, Theorem) = PartialEvaluator.default(program, Some(inv)).eval(e) match {
      case Successful(ev) => (ev, prove(e === ev))
      case _              => (e, truth)
    }
    (s"Expand invocation of '${inv.id}'", RewriteSuggestion(inv, RewriteResult(result)))
  }.toSeq

  /**
   * Finds expressions which can be applied to the inductive hypothesis in order to generate a new theorem.
   */
  private def findInductiveHypothesisApplication(e: Expr, ihs: Seq[StructuralInductionHypotheses]): Map[String, Theorem] = {
    val ihset = ihs.toSet
    val thms = collect[(String, Theorem)] { e: Expr =>
      ihset.flatMap { ihs =>
        if (ihs.isInner(e)) {
          ihs.hypothesis(e) match {
            case Success(thm) => Set((s"IH on `$e`", thm))
            case Failure(_)   => Set.empty[(String, Theorem)]
          }
        } else Set.empty[(String, Theorem)]
      }
    }(e)

    thms.toMap
  }

  /**
   * Unifies the pattern with the expression, where instantiableVars denotes the set of variables appearing in the pattern that are instantiable.
   */
  private def unify(expr: Expr, pattern: Expr, instantiableVars: Set[Variable]): Option[Map[Variable, Expr]] = (expr, pattern) match {
    case (ev: Variable, pv: Variable) if ev == pv => Some(Map.empty)

    case (expr, pv: Variable) =>
      if (instantiableVars(pv) && expr.getType == pv.tpe) Some(Map(pv -> expr))
      else None

    case (expr, pattern) if expr.getClass == pattern.getClass =>
      val (evars, eexprs, etypes, ebuilder) = deconstructor.deconstruct(expr)
      val (pvars, pexprs, ptypes, pbuilder) = deconstructor.deconstruct(pattern)

      if (evars.size == pvars.size &&
        eexprs.size == pexprs.size &&
        etypes == ptypes &&
        evars.map(_.tpe) == pvars.map(_.tpe) &&
        pbuilder(evars, eexprs, etypes) == expr) {

        val substs = pvars.zip(evars).toMap
        val subPexprs = pexprs.map(pexpr => replaceFromSymbols(substs, pexpr))

        eexprs.zip(subPexprs).foldLeft[(Option[Map[Variable, Expr]], Set[Variable])]((Some(Map.empty), instantiableVars)) {
          case ((Some(subst), instantiable), (eexpr, pexpr)) =>
            unify(eexpr, pexpr, instantiable) match {
              case Some(stepSubst) => (Some(subst ++ stepSubst), instantiable -- stepSubst.map(_._1))
              case _               => (None, instantiable)
            }
          case _ => (None, Set.empty)
        }._1
      } else
        None
    case _ => None
  }

  import scala.language.implicitConversions

  private implicit def attemptToOption[T](x: Attempt[T]): Option[T] = x match {
    case Success(v) => Some(v)
    case _          => None
  }

  private object TheoremWithExpression {
    def unapply(thm: Theorem): Option[(Theorem, Expr)] = Some((thm, thm.expression))
  }

  /**
   * Generates a new theorem from a given theorem by following elimination rules given by the path,
   * with the help of a substitution to instantiate foralls.
   */
  private def followPath(thm: Theorem, path: Path, subst: Map[Variable, Expr]): Option[Theorem] = path match {
    case NotE(next)              => followPath(notE(thm), next, subst)
    case AndE(i, next)           => followPath(andE(thm)(i), next, subst)
    case ForallE(vals, next)     => followPath(forallE(thm)(subst(vals.head.toVariable), (vals.tail map (v => subst(v.toVariable)): _*)), next, subst)
    case ImplE(assumption, next) => ???
    case EndOfPath               => Some(thm)
  }
  
  /**
   * Free variables are generally all instantiated by unifying the pattern of the conclusion with the subject expression.
   * However, sometimes this is not enough, as some quantified variables can not appear in the pattern:
   *  - If doesn't appear at all in the formula (then instantiate it with any value)
   *  - If it appears in a premise of an implication
   */
  private def instantiateFreeVariables(freeVars: Set[Variable], exp: Expr, pattern: Expr, path: Path): Option[Map[Variable, Expr]] = {
    unify(exp, pattern, freeVars)
  }

  /**
   * Given a root expression expr and a root theorem thm,
   * tries to find subexpressions inside expr where some conclusion of thm could be applied. 
   */
  private def instantiateConclusion(expr: Expr, thm: Theorem): Seq[(Expr, Expr, Theorem)] = {
    val concls = conclusionsOf(thm.expression) flatMap (_ match {
      case concl @ Conclusion(Equals(a, b), vars, path) => Seq(
        (a, (x: Equals) => x.lhs, (x: Equals) => x.rhs, vars, path),
        (b, (x: Equals) => x.rhs, (x: Equals) => x.lhs, vars, path))
      case _ => Nil
    })

    collectPreorderWithPath { (exp, exPath) =>
      concls flatMap {
        case (pattern, from, to, freeVars, path) =>
          instantiateFreeVariables(freeVars, exp, pattern, path) match {
            case Some(subst) => followPath(thm, path, subst).map {
              case TheoremWithExpression(thm, eq @ Equals(_, _)) => (from(eq), replaceTreeWithPath(expr, exPath, to(eq)), thm)
            }.toSeq
            case _ => Nil
          }
      }
    }(expr).groupBy(x => (x._1, x._2)).map(_._2.head).toSeq
  }

  /**
   * Given a root expression expr and a collection of theorems thms,
   * finds all possible applications of any theorem in thms on any subexpression of expr
   */
  private def findTheoremApplications(expr: Expr, thms: Map[String, Theorem]): Seq[NamedSuggestion] = {
    thms.toSeq flatMap {
      case (name, thm) =>
        if (name == "lemma") {
          println("loule")
        }
        instantiateConclusion(expr, thm) map { case (subj, res, proof) => (s"Apply theorem $name", RewriteSuggestion(subj, RewriteResult(res, proof))) }
    }
  }

  /**
   * Generates all suggestions by analyzing the given root expression and the theorems/IHS that are available.
   */
  protected[ipw] def analyse(e: Expr, thms: Map[String, Theorem], ihs: Seq[StructuralInductionHypotheses]): (Seq[NamedSuggestion], Map[String, Theorem]) = {
    val findInduct = findInductiveHypothesisApplication(e, ihs)
    val newThms = thms ++ findInduct
    (collectInvocations(e) ++ findTheoremApplications(e, newThms), newThms)
  }

  /**
   * Generates suggestions to eliminate a forall. 
   * (Either fix the variable, or if its type is inductive, suggest structural induction)
   */
  protected[ipw] def analyseForall(v: ValDef, body: Expr): Seq[NamedSuggestion] = {
    import Utils._

    val structInd = asADTType(v.tpe)
      .flatMap(_.lookupADT.flatMap(_.definition.isInductive.toOption(Seq((s"Structural induction on '${v.id}'", StructuralInduction))))) // sorry
      .getOrElse(Nil)

    structInd :+ (s"Fix variable '${v.id}'", FixVariable)
  }
}