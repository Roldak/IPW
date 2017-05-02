package ipw.core

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._
import welder._
import ipw.AssistedTheory
import inox.ast.TreeDeconstructor
import inox.ast.TreeExtractor

trait Analysers { theory: AssistedTheory =>
  implicit class IHUtils(hyp: StructuralInductionHypotheses) {
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

  sealed abstract class Path
  case class NotE(next: Path) extends Path
  case class AndE(clauseIndex: Int, next: Path) extends Path
  case class ForallE(vals: Seq[ValDef], next: Path) extends Path
  case class ImplE(assumption: Expr, next: Path) extends Path
  case object EndOfPath extends Path

  case class Conclusion(expr: Expr, freeVars: Set[Variable], path: Path) {
    def notE = Conclusion(expr, freeVars, NotE(path))
    def andE(index: Int) = Conclusion(expr, freeVars, AndE(index, path))
    def forallE(vals: Seq[ValDef]) = Conclusion(expr, freeVars ++ vals.map(_.toVariable), ForallE(vals, path))
    def implE(assumption: Expr) = Conclusion(expr, freeVars, ImplE(assumption, path))
  }

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

      case _ => Seq()
    }

    paths :+ Conclusion(thm, Set.empty, EndOfPath)
  }

  private def collectInvocations(e: Expr): Seq[Suggestion] = functionCallsOf(e).map(new ExpandInvocation(_)).toSeq

  private def findInductiveHypothesisApplication(e: Expr, ihs: StructuralInductionHypotheses): Map[String, Theorem] = {
    val ihsType = ihs.expression.getType

    val thms = collect[(String, Theorem)] { e: Expr =>
      if (ihs.isInner(e)) {
        ihs.hypothesis(e) match {
          case Success(thm) => Set((s"IH on `$e`", thm))
          case Failure(_)   => Set()
        }
      } else Set()
    }(e)

    thms.toMap
  }

  def unify(expr: Expr, pattern: Expr, instantiableVars: Set[Variable]): Option[Map[Variable, Expr]] = (expr, pattern) match {
    case (ev: Variable, pv: Variable) if ev == pv                               => Some(Map.empty)

    case (expr, pv: Variable) if instantiableVars(pv) && expr.getType == pv.tpe => Some(Map(pv -> expr))

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

  protected object TheoremWithExpression {
    def unapply(thm: Theorem): Option[(Theorem, Expr)] = Some((thm, thm.expression))
  }

  def followPath(thm: Theorem, path: Path, subst: Map[Variable, Expr]): Option[Theorem] = path match {
    case NotE(next)              => followPath(notE(thm), next, subst)
    case AndE(i, next)           => followPath(andE(thm)(i), next, subst)
    case ForallE(vals, next)     => followPath(forallE(thm)(subst(vals.head.toVariable), (vals.tail map (v => subst(v.toVariable)): _*)), next, subst)
    case ImplE(assumption, next) => ???
    case EndOfPath               => Some(thm)
  }

  def instantiateConclusion(expr: Expr, thm: Theorem): Seq[(Expr, Expr, Theorem)] = {
    val concls = conclusionsOf(thm.expression) flatMap (_ match {
      case concl @ Conclusion(Equals(a, b), vars, path) => Seq(
        (a, (x: Equals) => x.lhs, (x: Equals) => x.rhs, vars, path),
        (b, (x: Equals) => x.rhs, (x: Equals) => x.lhs, vars, path))
      case _ => Seq()
    })

    collectPreorderWithPath { (exp, exPath) =>
      concls flatMap {
        case (pattern, from, to, freeVars, path) =>
          unify(exp, pattern, freeVars) match {
            case Some(subst) => followPath(thm, path, subst).map {
              case TheoremWithExpression(thm, eq @ Equals(_, _)) => (from(eq), replaceTreeWithPath(expr, exPath, to(eq)), thm)
            }.toSeq
            case _ => Seq()
          }
      }
    }(expr).groupBy(x => (x._1, x._2)).map(_._2.head).toSeq
  }

  def findTheoremApplications(expr: Expr, thms: Map[String, Theorem]): Seq[Suggestion] = {
    thms.toSeq flatMap {
      case (name, thm) =>
        instantiateConclusion(expr, thm) map { case (subj, res, thm) => ApplyTheorem(name, thm, subj, res) }
    }
  }

  def analyse(e: Expr, thms: Map[String, Theorem], ihs: Option[StructuralInductionHypotheses]): (Seq[Suggestion], Map[String, Theorem]) = {
    val findInduct = ihs.map(findInductiveHypothesisApplication(e, _)).getOrElse(Map())
    val newThms = thms ++ findInduct
    (collectInvocations(e) ++ findTheoremApplications(e, newThms), newThms)
  }
}