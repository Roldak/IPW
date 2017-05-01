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
        //vals.foldLeft(conclusionsOf(body))((paths: Seq[Conclusion], v: ValDef) => paths map (_.forallE(v)))
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

    //println(thms map {case (_, thm) => conclusionsOf(thm.expression)})
    import theory._
    val tmp = Forall(Seq("x" :: IntegerType, "y" :: IntegerType),
      Forall(Seq("z" :: IntegerType), (E("x") === E("y")) ==> (E("x") === E("z"))))

    //theory.conclusionsOf(tmp) foreach println

    val x = ("x" :: IntegerType)
    val y = ("y" :: IntegerType)
    val z = ("z" :: IntegerType).toVariable
    println(theory.unify(Forall(Seq(x), x.toVariable === E(2)), Lambda(Seq(y), y.toVariable === z), Set(z)))

    thms.toMap
  }

  def unify(expr: Expr, pattern: Expr, instantiableVars: Set[Variable]): Option[Map[Variable, Expr]] = (expr, pattern) match {
    case (ev: Variable, pv: Variable) if ev == pv     => Some(Map.empty)

    case (expr, pv: Variable) if instantiableVars(pv) => Some(Map(pv -> expr))

    case (expr, pattern) if expr.getClass == pattern.getClass =>
      val (evars, eexprs, etypes, ebuilder) = deconstructor.deconstruct(expr)
      val (pvars, pexprs, ptypes, pbuilder) = deconstructor.deconstruct(pattern)

      if (evars.size == pvars.size &&
        eexprs.size == pexprs.size &&
        etypes == ptypes) {

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

  def followPath(thm: Theorem, path: Path, subst: Map[Variable, Expr]): Option[Theorem] = path match {
    case NotE(next)               => followPath(notE(thm), next, subst)
    case AndE(i, next)            => followPath(andE(thm)(i), next, subst)
    case ForallE(v :: vals, next) => followPath(forallE(thm)(subst(v.toVariable), (vals map (v => subst(v.toVariable)): _*)), next, subst)
    case ImplE(assumption, next)  => ???
    case EndOfPath                => Some(thm)
  }

  def instantiateConclusion(expr: Expr, thm: Theorem): Seq[(Expr, Theorem)] = {
    val concls = conclusionsOf(thm.expression) flatMap (_ match {
      case concl @ Conclusion(Equals(a, b), vars, path) => Seq(
        (a, (x: Equals) => x.rhs, vars, path),
        (b, (x: Equals) => x.lhs, vars, path))
      case _ => Seq()
    })

    println(s"conclusions for $thm:")
    concls foreach println

    collectPreorder { expr =>
      concls flatMap {
        case (pattern, getter, freeVars, path) =>
          unify(expr, pattern, freeVars) match {
            case Some(subst) => followPath(thm, path, subst).map(thm => thm.expression match {
              case e: Equals => (getter(e), thm)
            }).toSeq
            case _ => Seq()
          }
      }
    }(expr)
  }

  def findTheoremApplications(expr: Expr, thms: Map[String, Theorem]): Seq[Suggestion] = {
    thms.toSeq flatMap {
      case (name, thm) =>
        instantiateConclusion(expr, thm) map { case (res, thm) => ApplyTheorem(name, thm, res) }
    }
  }

  def analyse(e: Expr, thms: Map[String, Theorem], ihs: Option[StructuralInductionHypotheses]): (Seq[Suggestion], Map[String, Theorem]) = {
    val findInduct = ihs.map(findInductiveHypothesisApplication(e, _)).getOrElse(Map())
    val newThms = thms ++ findInduct
    (collectInvocations(e) ++ findTheoremApplications(e, newThms), newThms)
  }
}