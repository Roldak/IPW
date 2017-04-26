package ipw.eval

import inox._
import inox.evaluators._

import scala.collection.BitSet

object optInvokeFirst extends FlagOptionDef("invokefirst", false)

protected[eval] trait PartialEvaluatorHelper { eval: PartialEvaluator =>
  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  lazy val ignoreContracts = options.findOptionOrDefault(optIgnoreContracts)

  private def shift(b: BitSet, size: Int, i: Int): BitSet =
    b.map(_ + i).filter(bit => bit >= 1 && bit <= size)

  protected def finiteSet(els: Iterable[Expr], tpe: Type): FiniteSet = {
    FiniteSet(els.toSeq.distinct.sortBy(_.toString), tpe)
  }

  protected def finiteBag(els: Iterable[(Expr, Expr)], tpe: Type): FiniteBag = {
    FiniteBag(els.toMap.toSeq.filter { case (_, IntegerLiteral(i)) => i > 0 case _ => false }.sortBy(_._1.toString), tpe)
  }

  protected def finiteMap(els: Iterable[(Expr, Expr)], default: Expr, from: Type, to: Type): FiniteMap = {
    FiniteMap(els.toMap.toSeq.filter { case (_, value) => value != default }.sortBy(_._1.toString), default, from, to)
  }

  protected[eval] def ev(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    val res = expr match {
      case v: Variable => rctx.mappings.get(v.toVal).getOrElse(v)

      case Application(caller, args) =>
        val newArgs = args map ev
        ev(caller) match {
          case l @ Lambda(params, body) =>
            val mapping = l.paramSubst(newArgs)
            ev(body)(rctx.withNewVars(mapping), gctx)
          case f =>
            Application(f, newArgs)
        }

      case Tuple(ts) =>
        Tuple(ts map ev)

      case TupleSelect(t, i) =>
        val Tuple(rs) = ev(t)
        rs(i - 1)

      case Let(i, ex, b) =>
        val first = ev(ex)
        ev(b)(rctx.withNewVar(i, first), gctx)

      case Assume(cond, body) =>
        if (!ignoreContracts && ev(cond) != BooleanLiteral(true))
          throw RuntimeError("Assumption did not hold @" + expr.getPos)
        ev(body)

      case IfExpr(cond, thenn, elze) =>
        val first = ev(cond)
        first match {
          case BooleanLiteral(true)  => ev(thenn)
          case BooleanLiteral(false) => ev(elze)
          case _                     => IfExpr(first, ev(thenn), ev(elze))
        }

      case FunctionInvocation(id, tps, args) =>
        FunctionInvocation(id, tps, args map ev)

      case And(Seq(e1, e2)) => ev(e1) match {
        case BooleanLiteral(false) => BooleanLiteral(false)
        case BooleanLiteral(true)  => ev(e2)
        case le                    => And(le, ev(e2))
      }

      case And(args) =>
        ev(And(args.head, And(args.tail)))

      case Or(Seq(e1, e2)) => ev(e1) match {
        case BooleanLiteral(true)  => BooleanLiteral(true)
        case BooleanLiteral(false) => ev(e2)
        case le                    => Or(le, ev(e2))
      }

      case Or(args) =>
        ev(Or(args.head, Or(args.tail)))

      case Not(arg) =>
        ev(arg) match {
          case BooleanLiteral(v) => BooleanLiteral(!v)
          case other             => Not(other)
        }

      case Implies(l, r) =>
        ev(l) match {
          case BooleanLiteral(false) => BooleanLiteral(true)
          case BooleanLiteral(true)  => ev(r)
          case le                    => Implies(le, ev(r))
        }

      case Equals(le, re) =>
        BooleanLiteral(ev(le) == ev(re))

      case ADT(adt, args) =>
        val cc = ADT(adt, args.map(ev))
        if (!ignoreContracts) adt.getADT.invariant.foreach { tfd =>
          val v = Variable.fresh("x", adt, true)
          ev(tfd.applied(Seq(v)))(rctx.withNewVar(v.toVal, cc), gctx) match {
            case BooleanLiteral(true) =>
            case BooleanLiteral(false) =>
              throw RuntimeError("ADT invariant violation for " + cc.asString)
            case other =>
              throw RuntimeError(typeErrorMsg(other, BooleanType))
          }
        }
        cc

      case AsInstanceOf(expr, ct) =>
        val le = ev(expr)
        if (isSubtypeOf(le.getType, ct)) {
          le
        } else {
          throw RuntimeError("Cast error: cannot cast " + le.asString + " to " + ct.asString)
        }

      case IsInstanceOf(expr, ct) =>
        val le = ev(expr)
        BooleanLiteral(isSubtypeOf(le.getType, ct))

      case ADTSelector(expr, sel) =>
        ev(expr) match {
          case ADT(adt, args) => args(adt.getADT.definition match {
            case cons: ADTConstructor => cons.selectorID2Index(sel)
            case _                    => throw RuntimeError("Unexpected case class type")
          })
          case le => ADTSelector(le, sel)
        }

      case Plus(l, r) =>
        (ev(l), ev(r)) match {
          case (BVLiteral(i1, s1), BVLiteral(i2, s2)) if s1 == s2 => BVLiteral(
            (1 to s1).foldLeft((BitSet.empty, false)) {
              case ((res, carry), i) =>
                val (b1, b2) = (i1(i), i2(i))
                val nextCarry = (b1 && b2) || (b1 && carry) || (b2 && carry)
                val ri = b1 ^ b2 ^ carry
                (if (ri) res + i else res, nextCarry)
            }._1, s1)
          case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 + i2)
          case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
            normalizeFraction(FractionLiteral(ln * rd + rn * ld, ld * rd))
          case (le, re) => Plus(le, re)
        }

      case Minus(l, r) =>
        (ev(l), ev(r)) match {
          case (b1: BVLiteral, b2: BVLiteral)           => ev(Plus(b1, UMinus(b2)))
          case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 - i2)
          case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
            normalizeFraction(FractionLiteral(ln * rd - rn * ld, ld * rd))
          case (le, re) => Minus(le, re)
        }

      case StringConcat(l, r) =>
        (ev(l), ev(r)) match {
          case (StringLiteral(i1), StringLiteral(i2)) => StringLiteral(i1 + i2)
          case (le, re)                               => StringConcat(le, re)
        }

      case StringLength(a) => ev(a) match {
        case StringLiteral(a) => IntegerLiteral(a.length)
        case res              => StringLength(res)
      }

      case SubString(a, start, end) => (ev(a), ev(start), ev(end)) match {
        case (StringLiteral(a), IntegerLiteral(b), IntegerLiteral(c)) =>
          StringLiteral(a.substring(b.toInt, c.toInt))
        case (x, y, z) => SubString(x, y, z)
      }

      case UMinus(ex) =>
        ev(ex) match {
          case b @ BVLiteral(_, s)   => BVLiteral(-b.toBigInt, s)
          case IntegerLiteral(i)     => IntegerLiteral(-i)
          case FractionLiteral(n, d) => FractionLiteral(-n, d)
          case re                    => UMinus(re)
        }

      case Times(l, r) =>
        (ev(l), ev(r)) match {
          case (BVLiteral(i1, s1), BVLiteral(i2, s2)) if s1 == s2 =>
            i1.foldLeft(BVLiteral(0, s1): Expr) {
              case (res, i) =>
                ev(Plus(res, BVLiteral(shift(i2, s2, i - 1), s1)))
            }
          case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 * i2)
          case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
            normalizeFraction(FractionLiteral((ln * rn), (ld * rd)))
          case (le, re) => Times(le, re)
        }

      case Division(l, r) =>
        (ev(l), ev(r)) match {
          case (b1 @ BVLiteral(_, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            val bi2 = b2.toBigInt
            if (bi2 != 0) BVLiteral(b1.toBigInt / bi2, s1) else throw RuntimeError("Division by 0.")
          case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
            if (i2 != BigInt(0)) IntegerLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
          case (FractionLiteral(ln, ld), FractionLiteral(rn, rd)) =>
            if (rn != 0)
              normalizeFraction(FractionLiteral(ln * rd, ld * rn))
            else throw RuntimeError("Division by 0.")
          case (le, re) => Division(le, re)
        }

      case Remainder(l, r) =>
        (ev(l), ev(r)) match {
          case (b1 @ BVLiteral(_, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            val bi2 = b2.toBigInt
            if (bi2 != 0) BVLiteral(b1.toBigInt % bi2, s1) else throw RuntimeError("Division by 0.")
          case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
            if (i2 != BigInt(0)) IntegerLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
          case (le, re) => Remainder(le, re)
        }

      case Modulo(l, r) =>
        (ev(l), ev(r)) match {
          case (b1 @ BVLiteral(_, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            val bi2 = b2.toBigInt
            if (bi2 < 0)
              BVLiteral(b1.toBigInt mod (-bi2), s1)
            else if (bi2 != 0)
              BVLiteral(b1.toBigInt mod bi2, s1)
            else
              throw RuntimeError("Modulo of division by 0.")
          case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
            if (i2 < 0)
              IntegerLiteral(i1 mod (-i2))
            else if (i2 != BigInt(0))
              IntegerLiteral(i1 mod i2)
            else
              throw RuntimeError("Modulo of division by 0.")
          case (le, re) => Modulo(le, re)
        }

      case BVNot(b) =>
        ev(b) match {
          case BVLiteral(bs, s) =>
            BVLiteral(BitSet.empty ++ (1 to s).flatMap(i => if (bs(i)) None else Some(i)), s)
          case other => BVNot(other)
        }

      case BVAnd(l, r) =>
        (ev(l), ev(r)) match {
          case (BVLiteral(i1, s1), BVLiteral(i2, s2)) if s1 == s2 => BVLiteral(i1 & i2, s1)
          case (le, re) => BVAnd(le, re)
        }

      case BVOr(l, r) =>
        (ev(l), ev(r)) match {
          case (BVLiteral(i1, s1), BVLiteral(i2, s2)) if s1 == s2 => BVLiteral(i1 | i2, s1)
          case (le, re) => BVOr(le, re)
        }

      case BVXor(l, r) =>
        (ev(l), ev(r)) match {
          case (BVLiteral(i1, s1), BVLiteral(i2, s2)) if s1 == s2 => BVLiteral(i1 ^ i2, s1)
          case (le, re) => BVXor(le, re)
        }

      case BVShiftLeft(l, r) =>
        (ev(l), ev(r)) match {
          case (BVLiteral(i1, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            BVLiteral(shift(i1, s1, b2.toBigInt.toInt), s1)
          case (le, re) => BVShiftLeft(le, re)
        }

      case BVAShiftRight(l, r) =>
        (ev(l), ev(r)) match {
          case (BVLiteral(i1, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            val shiftCount = b2.toBigInt.toInt
            val shifted = shift(i1, s1, -shiftCount)
            BVLiteral(if (i1(s1)) shifted ++ ((s1 - shiftCount) to s1) else shifted, s1)
          case (le, re) => BVAShiftRight(le, re)
        }

      case BVLShiftRight(l, r) =>
        (ev(l), ev(r)) match {
          case (BVLiteral(i1, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            BVLiteral(shift(i1, s1, -b2.toBigInt.toInt), s1)
          case (le, re) => BVLShiftRight(le, re)
        }

      case LessThan(l, r) =>
        (ev(l), ev(r)) match {
          case (b1 @ BVLiteral(_, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            BooleanLiteral(b1.toBigInt < b2.toBigInt)
          case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 < i2)
          case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
            val FractionLiteral(n, _) = ev(Minus(a, b))
            BooleanLiteral(n < 0)
          case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 < c2)
          case (le, re)                           => LessThan(le, re)
        }

      case GreaterThan(l, r) =>
        (ev(l), ev(r)) match {
          case (b1 @ BVLiteral(_, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            BooleanLiteral(b1.toBigInt > b2.toBigInt)
          case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 > i2)
          case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
            val FractionLiteral(n, _) = ev(Minus(a, b))
            BooleanLiteral(n > 0)
          case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 > c2)
          case (le, re)                           => GreaterThan(le, re)
        }

      case LessEquals(l, r) =>
        (ev(l), ev(r)) match {
          case (b1 @ BVLiteral(_, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            BooleanLiteral(b1.toBigInt <= b2.toBigInt)
          case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 <= i2)
          case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
            val FractionLiteral(n, _) = ev(Minus(a, b))
            BooleanLiteral(n <= 0)
          case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 <= c2)
          case (le, re)                           => LessEquals(le, re)
        }

      case GreaterEquals(l, r) =>
        (ev(l), ev(r)) match {
          case (b1 @ BVLiteral(_, s1), b2 @ BVLiteral(_, s2)) if s1 == s2 =>
            BooleanLiteral(b1.toBigInt >= b2.toBigInt)
          case (IntegerLiteral(i1), IntegerLiteral(i2)) => BooleanLiteral(i1 >= i2)
          case (a @ FractionLiteral(_, _), b @ FractionLiteral(_, _)) =>
            val FractionLiteral(n, _) = ev(Minus(a, b))
            BooleanLiteral(n >= 0)
          case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 >= c2)
          case (le, re)                           => GreaterEquals(le, re)
        }

      case SetAdd(s1, elem) =>
        (ev(s1), ev(elem)) match {
          case (FiniteSet(els1, tpe), evElem) => finiteSet(els1 :+ evElem, tpe)
          case (le, re)                       => SetAdd(le, re)
        }

      case SetUnion(s1, s2) =>
        (ev(s1), ev(s2)) match {
          case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1 ++ els2, tpe)
          case (le, re)                                   => SetUnion(le, re)
        }

      case SetIntersection(s1, s2) =>
        (ev(s1), ev(s2)) match {
          case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1 intersect els2, tpe)
          case (le, re)                                   => SetIntersection(le, re)
        }

      case SetDifference(s1, s2) =>
        (ev(s1), ev(s2)) match {
          case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1.toSet -- els2, tpe)
          case (le, re)                                   => SetDifference(le, re)
        }

      case ElementOfSet(el, s) => (ev(el), ev(s)) match {
        case (ev, FiniteSet(els, _)) => BooleanLiteral(els.contains(ev))
        case (l, r)                  => ElementOfSet(l, r)
      }

      case SubsetOf(s1, s2) => (ev(s1), ev(s2)) match {
        case (FiniteSet(els1, _), FiniteSet(els2, _)) => BooleanLiteral(els1.toSet.subsetOf(els2.toSet))
        case (le, re)                                 => SubsetOf(le, re)
      }

      case f @ FiniteSet(els, base) =>
        finiteSet(els.map(ev), base)

      case BagAdd(bag, elem) => (ev(bag), ev(elem)) match {
        case (FiniteBag(els, tpe), evElem) =>
          val (matching, rest) = els.partition(_._1 == evElem)
          finiteBag(rest :+ (evElem -> matching.lastOption.map {
            case (_, IntegerLiteral(i)) => IntegerLiteral(i + 1)
            case (_, ev)                => throw EvalError(typeErrorMsg(ev, IntegerType))
          }.getOrElse(IntegerLiteral(1))), tpe)

        case (le, re) => BagAdd(le, re)
      }

      case MultiplicityInBag(elem, bag) => (ev(elem), ev(bag)) match {
        case (evElem, FiniteBag(els, tpe)) =>
          els.collect { case (k, v) if k == evElem => v }.lastOption.getOrElse(IntegerLiteral(0))
        case (le, re) => MultiplicityInBag(le, re)
      }

      case BagIntersection(b1, b2) => (ev(b1), ev(b2)) match {
        case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
          val map2 = els2.toMap
          finiteBag(els1.flatMap {
            case (k, v) =>
              val i = (v, map2.getOrElse(k, IntegerLiteral(0))) match {
                case (IntegerLiteral(i1), IntegerLiteral(i2)) => i1 min i2
                case (le, re)                                 => throw EvalError(typeErrorMsg(le, IntegerType))
              }

              if (i <= 0) None else Some(k -> IntegerLiteral(i))
          }, tpe)

        case (le, re) => BagIntersection(le, re)
      }

      case BagUnion(b1, b2) => (ev(b1), ev(b2)) match {
        case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
          val (map1, map2) = (els1.toMap, els2.toMap)
          finiteBag((map1.keys ++ map2.keys).toSet.map { (k: Expr) =>
            k -> ((map1.getOrElse(k, IntegerLiteral(0)), map2.getOrElse(k, IntegerLiteral(0))) match {
              case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 + i2)
              case (le, re)                                 => throw EvalError(typeErrorMsg(le, IntegerType))
            })
          }.toSeq, tpe)

        case (le, re) => BagUnion(le, re)
      }

      case BagDifference(b1, b2) => (ev(b1), ev(b2)) match {
        case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
          val map2 = els2.toMap
          finiteBag(els1.flatMap {
            case (k, v) =>
              val i = (v, map2.getOrElse(k, IntegerLiteral(0))) match {
                case (IntegerLiteral(i1), IntegerLiteral(i2)) => i1 - i2
                case (le, re)                                 => throw EvalError(typeErrorMsg(le, IntegerType))
              }

              if (i <= 0) None else Some(k -> IntegerLiteral(i))
          }, tpe)

        case (le, re) => BagDifference(le, re)
      }

      case FiniteBag(els, base) =>
        finiteBag(els.map { case (k, v) => (ev(k), ev(v)) }, base)

      case l @ Lambda(_, _) =>
        val (nl, deps) = normalizeStructure(l)
        val newCtx = deps.foldLeft(rctx) {
          case (rctx, (v, dep)) => rctx.withNewVar(v.toVal, ev(dep)(rctx, gctx))
        }
        val mapping = variablesOf(nl).map(v => v -> newCtx.mappings(v.toVal)).toMap
        replaceFromSymbols(mapping, nl)

      case f: Forall => onForallInvocation {
        replaceFromSymbols(variablesOf(f).map(v => v -> ev(v)).toMap, f).asInstanceOf[Forall]
      }

      case c: Choose =>
        rctx.getChoose(c.res.id) match {
          case Some(expr) => ev(expr)(rctx.withoutChoose(c.res.id), gctx)
          case None => onChooseInvocation {
            replaceFromSymbols(variablesOf(c).map(v => v -> ev(v)).toMap, c).asInstanceOf[Choose]
          }
        }

      case f @ FiniteMap(ss, dflt, kT, vT) =>
        finiteMap(ss.map { case (k, v) => (ev(k), ev(v)) }, ev(dflt), kT, vT)

      case g @ MapApply(m, k) => (ev(m), ev(k)) match {
        case (FiniteMap(ss, dflt, _, _), ev) =>
          ss.toMap.getOrElse(ev, dflt)
        case (l, r) => MapApply(l, r)
      }

      case g @ MapUpdated(m, k, v) => (ev(m), ev(k), ev(v)) match {
        case (FiniteMap(ss, dflt, kT, vT), ek, ev) =>
          finiteMap((ss.toMap + (ek -> ev)).toSeq, dflt, kT, vT)
        case (m, l, r) => MapUpdated(m, l, r)
      }

      case gl: GenericValue    => gl
      case fl: FractionLiteral => normalizeFraction(fl)
      case l: Literal[_]       => l

      case other               => other
    }
    println(s"$expr: ${expr.getType} => $res: ${expr.getType}")
    res
  }
}

trait PartialEvaluator
    extends ContextualEvaluator
    with DeterministicEvaluator
    with SolvingEvaluator
    with PartialEvaluatorHelper {

  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  val name = "Partial Evaluator"

  lazy val invokefirst = options.findOptionOrDefault(optInvokeFirst)

  protected[eval] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case FunctionInvocation(id, tps, args) if invokefirst =>
      val tfd = getFunction(id, tps)
      val evArgs = args map super[PartialEvaluatorHelper].ev

      // build a mapping for the function...
      val frame = rctx.withNewVars(tfd.paramSubst(evArgs)).newTypes(tps)

      super[PartialEvaluatorHelper].ev(tfd.fullBody)(frame, gctx)

    case other =>
      super[PartialEvaluatorHelper].ev(other)
  }
}

object PartialEvaluator {
  def apply(p: InoxProgram, opts: Options): PartialEvaluator { val program: p.type } = {
    new {
      val program: p.type = p
      val options = opts
    } with PartialEvaluator with HasDefaultGlobalContext with HasDefaultRecContext {
      val semantics: p.Semantics = p.getSemantics
    }
  }

  def default(p: InoxProgram) = apply(p, p.ctx.options)
}