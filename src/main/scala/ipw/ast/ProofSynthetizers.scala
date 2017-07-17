package ipw.ast

import ipw.AssistedTheory
import ipw.ProofBuilder
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._

trait ProofSynthetizers { theory: AssistedTheory with ProofBuilder =>
  import AST._
  import scala.language.postfixOps
  import scala.language.implicitConversions

  private implicit def proofExpr2Expr(p: ProofExpr): Expr = p.e

  private case class Context(indent: Int, inBlock: Boolean) {
    def indented = Context(indent + 1, false)
    def newBlock = Context(indent + 1, true)
    def noBlock = Context(indent, false)
  }

  private def format(s: String)(implicit ctx: Context): String = {
    val lines = s.split("\n") map { line =>
      if (line.stripMargin != line) "  " * ctx.indent + line.stripMargin
      else line
    }

    lines.mkString("\n")
  }

  private def lineSize(line: String): Int = (line split ("\n")).foldLeft(0)((acc, line) => Math.max(acc, line.size))

  private def synthValDef(v: ValDef)(implicit ctx: Context): String = s""""${v.id.name}" :: ${v.tpe}"""

  private def synthExpr(e: Expr)(implicit ctx: Context): String = e match {
    case Forall(vals, body) if vals.size <= 4 =>
      s"forall(${vals map synthValDef mkString ", "})((${vals map (_.id.name) mkString ", "}) => ${synthExpr(body)})"

    case _ => e.toString
  }

  private def synthCase(c: Case)(implicit ctx: Context): String = {
    val fieldstr = if (c.fields.size > 0) ", " + (c.fields map (_.id.name) mkString (", ")) else ""
    s"""case C(`${c.id.name}`${fieldstr}) => ${rec(c.body)(ctx indented)}"""
  }

  private def tryTurnIntoEqChain(p: Prove)(implicit ctx: Context): Attempt[String] = {
    sealed abstract class EqChain(val expr: ProofExpr)
    case class EqNode(override val expr: ProofExpr, jst: Proof, next: EqChain) extends EqChain(expr)
    case class EqLeaf(override val expr: ProofExpr) extends EqChain(expr)

    def synthEqChain(chain: EqChain)(implicit ctx: Context): String = {
      def inner(chain: EqChain): (List[String], Int) = chain match {
        case EqNode(expr, jst, next) =>
          val exprstr = synthExpr(expr)(ctx noBlock)
          val jststr = if (jst == Prove(ProofExpr(Equals(expr, next.expr)))) "trivial" else recNoBlock(jst)
          val localen = Math.max(lineSize(exprstr), lineSize(jststr))
          val (rest, globalen) = inner(next)
          (exprstr :: jststr :: rest, Math.max(localen, globalen))

        case EqLeaf(expr) =>
          val exprstr = synthExpr(expr)(ctx noBlock)
          (List(exprstr), exprstr.size)
      }

      val (strs, len) = inner(chain)

      if (strs.size == 1) strs.head
      else strs.zipWithIndex.map {
        case (str, idx) =>
          val pad = (" " * (len - str.size))
          if (idx == 0) str + pad + " ==|"
          else if (idx == strs.size - 1) "|" + str + pad
          else if (idx % 2 == 0) "|" + str + pad + " ==|"
          else "|  " + pad + str + " |"
      }.mkString("\n")
    }
    
    def buildChain(toProve:Expr, p: Prove, sofar: EqChain, lastjst: Proof): Attempt[EqChain] = p match {
      case Prove(ProofExpr(Equals(`toProve`, expr)), Seq(next: Prove, jst)) =>
        buildChain(toProve, next, EqNode(ProofExpr(expr), lastjst, sofar), jst)
      case Prove(ProofExpr(BooleanLiteral(true)), Seq()) => EqNode(ProofExpr(toProve), lastjst, sofar)
      case _ => Attempt.fail("Could not deduce EqChain")
    }

    p match {
      case Prove(ProofExpr(toProve), Seq(p: Prove, _)) => p match {
        case Prove(ProofExpr(Equals(`toProve`, leaf)), Seq(next: Prove, jst)) => 
          buildChain(toProve, next, EqLeaf(ProofExpr(leaf)), jst) map synthEqChain
        case Prove(ProofExpr(BooleanLiteral(true)), Seq()) => "trivial"
        case _ => Attempt.fail("Could not deduce EqChain")
      }
      case _ => Attempt.fail("Could not deduce EqChain")
    }
  }

  private object ForallIExtractor {
    def unapply(p: Proof): Option[(Seq[ValDef], Proof)] = p match {
      case f: ForallI =>
        def extractVarsAndBody(f: ForallI): (Seq[ValDef], Proof) = f match {
          case ForallI(vs, next: ForallI) =>
            val (vars, body) = extractVarsAndBody(next)
            (vs ++ vars, body)
          case ForallI(vs, body) => (vs, body)
        }
        Some(extractVarsAndBody(f))

      case _ => None
    }
  }

  private def recIndented(proof: Proof)(implicit ctx: Context): String = rec(proof)(ctx indented)
  private def recNewBlock(proof: Proof)(implicit ctx: Context): String = rec(proof)(ctx newBlock)
  private def recNoBlock(proof: Proof)(implicit ctx: Context): String = rec(proof)(ctx noBlock)

  private def rec(proof: Proof)(implicit ctx: Context): String = format(proof match {
    case ForallIExtractor(vs, body) =>
      s"""forallI(${vs map (synthValDef(_)(ctx noBlock)) mkString (", ")}) { case Seq(${vs map (_.id.name) mkString (", ")}) => 
          |  ${recNewBlock(body)}
          |}"""

    case AndI(trees) => s"""andI(${trees map recNoBlock mkString ", "})"""

    case ImplI(id, hyp, body) =>
      s"""implI(${synthExpr(hyp)(ctx noBlock)}) { $id =>
	      |  ${recNewBlock(body)}
	      |}"""

    case ForallE(tree, exprs) =>
      val exprstr = exprs map (synthExpr(_)(ctx noBlock))
      s"""forallE(${recNoBlock(tree)})(${exprstr.mkString(", ")})"""

    case LetAndE(tree, ids, body) =>
      if (ctx.inBlock)
        s"""val Seq(${ids mkString ", "}) = andE(${recNoBlock(tree)}) : Seq[Theorem]
            |${rec(body)}"""
      else
        s"""{
            |  val Seq(${ids mkString ", "}) = andE(${recNoBlock(tree)}) : Seq[Theorem]
            |  ${recNewBlock(body)}
            |}"""

    case AndESelect(tree, idx) => s"""andE(${recNoBlock(tree)})($idx)"""

    case ImplE(tree, proof) => s"""implE(${recNoBlock(tree)})(_.by(${recNoBlock(proof)}))"""

    case AST.StructuralInduction(v, prop, ihs, cases) =>
      val newctx = ctx noBlock
      val casestr = (cases map (c => "|    " + synthCase(c)(newctx indented))) mkString ("\n")
      s"""structuralInduction((${v.id.name}: Expr) => ${synthExpr(prop)(newctx)}, ${synthValDef(v)(newctx)}) { case (${ihs}, goal) =>
          |  ${ihs}.expression match {
               ${casestr}
          |  }
          |}"""

    case HypothesisApplication(ihs, expr) => s"""${ihs}.hypothesis(${synthExpr(expr)(ctx noBlock)})"""

    case Fact(id) => id

    case Let(id, v, in) =>
      if (ctx.inBlock)
        s"""val $id = ${recIndented(v)}
            |${rec(in)}"""
      else
        s"""{
	        |  val $id = ${recIndented(v)}
	        |  ${recNewBlock(in)}
	        |}"""

    case p @ Prove(expr, lemmas) => tryTurnIntoEqChain(p) match {
      case Success(str) => str
      case _ =>
        val lemstr = if (lemmas.size > 0) ", " + ((lemmas map recNoBlock) mkString (", ")) else ""
        s"""prove(${synthExpr(expr)(ctx noBlock) + lemstr})"""
    }
  })

  def synthesizeProof(proof: Proof): String = rec(proof)(Context(0, true))
}