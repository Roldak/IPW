package ipw.ast

import ipw.AssistedTheory
import inox._
import inox.trees._
import inox.trees.dsl._

trait ProofTrees { self: AssistedTheory =>

  object AST {

    sealed abstract class Proof

    // Intro rules
    case class ForallI(v: ValDef, body: Proof) extends Proof
    case class ImplI(id: String, hyp: Expr, body: Proof) extends Proof
    case class AndI(trees: Seq[Proof]) extends Proof

    // Elim rules
    case class ForallE(tree: Proof, expr: Expr) extends Proof
    case class LetAndE(tree: Proof, ids: List[String], body: Proof) extends Proof
    case class ImplE(tree: Proof, proof: Proof) extends Proof

    // Induction
    
    case class Case(id: String, fields: Seq[ValDef], body: Proof)
    case class StructuralInduction(v: ValDef, prop: Expr, ihs: String, cases: Seq[Case]) extends Proof
    case class HypothesisApplication(ihs: String, expr: Expr) extends Proof

    // Others
    case class Fact(id: String) extends Proof
    case class Let(id: String, value: Proof, in: Proof) extends Proof
    case class Prove(expr: Expr, facts: Seq[Proof] = Nil) extends Proof
    
    // Chains
    sealed abstract class EqChain extends Proof
    case class EqNode(expr: Expr, jst: Proof, next: EqChain) extends EqChain
    case class EqLeaf(expr: Expr) extends EqChain

    def eval(proof: Proof): Attempt[Theorem] = {
      def findKey[T](map: Map[String, T], key: String): Attempt[T] = map get key match {
        case Some(v) => Success(v)
        case _ => Attempt.fail("not found")
      }
      
      def evalEqChain(node: EqNode)(implicit ctx: Context): (Attempt[Theorem], Expr) = node.next match {
        case next: EqNode => 
          val localthm = prove(node.expr === next.expr, rec(node.jst))
          val (restthm, last) = evalEqChain(next)
          (prove(node.expr === last, restthm, rec(node.jst)), last)
          
        case EqLeaf(last) => 
          (prove(node.expr === last, rec(node.jst)), last)
      } 

      case class Context(vars: Map[String, Expr], facts: Map[String, Theorem], ihss: Map[String, StructuralInductionHypotheses]) {
        def withVar(id: String, v: Expr) = Context(vars + (id -> v), facts, ihss)
        def withFact(id: String, thm: Theorem) = Context(vars, facts + (id -> thm), ihss)
        def withIhs(id: String, ihs: StructuralInductionHypotheses) = Context(vars, facts, ihss + (id -> ihs))

        def variable(id: String): Attempt[Expr] = findKey(vars, id)
        def fact(id: String): Attempt[Theorem] = findKey(facts, id)
        def ihs(id: String): Attempt[StructuralInductionHypotheses] = findKey(ihss, id)
      }

      def rec(proof: Proof)(implicit ctx: Context): Attempt[Theorem] = proof match {
        case ForallI(v, body) => forallI(v)(v => rec(body)(ctx withVar (v.id.name, v)))
        case ImplI(id, hyp, body) => implI(hyp)(h => rec(body)(ctx withFact (id, h)))
        case AndI(trees) => Attempt.all(trees map rec) flatMap (andI(_))

        case ForallE(tree, expr) => rec(tree) flatMap (forallE(_)(expr)) 
        case LetAndE(tree, ids, body) => rec(tree) flatMap andE flatMap (thms =>
          rec(body)((ids zip thms).foldLeft(ctx)((ctx, keyval) => ctx withFact (keyval._1, keyval._2))))
        case ImplE(tree, proof) => rec(tree) flatMap (implE(_)(goal => rec(proof) flatMap (goal.by(_))))
          
        case StructuralInduction(v, prop, ihsid, cases) => structuralInduction(_ => prop, v) { case (ihs, goal) => 
          val Some((caseId, exprs)) = C.unapplySeq(ihs.expression)
          cases.find(_.id == caseId.name) match {
            case Some(c) => rec(c.body)((c.fields zip exprs)
                .foldLeft(ctx withIhs (ihsid, ihs))((ctx, keyval) => ctx withVar (keyval._1.id.name, keyval._2)))
            case _ => Attempt.fail(s"Incomplete structural induction (no case for ${caseId})")
          }
        }
        case HypothesisApplication(ihsid, expr) => ctx ihs ihsid hypothesis(expr) 
        
        case Fact(id) => ctx fact id
        case Let(id, v, in) => rec(v) flatMap (v => rec(in)(ctx withFact (id, v)))
        case Prove(expr, lemmas) => Attempt.all(lemmas map rec) flatMap (prove(expr, _))
        
        case n: EqNode => evalEqChain(n)._1
        case EqLeaf(expr) => Attempt.fail("Invalid equality chain")
      }

      rec(proof)(Context(Map.empty, Map.empty, Map.empty))
    }

    def synthesize(proof: Proof): String = {
      def synthValDef(v: ValDef): String = s""""${v.id.name}" :: ${v.tpe}"""

      def synthExpr(e: Expr): String = e match {
        case Forall(vals, body) if vals.size <= 4 =>
          s"forall(${vals map synthValDef mkString ", "})((${vals map (_.id.name) mkString ", "}) => ${synthExpr(body)})"

        case _ => e.toString
      }

      def synthCase(c: Case): String = {
        val fieldstr = if (c.fields.size > 0) ", " + (c.fields map (_.id.name) mkString(", ")) else ""
        s"""case C(`${c.id}`${fieldstr}) => ${rec(c.body)}"""
      }
      
      def rec(proof: Proof): String = proof match {
        case ForallI(v, body) =>
          s"""forallI(${synthValDef(v)}) { ${v.id.name} => 
            ${rec(body)}
          }"""

        case ImplI(id, hyp, body) =>
          s"""implI(${synthExpr(hyp)}) { $id =>
	        ${rec(body)}
	      }"""

        case AndI(trees) => s"""andI(${trees map rec mkString ", "})"""

        case ForallE(tree, expr) => s"""forallE(${rec(tree)})(${synthExpr(expr)})"""
        
        case LetAndE(tree, ids, body) =>
          s"""{
            val Seq(${ids mkString ", "}) = andE(${rec(tree)}) : Seq[Theorem]
            ${rec(body)}
          }"""
            
        case ImplE(tree, proof) => s"""implE(${rec(tree)})(_.by(${rec(proof)}))"""

        case StructuralInduction(v, prop, ihs, cases) =>
          val casestr = (cases map synthCase) mkString ("\n")
          s"""structuralInduction((${v.id.name}: Expr) => ${synthExpr(prop)}, ${synthValDef(v)}) { case (${ihs}, goal) =>
            ${ihs}.expression match {
          	${casestr}
            }
          }"""
        
        case HypothesisApplication(ihs, expr) => s"""${ihs}.hypothesis(${synthExpr(expr)})"""
          	
        case Fact(id) => id

        case Let(id, v, in) =>
          s"""{
	        val $id = ${rec(v)}
	        ${rec(in)}
	      }"""
	        
        case Prove(expr, lemmas) =>
          val lemstr = if (lemmas.size > 0) ", " + ((lemmas map rec) mkString(", ")) else ""
          s"""prove(${synthExpr(expr) + lemstr})"""
          
        case EqNode(expr, jst, next) =>
          s"""${synthExpr(expr)} ==|
          ${rec(jst)} |
          ${rec(next)}
          """
          
        case EqLeaf(expr) => s"""${synthExpr(expr)}"""
      }

      rec(proof)
    }

  }
}