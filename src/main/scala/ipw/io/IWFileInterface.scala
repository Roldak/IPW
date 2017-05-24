package ipw.io

import ipw.AssistedTheory

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._

protected[ipw] trait IWFileInterface { theory: AssistedTheory =>
  protected[ipw] type ProofIdentifier = Expr

  protected[ipw] def readProofDocument(source: String, id: ProofIdentifier): ProofDocument
}