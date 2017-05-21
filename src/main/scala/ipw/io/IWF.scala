package ipw.io

import ipw.AssistedTheory

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._

protected[ipw] trait IWFileInterface { theory: AssistedTheory =>
  protected[ipw] type IWFTitle = (Expr, Seq[Theorem])
  protected[ipw] type IWFDocument = List[Suggestion]
  
  protected[ipw] def readIWFDocument(source: String, title: IWFTitle): IWFDocument
  protected[ipw] def writeIWFDocument(source: String, title: IWFTitle, document: IWFDocument): Unit
}

protected[ipw] trait IOs { theory: AssistedTheory with IWFileInterface =>
  protected[ipw] class IWFInterface(private val source: String, private val title: IWFTitle) {
    private var doc: IWFDocument = readIWFDocument(source, title)

    def cancel: Unit = doc match {
      case e :: es => doc = es
      case _       =>
    }

    def append(s: Suggestion): Unit = {
      doc = s :: doc
    }

    def save(): Unit = {
      writeIWFDocument(source, title, doc)
    }
  }
}