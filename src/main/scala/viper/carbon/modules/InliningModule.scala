package viper.carbon.modules

import viper.carbon.modules.components.{CarbonStateComponent, Component, ComponentRegistry, StmtComponent}
import viper.silver.{ast => sil}
import viper.silver.ast.{ErrorTrafo, Info, Method, Position}
import viper.silver.verifier.VerificationError
import viper.silver.ast
import viper.carbon.boogie._

// trait InhaleModule extends Module with InhaleComponent with ComponentRegistry[InhaleComponent] {
trait InliningModule extends Module with Component {

  var current_exists: Option[Var]
  var current_exists_sil: Option[sil.LocalVar]

  def wfMask(args: Seq[Exp], typ: Type = Bool): Exp

  def sumStateNormal(mask1: Var, heap1: Var, mask2: Var, heap2: Var, mask: Var, heap: Var): Exp

  def smallerState(smallMask: Var, smallHeap: Var, bigMask: Var, bigHeap: Var): Exp

  var current_depth: Int

  def maxDepth: Int

  var used_checks: Set[String]

  def containsPermOrForperm(exp: sil.Exp): Boolean

  def containsAcc(exp: sil.Exp): Boolean

  def containsWildcard(exp: sil.Exp): Boolean

  def syntacticFraming(s: sil.Stmt, checkMono: Boolean = false): Boolean

  def recordExhaleHeaps(s: Stmt): (Stmt, Seq[LocalVarDecl])

  def assumeExhaleHeap(s: Stmt, l: Seq[LocalVarDecl], check: LocalVar, e: VerificationError): (Stmt, Seq[LocalVarDecl])

  def normalState: (Var, Var)

  var id_checkFraming: Int
  var id_checkMono: Int

  def silEmptyStmt(): ((Position, Info, ErrorTrafo) => ast.Seqn)

  def silNameNotUsed(s: String): String

  var recordedScopes: Seq[Seq[sil.LocalVar]]

  def recordVarsSil(s: sil.Stmt): sil.Stmt

  def assignVarsSil(s: sil.Stmt): sil.Stmt

  def removeAssume(s: Stmt, exists: LocalVar): Stmt

  def modifError(s: Stmt, error: VerificationError, check: Var): Stmt

  def assumify(s: Stmt): Stmt

  var checkingFraming: Boolean

  def isCheckingFraming(): Boolean

  def assignSeqToSeq(s1: Seq[Var], s2: Seq[Var]): Stmt

  def equalSeq(s1: Seq[Var], s2: Seq[Var]): Exp

  var id_wfm: Int

  def checkFraming(orig_s: sil.Stmt, orig: ast.Stmt, checkMono: Boolean = false, checkWFM: Boolean = false): Stmt

  def inlineLoop(w: sil.Stmt, cond: ast.Exp, invs: Seq[ast.Exp], body: ast.Seqn): Stmt

  def inlineMethod(m: Method, args: Seq[ast.Exp], targets: Seq[ast.LocalVar]): Stmt

  def inlinable(stmt: sil.Stmt): Boolean

  def groupNonInlinableStmts(ss: Seq[sil.Stmt], orig_s: sil.Stmt): Seq[sil.Stmt]

  def getAxioms(): List[Decl]

}
