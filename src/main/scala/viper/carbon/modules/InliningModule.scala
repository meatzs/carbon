package viper.carbon.modules

import viper.carbon.modules.components.Component
import viper.silver.{ast => sil}
import viper.silver.ast.{ErrorTrafo, Info, Method, Position}
import viper.silver.verifier.VerificationError
import viper.silver.ast
import viper.carbon.boogie._

trait InliningModule extends Module with Component {

  def length(s: sil.Stmt): Int

  def staticHeap(): Var

  var current_depth: Int

  def maxDepth: Int

  def normalState: (Var, Var)

  def silEmptyStmt(): ((Position, Info, ErrorTrafo) => ast.Seqn)

  def silNameNotUsed(s: String): String

  // ----------------------------------------------------------------
  // MATCH DETERMINISM
  // ----------------------------------------------------------------

  // Records:
  // - exhale heaps
  // - wildcard values
  // - new version of predicates unfolded (?)
  // - values of "freshObj"
  def recordDeterminism(s: Stmt): (Stmt, Seq[LocalVarDecl])

  def determinize(s: Stmt, l: Seq[LocalVarDecl], check: Exp, id_check: Int, e: VerificationError): (Stmt, Seq[LocalVarDecl])

  var recordedScopes: Seq[Seq[sil.LocalVar]]

  def recordVarsSil(s: sil.Stmt): sil.Stmt

  def assignVarsSil(s: sil.Stmt): sil.Stmt

  // Only changes "assume state" into "exists := exists && wfState"
  def changeStateWfState(s: Stmt, exists: LocalVar): Stmt

  def addIfExists(s: Stmt, exists: LocalVar): Stmt

  var id_var_deter: Int
  private val deter_namespace: Namespace = verifier.freshNamespace("determinism")

  def getVarDecl(name: String, typ: Type): LocalVarDecl

  // ----------------------------------------------------------------
  // CHECK SOUNDNESS CONDITION
  // ----------------------------------------------------------------

  def containsPermOrForperm(exp: sil.Exp): Boolean

  def containsAcc(exp: sil.Exp): Boolean

  def containsWildcard(exp: sil.Exp): Boolean

  def syntacticFraming(s: sil.Stmt, checkMono: Boolean = false): Boolean

  def wfMask(args: Seq[Exp], typ: Type = Bool): Exp

  def sumStateNormal(mask1: Var, heap1: Var, mask2: Var, heap2: Var, mask: Var, heap: Var): Exp

  def smallerState(smallMask: Var, smallHeap: Var, bigMask: Var, bigHeap: Var): Exp

  def doubleErrorSafeMono(s: Stmt, error: VerificationError, check: Exp, id_check: Int): Stmt

  def assumify(s: Stmt): Stmt

  var checkingFraming: Boolean

  def isCheckingFraming(): Boolean

  def assignSeqToSeq(s1: Seq[Var], s2: Seq[Var]): Stmt

  def equalSeq(s1: Seq[Var], s2: Seq[Var]): Exp

  def currentPermission(mask: Exp, rcv: Exp, location: Exp): MapSelect

  def getAxioms(): List[Decl]

  var current_exists: Option[Var]
  var id_checkFraming: Int
  var id_checkMono: Int

  def checkFraming(orig_s: sil.Stmt, orig: ast.Stmt, checkMono: Boolean = false, checkWFM: Boolean = false): Stmt

  def inlinable(stmt: sil.Stmt): Boolean

  def groupNonInlinableStmts(ss: Seq[sil.Stmt], orig_s: sil.Stmt): Seq[sil.Stmt]

  // ----------------------------------------------------------------
  // ACTUAL INLINING
  // ----------------------------------------------------------------

  def inlineLoop(w: sil.Stmt, cond: ast.Exp, invs: Seq[ast.Exp], body: ast.Seqn): Stmt

  def inlineMethod(m: Method, args: Seq[ast.Exp], targets: Seq[ast.LocalVar]): Stmt

  // ----------------------------------------------------------------
  // RENAMING
  // ----------------------------------------------------------------

  def readVarsExp(e: ast.Exp): Set[ast.LocalVar]

  def readVarsDecl(d: ast.Declaration): Seq[ast.LocalVar]

  var currentRenaming: Map[ast.LocalVar, ast.LocalVar]

  def newString(s: String): String

  def renameVar(x: ast.LocalVar): ast.LocalVar

  def renameExp(exp: ast.Exp): ast.Exp

  def renameAccPredicate(acc: ast.PredicateAccessPredicate): ast.PredicateAccessPredicate

  def renameDecl(d: sil.Declaration): sil.Declaration

  def renameWand(wand: sil.MagicWand): sil.MagicWand

  def alphaRename(s: ast.Stmt): ast.Stmt

}
