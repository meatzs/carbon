package viper.carbon.modules

import viper.carbon.modules.components.Component
import viper.silver.{ast => sil}
import viper.silver.ast.{ErrorTrafo, Info, Method, Position}
import viper.silver.verifier.VerificationError
import viper.silver.ast
import viper.carbon.boogie._

import scala.collection.mutable.ListBuffer

trait InliningModule extends Module with Component {

  def annotateMethod(m: ast.Method): ast.Method
  def annotateStmt(s: ast.Stmt): ast.Stmt
  def flattenStmt(s: sil.Stmt): sil.Stmt

  def length(s: sil.Stmt): Int

  def staticHeap(): Var

  var current_depth: Int

  def maxDepth: Int

  def normalState: (Var, Var)

  def silEmptyStmt(): ((Position, Info, ErrorTrafo) => ast.Seqn)

  def silNameNotUsed(s: String): String

  // ----------------------------------------------------------------
  // CALLSTACK AND ERROR-MESSAGE GENERATION
  // ----------------------------------------------------------------

  /** Set of and loops that are supposed to be printed verbose */
  var verboseSet: Set[Int]

  /** Name of entry method when verifying a program. Either defined by option verifier.entry or default. */
  var entryMethod: String

  /** keeps track of inlined loops and serves as unique id to distinguish between inlined loops with same position*/
  var loopEnumerationCounter: Int

  /** increments loopEnumerationCounter by 1 */
  def incrementLoopEnumCounter(): Unit

  /**
   * Does not consume the callstack (DefaultInliningModule.callStack) generated during inlining and does
   * not modify any variables.
   *
   * @return returns String of the callstack generated during inlining. If verifier.verboseCallstack.isDefined it will
   *         use the non-collapsed callstack in the return. Otherwise, it will use the collapsed version of the
   *         callStack.
   */
  def callStackToString() : String

  def copyCallStack(): ListBuffer[(sil.Stmt, Boolean)]

  /**
   * Does not consume the callstack (DefaultInliningModule.callStack) generated during inlining and does
   * not modify any variables.
   *
   * @return returns String of the non-collapsed callstack generated during inlining
   */
  def callStackToStringVerbose(): String

  /**
    * Only gets called if staticInlining is active. The method will add information about the confidence level of an
    * error. If there is no soundness check error then the readable massage of all errors in the errormap with their key
    * as element of errorIds will be extended with the message that the confidence level is high. Otherwise the
    * readable message of the errors in the errormap with their key as element of errorIds will be extended with the
    * message that the confidence level is low. The soundness check errors themselves do not have a confidence level.
    *
    * @param errorIds The sequence of boogie error ids that failed the assertion.
    */
  def soundnessCheckConfidenceTransformation(errorIds: Seq[Int], oldErrormap: Map[Int, VerificationError]): Map[Int, VerificationError]



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

  def recordVarsSil(s: sil.Stmt, exists: sil.LocalVar): sil.Stmt

  def assignVarsSil(s: sil.Stmt, exists: sil.LocalVar): sil.Stmt

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

  //def doubleErrorSafeMono(s: Stmt, error: VerificationError, check: Exp, id_check: Int): Stmt
  def doubleErrorSafeMono(s: Stmt, orig: sil.Stmt, id_error: Int, type_error: String, check: Exp, id_check: Int): Stmt

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
  var n_syntactic: Int
  var n_syntactic_not: Int

  def checkFraming(pre_orig_s: sil.Stmt, orig: ast.Stmt, checkMono: Boolean = false, checkWFM: Boolean = false, modif_vars: Seq[LocalVar] = Seq()): Stmt

  /**
   * Only checks if the code contains method calls or loops. Does not check soundness.
   *
   * @param stmt a Viper statement
   * @return True if stmt contains a method call of a defined method or a loop
   */
  def inlinable(stmt: sil.Stmt): Boolean

  def alreadyGroupedInlinableStmts(ss: Seq[sil.Stmt]): Boolean
  def groupNonInlinableStmts(ss: Seq[sil.Stmt], orig_s: sil.Stmt, locals: Seq[sil.LocalVarDecl]): (Seq[sil.Stmt], Seq[sil.LocalVarDecl])

  // ----------------------------------------------------------------
  // LABEL RENAMING
  // ----------------------------------------------------------------

  def getLabel(s: String): String

  def updateLabel(s: String): String

  // ----------------------------------------------------------------
  // ACTUAL INLINING
  // ----------------------------------------------------------------


  def ignoreErrorsWhenBounded(stmt: Stmt): Stmt

  def inlineLoop(w: sil.WhileInl): Stmt

  def inlineMethod(mc: sil.MethodCall, m: Method, args: Seq[ast.Exp], targets: Seq[ast.LocalVar]): Stmt

  // ----------------------------------------------------------------
  // RENAMING
  // ----------------------------------------------------------------

  def readVarsExp(e: ast.Exp): Set[ast.LocalVar]

  def readVarsDecl(d: ast.Declaration): Seq[ast.LocalVar]

  var currentRenaming: Map[ast.LocalVar, ast.LocalVar]

  def newString(s: String, n: Int = 1): String

  def renameVar(x: ast.LocalVar): ast.LocalVar

  def renameExp(exp: ast.Exp): ast.Exp

  def renameAccPredicate(acc: ast.PredicateAccessPredicate): ast.PredicateAccessPredicate

  def renameDecl(d: sil.Declaration): sil.Declaration

  def renameWand(wand: sil.MagicWand): sil.MagicWand

  def alphaRename(s: ast.Stmt): ast.Stmt

}
