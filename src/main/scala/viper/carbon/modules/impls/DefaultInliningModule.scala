package viper.carbon.modules.impls

import viper.carbon.modules.InliningModule
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import Implicits._
import viper.carbon.modules.components.Component
import viper.silver.ast.{CurrentPerm, ErrorTrafo, FieldAccess, FieldAssign, ForPerm, HasLineColumn, Info, LocalVarAssign, LocationAccess, Method, Position, WildcardPerm}
import viper.silver.verifier.{DummyReason, ErrorMessage, ErrorReason, VerificationError}
import viper.silver.ast.utility.Expressions
import viper.silver.verifier.errors.{ErrorNode, SoundnessFailed}
import viper.silver.ast

import scala.collection.mutable.ListBuffer

/**
 * Handels the inlining of programs.
 */
class DefaultInliningModule(val verifier: Verifier) extends InliningModule with Component {

  import verifier._
  import expModule._
  import heapModule._
  import permModule._

  override def start() {
    // register(this)
  }

  override def reset(): Unit = {}

  val lblNamespace = verifier.freshNamespace("stmt.lbl")
  implicit val namespace = verifier.freshNamespace("inlining")

  def name = "Inlining module"

  /**
   * @param s A Viper statement
   * @return returns the number of Exp's and Stmt's in s. MethodCalls are counted as one and invariants are not
   *         counted.
   */
  def length(s: sil.Stmt): Int = {
    s match {
      case ast.Seqn(ss, _) => ss.foldLeft(0)(_ + length(_))
      case ast.If(_, thn, els) => 1 + length(thn) + length(els)
      case ast.While(_, _, body) => 1 + length(body)
      case _ => 1
    }
  }

  private val maskType = NamedType("MaskType")
  private val heapType = NamedType("HeapType")

  private val smallMask = LocalVarDecl(Identifier("SmallMask"),maskType)
  private val bigMask = LocalVarDecl(Identifier("BigMask"),maskType)
  private val smallerMask = Identifier("SmallerMask")

  private val wfMask = Identifier("wfMask")
  private val normalMask = LocalVarDecl(Identifier("normalMask"),maskType)

  private def lookup(h: Exp, o: Exp, f: Exp) = MapSelect(h, Seq(o, f))
  private val normalHeap: LocalVarDecl = LocalVarDecl(Identifier("normalHeap"), heapType)

  def staticHeap(): Var = {
    heapModule.currentHeap.head.asInstanceOf[Var]
  }

  private val equalOnMask = Identifier("EqualOnMask")
  private val heap1 = LocalVarDecl(Identifier("Heap1"), heapType)
  private val heap2 = LocalVarDecl(Identifier("Heap2"), heapType)

  private val equalOnInter = Identifier("EqualOnIntersection")

  private val smallerState = Identifier("SmallerState")
  private val sumState = Identifier("SumState")
  private val mask1 = LocalVarDecl(Identifier("Mask1"),maskType)
  private val mask2 = LocalVarDecl(Identifier("Mask2"),maskType)
  private val smallHeap = LocalVarDecl(Identifier("SmallHeap"), heapType)
  private val bigHeap = LocalVarDecl(Identifier("BigHeap"), heapType)

  private val axiomNamespace = verifier.freshNamespace("inlining.axiom")

  /** counter used to generate unique temporary argument names */
  private var currentArgInt = 0

  /** counter used to generate unique temporary label names */
  private var currentLabelInt = 0

  /** Counter for the current depth; never decrements; gets incremented when a new level gets inlined */
  var current_depth = 0
  /** Counter for the current number of inlined loops or methods; gets incremented when a loop or method that has not
   * yet been inlined gets inlined (-> not equivalent to depth)*/
  var n_inl = 0

  /** assigns the max depth given by the user to "maxDepth". If no arg is given by user then "maxDepth"==0 */
  def maxDepth: Int = verifier.staticInlining match {
    case None => 0
    case Some(n) => n
  }

  def normalState: (Var, Var) = (permModule.currentMask.head.asInstanceOf[Var], heapModule.currentHeap.head.asInstanceOf[Var])

  // heapModule.freshTempState("").head)

  def silEmptyStmt(): ((Position, Info, ErrorTrafo) => ast.Seqn) = {
    sil.Seqn(Seq(), Seq())
  }

  def silNameNotUsed(s: String): String = {
    if ((mainModule.env.allDefinedVariables() map (_.name)).contains(s)) {
      silNameNotUsed(s + "_r")
    }
    else {
      s
    }
  }

  // ----------------------------------------------------------------
  // CALLSTACK AND ERROR-MESSAGE GENERATION
  // ----------------------------------------------------------------

  /** Set of and loops that are supposed to be printed verbose */
  var verboseSet: Set[Int] = Set()

  /** Name of entry method when verifying a program. Either defined by option verifier.entry or default. */
  var entryMethod: String = ""

  /** gives the inlined loops a unique id to distinguish between inlined loops with same position*/
  var loopEnumerationCounter = 0



  /**
   * Callstack of loops and methods that gets build during inlining. It does not include the entryMethod.
   *
   * Stack of tuples with sil.Stmt's at first and Booleans at second. All sil.Stmt's are either of type sil.WhileInl
   * or sil.MethodCall. The corresponding Boolean is true for sil.WhileInl if stopInlining() is true and is true for
   * sil.MethodCall if stopInlining() is true or if the MethodCall exits.
   *
   * Finished loops and methods build "brackets" around the nested calls inside. For MethodCalls from
   * (sil.MethodCall, false) -> (sil.MethodCall, true) and for loops from (sil.WhileInl(_,id,1), false) to
   * (sil.WhileInl(_,id,_),true). Unfinished loops or methods do not have the second==true "bracket". These "brackets"
   * are used to collapse the callStack for callStackToString().
   */
  private var callStack: ListBuffer[(sil.Stmt, Boolean)] = ListBuffer[(sil.Stmt, Boolean)]()

  /** Gets set to true if n_inl>verifier.maxInl.get and used to print this information in callStackToString() */
  var maxInlineReached: Boolean = false

  /** increments loopEnumerationCounter by 1 */
  def incrementLoopEnumCounter(): Unit = {
    loopEnumerationCounter += 1
  }

  override def copyCallStack(): ListBuffer[(ast.Stmt, Boolean)] = callStack.clone()


  def push(stack: ListBuffer[(sil.Stmt, Boolean)], t : (sil.Stmt, Boolean)) : Unit = {
    stack.prepend(t)
  }

  def top(stack: ListBuffer[(sil.Stmt, Boolean)]) : (sil.Stmt, Boolean) = {
    stack.head
  }

  def pop(stack:ListBuffer[(sil.Stmt, Boolean)]) : (sil.Stmt, Boolean) = {
    var ret = stack.head
    stack.remove(0)
    ret
  }

  /**
   * Pushes tuple onto inlining callStack.
   *
   * @param s sil.Stmt either of type sil.WhileInl or sil.MethodCall.
   * @param end true for s==sil.WhileInl if stopInlining() is true. True for s==sil.Methodcall if stopInlining() is
   *            true or if MethodCall exits.
   */
  def extendCallstack(s : sil.Stmt, end: Boolean = false): Unit = {
    //TODO: simplify if no more changes are made
    s match {
      case wi@sil.WhileInl(_,_,_) =>
        push(callStack,(wi,end))
      case mc@sil.MethodCall(name, args, _) =>
        push(callStack,(mc, end))
      case _ =>
    }
  }

  /**
   * Does not consume the callstack (DefaultInliningModule.callStack) generated during inlining and does
   * not modify any variables.
   *
   * @return returns String of the callstack generated during inlining. If verifier.verboseCallstack.isDefined it will
   *         use the non-collapsed callstack in the return. Otherwise, it will use the collapsed version of the
   *         callStack given by DefaultInliningModule.collapseCallStack().
   */
  def callStackToString() : String = {
    if (verifier.verboseCallstack.isDefined) {
      return callStackToStringVerbose()
    }

    var res = ""
    var collapsedCallstack: ListBuffer[(sil.Stmt, Boolean)] = collapseCallstack(callStack)
    for (call <- collapsedCallstack) {
      call match {
        case (w@sil.WhileInl(_,id,iteration), true) =>
          res = "Loop@" + w.pos.asInstanceOf[HasLineColumn].line +"_id"+id + "; iter.: " + iteration +" (fin.)"+ res
        case (w@sil.WhileInl(_, id, iteration), false) =>
          res = "Loop@"+ w.pos.asInstanceOf[HasLineColumn].line +"_id"+ id +" iteration: " + iteration + res
        case (mc@sil.MethodCall(name,args,_), true) =>
          res = name + "@"+mc.pos.asInstanceOf[HasLineColumn].line+ "(" + args.toString() + ") (fin.)" +/*mc.pos +*/ res
        case (mc@sil.MethodCall(name, args, _), false) =>
          res = name + "@"+mc.pos.asInstanceOf[HasLineColumn].line+ "(" + args.toString() + ")" + /*mc.pos +*/ res
        case _ =>
      }
      res = " -> " + res
    }
    entryMethod + res
  }

  /**
   * Does not consume the callstack (DefaultInliningModule.callStack) generated during inlining and does
   * not modify any variables.
   *
   * @return returns String of the non-collapsed callstack generated during inlining
   */
  def callStackToStringVerbose(): String = {
    var copyCallstack = collapseCallstack(callStack, verboseSet.isEmpty)

    var res: String = ""
    for (call <- copyCallstack){
        call match {
          case (w@sil.WhileInl(_, id, iteration), true) =>
            res = "Loop@" + w.pos.asInstanceOf[HasLineColumn].line + "_id" + id + "; iter.: " + iteration + " (fin.)" + res
          case (w@sil.WhileInl(_, id, iteration),false) =>
            res = "Loop@" + w.pos.asInstanceOf[HasLineColumn].line+ "_id" +id + /*w.pos +*/ "; iter.: " + iteration + res
          case (mc@sil.MethodCall(name, args, _), true) =>
            res = name + "@" + mc.pos.asInstanceOf[HasLineColumn].line + "(" + args.toString() + ") (fin.)" + /*mc.pos +*/ res
          case (mc@sil.MethodCall(name, args, _), false) =>
            res = name + "@"+mc.pos.asInstanceOf[HasLineColumn].line +"(" + args.toString() + ")" + /*mc.pos +*/ res
          case _ =>
        }
      res = " -> " + res

    }
    if (maxInlineReached) {res+= "; maxInline was reached!"}
    entryMethod + res
  }

/* assumes that collapseCallstack ensures that if method or loop finished execution then end is on top of start with
  * no nested loops or methods in between (does not count for entry method) */

  /**
   * requires that there is already some information attached to the elements in what iteration they are and ofc that
   * each the while statements are separate objects
   *
   * @param stack takes the callStack as argument but will not change it
   * @return returns a collapsed version of the callStack. Contains only the last execution of loops and
   *         methods. Any nested loops or methods of finished executions are filtered. Maintains the order of input
   *         stack.
   */
  def collapseCallstack(stack: ListBuffer[(sil.Stmt, Boolean)], verbose: Boolean = false) : ListBuffer[(sil.Stmt, Boolean)] = {
    var stackClone = stack.clone()
    var res: ListBuffer[(sil.Stmt, Boolean)] = ListBuffer[(sil.Stmt, Boolean)]()

    while (stackClone.nonEmpty) {
      var s = top(stackClone)
      s match {
        case (mc@sil.MethodCall(_,_,_), false) =>
        case (w@sil.WhileInl(_,_,1), false) =>
        case (_, _) =>
          collapseCallstackNest(stackClone, verbose)
      }
      pop(stackClone)
      push(res, s)
    }
    res.reverse
  }

  /**
   * All nested elements get removed form the input stack by using the start/end "brackets" of var callStack. Only the
   * end "bracket" will remain in the stack.
   *
   * @param stack partial callStack of which _2 of the top element is true or if false then _1 is of type sil.WhileInl
   *              and the iteration number of sil.WhileInl is greater 1. This means that top is either a finished
   *              execution of a MethodCall or Loop, or an unfinished loop with more than one iteration.
   *              Input stack may not be empty. Assumes that all MethodCalls in the input stack have finished their
   *              execution and start and end are contained in input stack. Assumes that if _1 is of type WhileInl
   *              with id ID and some iteration number it then there exist another element in the
   *              stack of type WhileInl with id==ID and iteration==1.
   * @param verbose verbose is true if inliningModule.verboseCallstack.isDefined and the user has not defined any loops
   *                or methods that are not supposed to be collapsed, meaning verboseSet==Set() => collapse nothing
   */
  def collapseCallstackNest(stack: ListBuffer[(sil.Stmt, Boolean)], verbose:Boolean) : Unit = {
    assert(stack.nonEmpty)

    var s = pop(stack)

    if (stack.nonEmpty && !verbose && collapse(s)) {
      var next = top(stack)

      s._1 match {
        case sil.WhileInl(_, id, iteration) =>
          if (iteration > 1) {
            if (!containsVerboseSetElem(stack, s)) {
              var contin: Boolean = true
              while (contin && stack.nonEmpty) {
                next = top(stack)
                next._1 match {
                  case sil.WhileInl(_, nextID, nextIteration) =>
                    if (id == nextID && nextIteration == 1) {
                      contin = false
                    }
                  case _ =>
                }
                pop(stack)
              }
            }
          }
          else {
            pop(stack)
          }
        case mc@sil.MethodCall(_, _, _) =>
          if (!containsVerboseSetElem(stack, s)) {
            while (next._1 != mc) {
              pop(stack)
              next = top(stack)
            }
            pop(stack)
          }
        case _ =>
      }
    }
    push(stack,s)
  }

  /**
   * true if the user has not defined the loop or method statement in s._1 to be verbose
   */
  def collapse(s: (sil.Stmt, Boolean)) : Boolean = {
    s._1 match {
      case sil.MethodCall(methodName, args, targets) =>
        !verboseSet.contains(verifier.program.findMethod(methodName).pos.asInstanceOf[HasLineColumn].line)
      case wi@sil.WhileInl(w, id, iteration) =>
        !verboseSet.contains(wi.pos.asInstanceOf[HasLineColumn].line)
      case _ => false
    }
  }

  /**
   * @param stack partial callStack
   * @param top element of stack that was popped of before
   * @return true if a While loop or MethodCall that is about to be collapsed has a nested a method or loop during
   *         executions that is contained in VerboseSet and is not supposed to be collapsed
   */
  def containsVerboseSetElem(stack: ListBuffer[(sil.Stmt, Boolean)], top: (sil.Stmt,Boolean)) : Boolean = {
    for (i <- stack) {
      i._1 match {
        case sil.WhileInl(_, _, _) =>
          if (verboseSet.contains(i._1.pos.asInstanceOf[HasLineColumn].line))
            return true
        case sil.MethodCall(methodName, _, _) =>
          if (verboseSet.contains(verifier.program.findMethod(methodName).pos.asInstanceOf[HasLineColumn].line))
            return true
        case _ =>
      }
      top._1 match {
        case sil.WhileInl(_, id, _) =>
          i._1 match {
            case sil.WhileInl(_, idN, itN) =>
              if (id == idN && itN == 1)
                return false
            case _ =>
          }
        case mc@sil.MethodCall(_,_,_) =>
          if (top._1==mc)
            return false
        case _ =>
      }
    }
    false
  }

  /**
    * Only gets called if staticInlining is active. The method will add information about the confidence level of an
    * error. If there is no soundness check error then the readable massage of all errors in the errormap with their key
    * as element of errorIds will be extended with the message that the confidence level is high. Otherwise the
    * readable message of the errors in the errormap with their key as element of errorIds will be extended with the
    * message that the confidence level is low. The soundness check errors themselves do not have a confidence level.
    *
    * @param errorIds    The sequence of boogie error ids that failed the assertion.
    * @param oldErrormap the errormap that needs to be updated TODO: what is contained in the errormap
    * @return returns a new errormap with the modifications to oldErrormap
    */
  def soundnessCheckConfidenceTransformation(errorIds: Seq[Int], oldErrormap: Map[Int, VerificationError]): Map[Int, VerificationError] = {
    var errormap: Map[Int, VerificationError] = oldErrormap
    var lowConfidence = false
    for (id <- errorIds) {
      val error = errormap.get(id).get
      val scError = error.readableMessage.contains("MONO ") || error.readableMessage.contains("FRAMING ") ||
        error.readableMessage.contains("WFM ")
      if (scError) {
        lowConfidence = true
      }
      errormap += (id -> new VerificationError {
        val conf = lowConfidence
        override def reason: ErrorReason = error.reason
        override def readableMessage(withId: Boolean, withPosition: Boolean): String = (error.readableMessage + {
          if (scError) "" else if (conf) " Low confidence that real error." else " High confidence that real error."
        })
        override def id: String = error.id
        override def offendingNode: ErrorNode = error.offendingNode
        override def pos: Position = error.pos
        override def withNode(offendingNode: ErrorNode): ErrorMessage = error.withNode()
      })
    }
    errormap
  }


  // ----------------------------------------------------------------
  // MATCH DETERMINISM
  // ----------------------------------------------------------------

  var recordedScopes: Seq[Seq[sil.LocalVar]] = Seq()

  var altExists: Seq[sil.LocalVar] = Seq()
  var altExistsAll: Set[sil.LocalVar] = Set()

  // Record the values of variables at the beginning of scopes, and ensure return variables are the same (neither sound nor complete)
  def recordVarsSil(s: sil.Stmt, exists: sil.LocalVar): sil.Stmt = {
    val a = s.pos
    val b = s.info
    val c = s.errT
    s match {
      case sil.Seqn(ss, scopedDecls) =>
        val locals: Seq[ast.LocalVarDecl] = scopedDecls.collect { case l: sil.LocalVarDecl => l }
        val tempVars: Seq[ast.LocalVar] = locals map ((x: ast.LocalVarDecl) => {
          val name = silNameNotUsed(x.localVar.name + "_temp")
          val tempLocalVar = sil.LocalVar(name, x.localVar.typ)(x.pos, x.info, x.errT)
          mainModule.env.define(tempLocalVar)
          tempLocalVar
        })
        recordedScopes :+= tempVars
        val assign: Seq[LocalVarAssign] = (tempVars zip locals) map { (x: (sil.LocalVar, sil.LocalVarDecl)) => sil.LocalVarAssign(x._1, x._2.localVar)(a, b, c) }
        sil.Seqn(assign ++ ss map (recordVarsSil(_, exists)), scopedDecls)(a, b, c)
      // case sil.Inhale(exp) if (exp.isPure) => sil.LocalVarAssign(exists, sil.And(exists, exp)(exp.pos, exp.info, exp.errT))(a, b, c)
      // Assume
      case sil.MethodCall(methodName, args, targets: Seq[ast.LocalVar]) if program.findMethod(methodName).body.isEmpty =>
        // Abstract method
        val tempRets: Seq[ast.LocalVar] = targets map ((x: ast.LocalVar) => {
          val name = silNameNotUsed(x.name + "_temp")
          val tempLocalVar = sil.LocalVar(name, x.typ)(x.pos, x.info, x.errT)
          mainModule.env.define(tempLocalVar)
          tempLocalVar
        })

        // recordedScopes :+= tempArgs
        recordedScopes :+= tempRets
        // val assignArgs: Seq[LocalVarAssign] = (tempArgs zip args) map { (x: (sil.LocalVar, sil.Exp)) => sil.LocalVarAssign(x._1, x._2)(a, b, c) }
        val assignRets: Seq[LocalVarAssign] = (tempRets zip targets) map { (x: (sil.LocalVar, sil.LocalVar)) => sil.LocalVarAssign(x._1, x._2)(a, b, c) }

        val existAlter: ast.LocalVarDecl = sil.LocalVarDecl(silNameNotUsed("__altExists"), sil.Bool)(a, b, c)
//         val existAlter: sil.LocalVar = getVarDecl("altExists", Bool).l
        altExists :+= existAlter.localVar
        altExistsAll += existAlter.localVar

        val assignExists: sil.LocalVarAssign = sil.LocalVarAssign(existAlter.localVar, exists)(a, b, c)

        val ifAssignRets = sil.If(existAlter.localVar, sil.Seqn(assignRets, Seq())(a, b, c), sil.Seqn(Seq(), Seq())(a, b, c))(a, b, c)

        // sil.Seqn(assignArgs ++ Seq(assignExists, s, ifAssignRets), Seq(existAlter))(a, b, c)
        sil.Seqn(Seq(assignExists, s, ifAssignRets), Seq(existAlter))(a, b, c)
      case sil.If(cond, s1: sil.Seqn, s2: sil.Seqn) =>
        val ss1 = recordVarsSil(s1, exists).asInstanceOf[sil.Seqn]
        val ss2 = recordVarsSil(s2, exists).asInstanceOf[sil.Seqn]
        sil.If(cond, ss1, ss2)(a, b, c)
      case _ => s
    }
  }

  def assignVarsSil(s: sil.Stmt, exists: sil.LocalVar): sil.Stmt = {
    val a = s.pos
    val b = s.info
    val c = s.errT
    s match {
      case sil.Seqn(ss, scopedDecls) =>
        val locals: Seq[ast.LocalVarDecl] = scopedDecls.collect { case l: sil.LocalVarDecl => l }
        val tempVars: Seq[ast.LocalVar] = recordedScopes.head
        assert(locals.size == tempVars.size)
        recordedScopes = recordedScopes.tail
        val assign: Seq[LocalVarAssign] = (locals zip tempVars) map { (x: (sil.LocalVarDecl, sil.LocalVar)) => sil.LocalVarAssign(x._1.localVar, x._2)(a, b, c) }
        // val if_assign: ast.Stmt = sil.If(check, sil.Seqn(assign, Seq())(a, b, c), silEmptyStmt()(a, b, c))(a, b, c)
        sil.Seqn(assign ++ ss map (assignVarsSil(_, exists)), scopedDecls)(a, b, c)
      case sil.MethodCall(methodName, args, targets: Seq[ast.LocalVar]) if program.findMethod(methodName).body.isEmpty
        // && program.findMethod(methodName).pres.isEmpty
       =>
        /*
        val tempArgs: Seq[ast.LocalVar] = recordedScopes.head
        recordedScopes = recordedScopes.tail
         */
        val tempRets: Seq[ast.LocalVar] = recordedScopes.head
        recordedScopes = recordedScopes.tail
        // assert(args.size == tempArgs.size)
        assert(targets.size == tempRets.size)

        // We need to make sure the arguments from the two method calls are the same, with a boolean variable
        // Actually no
        /*
        val same_seq: Seq[sil.Exp] = (tempArgs zip args) map { (x: (sil.LocalVar, sil.Exp)) => sil.EqCmp(x._1, x._2)(a, b, c) }
        val same_args_name = silNameNotUsed("sameArgs")
        val same_args: ast.LocalVar = sil.LocalVar(same_args_name, sil.Bool)(a, b, c)
        mainModule.env.define(same_args)
        val same_args_true: LocalVarAssign = LocalVarAssign(same_args, sil.TrueLit()(a, b, c))(a, b, c)
        val assign_same_args: Seq[LocalVarAssign] = same_seq map ((exp: sil.Exp) => sil.LocalVarAssign(same_args, sil.And(same_args, exp)(a, b, c))(a, b, c))
         */

        // val assign: Seq[LocalVarAssign] = (tempRets zip targets) map { (x: (sil.LocalVar, sil.LocalVar)) => sil.LocalVarAssign(x._2, x._1)(a, b, c) }
        val assign: Seq[sil.Stmt] = (tempRets zip targets) map { (x: (sil.LocalVar, sil.LocalVar)) => sil.Inhale(sil.EqCmp(x._1, x._2)(a, b, c))(a, b, c) }
        // val if_assign: ast.Stmt = sil.If(same_args, sil.Seqn(assign, Seq())(a, b, c), sil.Seqn(Seq(), Seq())(a, b, c))(a, b, c)
        // sil.Seqn(Seq(same_args_true) ++ assign_same_args ++ Seq(s) ++ Seq(if_assign), Seq())(a, b, c)
        sil.Seqn(Seq(s) ++ assign, Seq())(a, b, c)
      case sil.If(cond, s1, s2) =>
        val ss1 = assignVarsSil(s1, exists).asInstanceOf[sil.Seqn]
        val ss2 = assignVarsSil(s2, exists).asInstanceOf[sil.Seqn]
        sil.If(cond, ss1, ss2)(a, b, c)
      case _ => s
    }
  }


  var id_checkVar = 0
  var checkVar = getVarDecl("checkFraming", Int)

  def getCheckBool(): (Exp, Int) = {
    id_checkVar += 1
    (checkVar.l === IntLit(id_checkVar), id_checkVar)
  }

  var declareFalseAtBegin: Seq[LocalVarDecl] = Seq()

  // TODO: Improve
  def remove_assume_false(s: Stmt): Stmt = {
    s match {
      case Seqn(stmts) => Seqn(stmts.dropRight(1) ++ Seq(remove_assume_false(stmts.last)))
      case Assume(FalseLit()) => Statements.EmptyStmt
      case If(cond, thn, els) => assert(els.toString() == "")
        assert(cond.toString.contains("vexists"))
        If(cond, remove_assume_false(thn), els)
      case _ => s // Unknown, shouldn't happen
    }
  }

  def handleFunctionPrecondition(s: Stmt): Stmt = {
      val beforeMask = getVarDecl("beforeMask", maskType)
      val beforeHeap = getVarDecl("beforeHeap", heapType)
      MaybeComment("Record state before", Assign(beforeMask.l, normalState._1) ++ Assign(beforeHeap.l, normalState._2)) ++
      remove_assume_false(s) ++
      MaybeComment("Back to the former state", Assign(normalState._1, beforeMask.l) ++ Assign(normalState._2, beforeHeap.l))
  }

  /**
   *  Records:
   *  - exhale heaps
   *  - wildcard values
   *  - new version of predicates unfolded (?)
   *  - values of "freshObj"
  */
  def recordDeterminism(s: Stmt): (Stmt, Seq[LocalVarDecl]) = {
    s match {
      case Seqn(stmts) => val r = (stmts map recordDeterminism)
        (Seqn(r map (_._1)), r flatMap (_._2))
      case Assume(BinExp(v: LocalVar, LtCmp, right)) if (v.name.name == "wildcard") =>
        // Exhale wildcard
        // val w = newWildcard()
        val b = getVarDecl("BranchTakenForWildcard", Bool)
        declareFalseAtBegin :+= b
        val w = getVarDecl("wildcard", permType)
        val p = getVarDecl("permwild", permType)
        val noPerm = BinExp(IntLit(0), Div, IntLit(1))
        (Assign(b.l, TrueLit()) ++ Assign(w.l, v) ++ Assign(p.l, right) ++ s, Seq(b, w, p))
      case CommentBlock(c, ss) =>
        val (sss, l) = recordDeterminism(ss)
        (CommentBlock(c, sss), l)
      case If(cond, thn, els) =>
        val (nthn, l1) = recordDeterminism(thn)
        val (nels, l2) = recordDeterminism(els)
        (If(cond, nthn, nels), l1 ++ l2)
      case Assign(LocalVar(Identifier("perm", n1), typ1), v: LocalVar) if (v.name.name == "wildcard") =>
        // val w = newWildcard()
        val w = getVarDecl("wildcard", permType)
        (Assign(w.l, v) ++ s, Seq(w))
      case NondetIf(thn, els) =>
        if (!verifier.pureFunctionsSC) {
          assert(els.toString() == "")
          (handleFunctionPrecondition(thn), Seq())
        }
        else {
          (s, Seq())
        }
      case HavocImpl(Seq(v)) =>
        if (v.name.name == "ExhaleHeap") {
          val b = getVarDecl("BranchTakenForExhale", Bool)
          declareFalseAtBegin :+= b
          val pre = getVarDecl("PreExhaleHeap", heapType)
          val preMask = getVarDecl("PreExhaleMask", maskType)
          val h = getVarDecl("ExhaleHeap", heapType)
          (Seqn(Seq(Assign(b.l, TrueLit()), Assign(pre.l, currentHeap.head), Assign(preMask.l, currentMask.head), s, Assign(h.l, v))), Seq(b, pre, preMask, h))
        }
        else if (v.name.name == "newVersion") {
          // val nv = newVar(v.typ)
          val nv = getVarDecl("newVersion", v.typ)
          (Seqn(Seq(s, Assign(nv.l, v))), Seq(nv))
        }
        else if (v.name.name == "freshObj") {
          // val obj = newFreshObj()
          val obj = getVarDecl("freshObj", refType)
          (Seqn(Seq(s, Assign(obj.l, v))), Seq(obj))
        }
        else {
          (s, Seq())
        }
      case ss => (ss, Seq())
    }
  }

  def conditionToAvoid(cond: Exp, id_check: Int): Boolean = {
    cond match {
      case BinExp(e1, Implies, _) => conditionToAvoid(e1, id_check)
      case BinExp(e1, And, _) => conditionToAvoid(e1, id_check)
      case BinExp(v: LocalVar, EqCmp, IntLit(i)) => v.name == checkVar.l.name && i != id_check
      case _ => false
    }
  }

  def determinize(s: Stmt, l: Seq[LocalVarDecl], check: Exp, id_check: Int, e: VerificationError): (Stmt, Seq[LocalVarDecl]) = {
    s match {
      case Seqn(stmts) =>
        var new_s: Seq[Stmt] = Seq()
        var ll = l
        for (ss <- stmts) {
          val (sss, lll) = determinize(ss, ll, check, id_check, e)
          ll = lll
          new_s = new_s :+ sss
        }
        (Seqn(new_s), ll)
      case CommentBlock(c, ss) =>
        val (sss, ll) = determinize(ss, l, check, id_check, e)
        (CommentBlock(c, sss), ll)
      case Assume(BinExp(w: LocalVar, LtCmp, right)) if (w.name.name == "wildcard") =>
        val b = l.head
        val old_w = l.tail.head
        val p = l.tail.tail.head

        val s1 = Assert(right >= p.l, e)
        val s2 = Assume(right - w >= p.l - old_w.l)

        (If(b.l, s1 ++ s2, s), l.tail.tail.tail)
      case If(cond, thn, els) =>
        val (nthn, l1) = determinize(thn, l, check, id_check, e)
        val (nels, l2) = determinize(els, l1, check, id_check, e)
        (If(cond, nthn, nels), l2)
      case Assign(LocalVar(Identifier("perm", n1), typ1), v: LocalVar) if (v.name.name == "wildcard") =>
        // Inhale wildcard
        (Assign(v, l.head.l) ++ s, l.tail)
      case HavocImpl(Seq(v)) =>
        if (v.name.name == "freshObj" || v.name.name == "newVersion") {
          val ss = Assume(v === l.head.l)
          (s ++ ss, l.tail)
        }
        else if (v.name.name == "ExhaleHeap") {
          val b = l.head
          val pre = l.tail.head
          val preMask = l.tail.tail.head
          val h = l.tail.tail.tail.head
          /*val ss = If(check,
            Assert(b.l ==> (pre.l === currentHeap.head), e) ++
              Assume(v === h.l), Statements.EmptyStmt)
           */
          val ss = If(b.l,
            Assert(
              equalOnMaskFunc(pre.l, currentHeap.head.asInstanceOf[Var], preMask.l)
                //currentMask.head.asInstanceOf[Var])
              //pre.l === currentHeap.head
            , e) ++
              Assume(v === h.l), Statements.EmptyStmt)
          (s ++ ss, l.tail.tail.tail.tail)
        }
        else {
          (s, l)
        }
      case _ => (s, l)
    }
  }

  var id_var_deter: Int = 0
  private val deter_namespace: Namespace = verifier.freshNamespace("determinism")

  def getVarDecl(name: String, typ: Type): LocalVarDecl = {
    id_var_deter += 1
    LocalVarDecl(Identifier("varTemp_" + id_var_deter + "_" + name)(deter_namespace), typ)
  }

  // ----------------------------------------------------------------
  // CHECK SOUNDNESS CONDITION
  // ----------------------------------------------------------------

  // Only changes "assume state" into "exists := exists && wfState"
  def changeStateWfState(s: Stmt, exists: LocalVar): Stmt = {
    s match {
      case Seqn(stmts) => stmts map (changeStateWfState(_, exists))
      case Assume(FuncApp(Identifier("state", namespace), args, typ)) =>
        Assign(exists, exists && wfMask(args.tail, typ))
      case CommentBlock(c, ss) =>
        CommentBlock(c, changeStateWfState(ss, exists))
      case If(cond, thn, els) => If(cond, changeStateWfState(thn, exists), changeStateWfState(els, exists))
      case NondetIf(thn, els) => NondetIf(changeStateWfState(thn, exists), changeStateWfState(els, exists))
      case ss => ss
    }
  }

  def addIfExists(s: Stmt, exists: LocalVar): Stmt = {
    s match {
      case Seqn(stmts) => stmts map (addIfExists(_, exists))
      case CommentBlock(c, ss) =>
        CommentBlock(c, addIfExists(ss, exists))
      case If(cond: LocalVar, thn, els) if cond.name.name.startsWith("__altExists") => If(cond, thn, addIfExists(els, exists))
      case If(cond, thn, els) => If(cond, addIfExists(thn, exists), addIfExists(els, exists))
      case NondetIf(thn, els) => NondetIf(addIfExists(thn, exists), addIfExists(els, exists))
      case ss => If(exists, ss, Statements.EmptyStmt)
    }
  }

  def containsPermOrForperm(exp: sil.Exp): Boolean = {
    exp.contains[ForPerm] || exp.contains[CurrentPerm]
  }

  def containsAcc(exp: sil.Exp): Boolean = {
    exp.contains[LocationAccess]
  }

  def containsWildcard(exp: sil.Exp): Boolean = {
    exp.contains[WildcardPerm]
  }

  def syntacticFraming(s: sil.Stmt, checkMono: Boolean = false): Boolean = {
    if (verifier.noSyntacticCheck) {
      false
    }
    else {
      s match {
        case ast.LocalVarAssign(_, rhs) => !containsPermOrForperm(rhs)
        case ast.FieldAssign(ast.FieldAccess(rcv, _), rhs) => !containsPermOrForperm(rcv) && !containsPermOrForperm(rhs)
        case ast.MethodCall(methodName, args, _) =>
          val method = verifier.program.findMethod(methodName)
          (args forall (!containsPermOrForperm(_))) && method.body.isEmpty &&
            method.posts.forall(!containsPermOrForperm(_)) &&
            method.pres.forall(exp => !containsPermOrForperm(exp) && (!containsWildcard(exp) || checkMono))
        case ast.Exhale(exp) => !containsPermOrForperm(exp) && (!containsWildcard(exp) || checkMono)
        case ast.Inhale(exp) => !containsPermOrForperm(exp)
        case ast.Assert(exp) => !containsPermOrForperm(exp)
        case ast.Assume(exp) => !containsPermOrForperm(exp) && !containsAcc(exp)
        case sil.Fold(acc) => !containsPermOrForperm(acc) && !containsWildcard(acc) &&
          !containsWildcard(acc.loc.predicateBody(verifier.program, mainModule.env.allDefinedNames(program)).get)
        case ast.Unfold(acc) => !containsPermOrForperm(acc) && !containsWildcard(acc)
        case ast.Package(_, proofScript) => syntacticFraming(proofScript, checkMono)
        case ast.Apply(_) => true
        case ast.Seqn(ss, _) => ss forall (syntacticFraming(_, checkMono))
        case ast.If(cond, thn, els) => !containsPermOrForperm(cond) && syntacticFraming(thn, checkMono) && syntacticFraming(els, checkMono)
        case ast.While(cond, invs, body) => assert(false); false // This should not happen
        case ast.Label(_, _) => true
        case ast.Goto(_) =>
          println("Warning: goto statements are only partially supported")
          false
        case ast.NewStmt(lhs, fields) => true
        case ast.LocalVarDeclStmt(decl) => true
        case ast.WhileInl(_,_,_) =>
          assert(false); false //should not happen
        case _: ast.ExtensionStmt =>
          assert(false); false // This should not happen
      }
    }
  }

  def wfMask(args: Seq[Exp], typ: Type = Bool): Exp = FuncApp(wfMask, args, typ)
  def equalOnMaskFunc(heap1: Var, heap2: Var, mask: Var): Exp = FuncApp(equalOnMask, Seq(heap1, heap2, mask), Bool)
  def equalOnInterFunc(heap1: Var, heap2: Var, mask1: Var, mask2: Var): Exp = FuncApp(equalOnInter, Seq(heap1, heap2, mask1, mask2), Bool)


  def sumMasksFunc(mask1: Var, mask2: Var, mask: Var): Exp = {
    FuncApp(sumMasks, Seq(mask1, mask2, mask), Bool)
  }

  def sumStateNormal(mask1: Var, heap1: Var, mask2: Var, heap2: Var, mask: Var, heap: Var): Exp = {
    FuncApp(sumState, Seq(mask1, heap1, mask2, heap2, mask, heap), Bool)
  }

  def smallerState(smallMask: Var, smallHeap: Var, bigMask: Var, bigHeap: Var): Exp = {
    FuncApp(smallerState, Seq(smallMask, smallHeap, bigMask, bigHeap), Bool)
  }

  def smallerMask(smallMask: Var, bigMask: Var): Exp = {
    FuncApp(smallerMask, Seq(smallMask, bigMask), Bool)
  }

  def doubleErrorSafeMono(s: Stmt, orig: sil.Stmt, id_error: Int, type_error: String, check: Exp, id_check: Int): Stmt = {
    s match {
      case Seqn(stmts) => stmts map (doubleErrorSafeMono(_, orig, id_error, type_error, check, id_check))
      case CommentBlock(c, ss) => CommentBlock(c, doubleErrorSafeMono(ss, orig, id_error, type_error, check, id_check))
      // case If(cond: LocalVar, thn, els) if (used_checks.contains(cond.name.name) && cond.name.name != check.name.name) =>
      case If(cond, thn, els) if conditionToAvoid(cond, id_check) =>
        If(cond, thn, doubleErrorSafeMono(els, orig, id_error, type_error, check, id_check))
      case If(cond, thn, els) => If(cond, doubleErrorSafeMono(thn, orig, id_error, type_error, check, id_check), doubleErrorSafeMono(els, orig, id_error, type_error, check, id_check))
      case NondetIf(thn, els) => NondetIf(doubleErrorSafeMono(thn, orig, id_error, type_error, check, id_check), doubleErrorSafeMono(els, orig, id_error, type_error, check, id_check))
      // case Assert(BinExp(e1, Implies,  _), _) if conditionToAvoid(e1, id_check) => s
      case Assert(exp, old_error) =>
        val nsm: VerificationError = SoundnessFailed(orig, DummyReason, "safeMono", id_error, type_error, old_error.toString)
        Assert(exp, nsm)
      case _ => s
    }
  }

  def assumify(s: Stmt): Stmt = {
    s match {
      case Seqn(stmts) => stmts map assumify
      case CommentBlock(c, ss) => CommentBlock(c, assumify(ss))
      case If(cond, thn, els) => If(cond, assumify(thn), assumify(els))
      case NondetIf(thn, els) => NondetIf(assumify(thn), assumify(els))
      case Assert(exp, _) => Assume(exp)
      case ss => ss
    }
  }

  var checkingFraming: Boolean = false

  def isCheckingFraming(): Boolean = {
    (checkingFraming || verifier.noCheckSC)
  }

  def assignSeqToSeq(s1: Seq[Var], s2: Seq[Var]): Stmt = {
    (s1, s2) match {
      case (Seq(), _) => Statements.EmptyStmt
      case (_, Seq()) => Statements.EmptyStmt
      case (Seq(a1, b1@_*), Seq(a2, b2@_*)) => Assign(a1, a2) ++ assignSeqToSeq(b1, b2)
    }
  }

  /**
    * Creates an expression that can be evaluated to checks the equality of two boogie variable sequences.
    *
    * @param s1 A sequence of boogie variables.
    * @param s2 A sequence of boogie variables.
    * @return Returns a true literal if either s1 or s2 is a empty sequence and otherwise returns a
    *         conjunction of equalities of the elements of s1 and s2 with the same index by applying itself recursively.
    */
  def equalSeq(s1: Seq[Var], s2: Seq[Var]): Exp = {
    (s1, s2) match {
      case (Seq(), _) => TrueLit()
      case (_, Seq()) => TrueLit()
      case (Seq(a1, b1@_*), Seq(a2, b2@_*)) => a1 === a2 && equalSeq(b1, b2)
    }
  }

  def currentPermission(mask: Exp, rcv: Exp, location: Exp): MapSelect = {
    MapSelect(mask, Seq(rcv, location))
  }

  /**
    * @return Defines the functions and axioms necessary for the soundness condition checks in the generated boogie file.
    */
  def getAxioms(): List[Decl] = {
    val obj: LocalVarDecl = LocalVarDecl(Identifier("o")(axiomNamespace), refType)
    val field = LocalVarDecl(Identifier("f")(axiomNamespace), fieldType)
    val smallerMaskArgs = Seq(smallMask, bigMask)
    val smallerMaskApp = FuncApp(smallerMask, smallerMaskArgs map (_.l), Bool)
    val permSmall = currentPermission(smallMask.l, obj.l, field.l)
    val permBig = currentPermission(bigMask.l,obj.l,field.l)

    val wfMaskArgs = Seq(normalMask)
    val wfMaskApp = FuncApp(wfMask, wfMaskArgs map (_.l), Bool)
    val perm = currentPermission(normalMask.l, obj.l, field.l)

    val equalOnArgs = Seq(heap1, heap2, normalMask)
    val equalOnApp = FuncApp(equalOnMask, equalOnArgs map (_.l), Bool)
    val lookup1 = lookup(heap1.l, obj.l, field.l)
    val lookup2 = lookup(heap2.l, obj.l, field.l)

    val equalOnInterArgs = Seq(heap1, heap2, mask1, mask2)
    val equalOnInterApp = FuncApp(equalOnInter, equalOnInterArgs map (_.l), Bool)
    val perm1 = currentPermission(mask1.l, obj.l, field.l)
    val perm2 = currentPermission(mask2.l, obj.l, field.l)

    val smallerStateArgs = Seq(smallMask, smallHeap, bigMask, bigHeap)
    val smallerStateApp = FuncApp(smallerState, smallerStateArgs map (_.l), Bool)

    val sumStateArgs = Seq(mask1, heap1, mask2, heap2, normalMask, normalHeap)
    val sumStateApp = FuncApp(sumState, sumStateArgs map (_.l), Bool)
    val sumMaskApp = FuncApp(sumMasks, Seq(normalMask, mask1, mask2) map (_.l), Bool)

/*
    MaybeCommentedDecl("Frame all locations with direct permissions", Axiom(Forall(
      vars ++ Seq(obj, field),
      //        Trigger(Seq(identicalFuncApp, lookup(h.l, obj.l, field.l))) ++
      Trigger(Seq(identicalFuncApp, lookup(eh.l, obj.l, field.l))),
      identicalFuncApp ==>
        (staticPermissionPositive(obj.l, field.l) ==>
          (lookup(h.l, obj.l, field.l) === lookup(eh.l, obj.l, field.l)))
    )), size = 1) ++

 */

    MaybeCommentedDecl("CHECK SOUNDNESS CONDITION",
      Func(smallerMask, smallerMaskArgs, Bool) ++
        Axiom(Forall(
          smallerMaskArgs,
          Trigger(smallerMaskApp),
          smallerMaskApp <==>
            Forall(
              Seq(obj, field),
              Trigger(Seq(permSmall)) ++ Trigger(Seq(permBig)),
              permSmall <= permBig,
              field.typ.freeTypeVars)
        )) ++
        Func(wfMask, wfMaskArgs, Bool) ++
        Axiom(Forall(
          wfMaskArgs,
          Trigger(wfMaskApp),
          wfMaskApp <==>
            Forall(obj ++ field,
              Trigger(Seq(perm)),
              (perm >= noPerm && ((heapModule.isPredicateField(field.l).not && heapModule.isWandField(field.l).not) ==> perm <= fullPerm)),
              field.typ.freeTypeVars)
        )) ++
        Func(equalOnMask, equalOnArgs, Bool) ++
        Axiom(Forall(
          equalOnArgs,
          Trigger(equalOnApp),
          equalOnApp <==>
            Forall(obj ++ field,
              Trigger(Seq(lookup1)) ++ Trigger(Seq(lookup2)),
              perm > noPerm ==> (lookup1 === lookup2),
              field.typ.freeTypeVars)
        )) ++
        Func(equalOnInter, equalOnInterArgs, Bool) ++
        Axiom(Forall(
          equalOnInterArgs,
          Trigger(equalOnInterApp),
          equalOnInterApp <==>
            Forall(obj ++ field,
              Trigger(Seq(lookup1)) ++ Trigger(Seq(lookup2)) ++ Trigger(Seq(perm1)) ++ Trigger(Seq(perm2)),
              (perm1 > noPerm && perm2 > noPerm) ==> (lookup1 === lookup2),
              field.typ.freeTypeVars)
        )) ++
      Func(smallerState, smallerStateArgs, Bool) ++
      Axiom(Forall(
        smallerStateArgs,
        Trigger(smallerStateApp),
        smallerStateApp <==> (smallerMaskApp &&
          FuncApp(equalOnMask, Seq(smallHeap.l, bigHeap.l, smallMask.l), Bool)
          ))) ++
      Func(sumState, sumStateArgs, Bool) ++
      Axiom(Forall(
        sumStateArgs,
        Trigger(sumStateApp),
        sumStateApp <==> (sumMaskApp
          && FuncApp(equalOnMask, Seq(normalHeap.l, heap1.l, mask1.l), Bool)
          && FuncApp(equalOnMask, Seq(normalHeap.l, heap2.l, mask2.l), Bool)
          ))))
  }

  var current_exists: Option[Var] = None
  var id_checkFraming = 0
  var id_checkMono = 0
  var id_checkWfm = 0

  var first_block: Boolean = true

  /** Distinguishes Mono and Framing. Small optimization since initial method does not have to be framing. */
  var inside_initial_method = true

  val getBounded = getVarDecl("getBounded", Bool)

  def getBoundedComplete(): Stmt = {
    if (isCheckingFraming() || !closureSC) {
      Statements.EmptyStmt
    }
    else {
      val mask = getVarDecl("boundedMask", maskType)
      val r: Seq[Stmt] = Assume(smallerMask(mask.l, normalState._1)) ++
        Assume(wfMask(Seq(mask.l))) ++
        Assign(normalState._1, mask.l)
      If(getBounded.l, r, Statements.EmptyStmt)
    }
  }

  var recordingSil = false
  var assigningSil = false

  def inlineSilAux(s: sil.Stmt, n: Int): sil.Stmt = {

    val (a, b, c) = (s.pos, s.info, s.errT)
    s match {
      case sil.MethodCall(methodName, args, targets) if program.findMethod(methodName).body.isDefined =>
        if (n > 0) {
          val m = program.findMethod(methodName)
          val pre_body = m.body.get

          val oldInRenaming = inRenaming
          inRenaming = Set()
          val body = alphaRename(pre_body)

          namesAlreadyUsed ++= read(body)

          val renamedFormalArgsVars: Seq[sil.LocalVar] = (m.formalArgs map (_.localVar)) map renameVar

          namesAlreadyUsed ++= renamedFormalArgsVars

          val renamedFormalReturnsVars: Seq[ast.LocalVar] = (m.formalReturns map (_.localVar)) map renameVar
          namesAlreadyUsed ++= renamedFormalReturnsVars

          val scopeArgs: Seq[ast.LocalVarDecl] = renamedFormalArgsVars map (x => sil.LocalVarDecl(x.name, x.typ)(a, b, c))
          val scopeRets: Seq[ast.LocalVarDecl] = renamedFormalReturnsVars map (x => sil.LocalVarDecl(x.name, x.typ)(a, b, c))

          val inlined_m: ast.Stmt = inlineSilAux(body, n - 1)

          val assignArgsPre: Seq[(sil.LocalVar, sil.Exp)] = (renamedFormalArgsVars zip args) filter ((x) => x._1 != x._2)
          val assignRetsPre: Seq[(sil.LocalVar, sil.Exp)] = (targets zip renamedFormalReturnsVars) filter ((x) => x._1 != x._2)
          val assignArgs: Seq[sil.LocalVarAssign] = assignArgsPre map (x => sil.LocalVarAssign(x._1, x._2)(a, b, c))
          val assignRets: Seq[sil.LocalVarAssign] = assignRetsPre map (x => sil.LocalVarAssign(x._1, x._2)(a, b, c))

          inRenaming = oldInRenaming

          sil.Seqn(assignArgs ++ Seq(inlined_m) ++ assignRets, scopeArgs ++ scopeRets)(a, b, c)
        }
        else {
          sil.Inhale(sil.FalseLit()(a, b, c))(a, b, c)
        }
      case sil.While(cond, invs, body) =>
        if (n > 0) {
          val s_inl: sil.Stmt = inlineSilAux(body, n - 1)
          val w_inl: sil.Stmt = inlineSilAux(s, n - 1)
          val seq: sil.Seqn = sil.Seqn(Seq(s_inl, w_inl), Seq())(a, b, c)
          val empty: sil.Seqn = sil.Seqn(Seq(), Seq())(a, b, c)
          sil.If(cond, seq, empty)(a, b, c)
        }
        else {
          sil.Inhale(sil.Not(cond)(a, b, c))(a, b, c)
        }
      case sil.If(cond, thn, els) => sil.If(cond, inlineSilAux(thn, n).asInstanceOf[sil.Seqn], inlineSilAux(els, n).asInstanceOf[sil.Seqn])(a, b, c)
      case sil.Seqn(ss, scopedDecls) => sil.Seqn(ss map (inlineSilAux(_, n)), scopedDecls)(a, b, c)
      case _ => s
    }

  }

  def readAccPredicate(acc: ast.PredicateAccessPredicate): Set[sil.LocalVar] = {
    acc match {
      case sil.PredicateAccessPredicate(pred, perm) =>
        pred match {
          case sil.PredicateAccess(args, name) =>
            (args map readVarsExp).fold(Set())(_ ++ _) ++ readVarsExp(perm)
        }
    }
  }


  def readWand(wand: sil.MagicWand): Set[sil.LocalVar] = {
    wand match {
      case sil.MagicWand(e1, e2) => readVarsExp(e1) ++ readVarsExp(e2)
    }
  }

  def read(s: sil.Stmt): Set[sil.LocalVar] = {
    s match {
      case sil.Seqn(ss, scopedDecls) => (ss map read).fold(Set())(_ ++ _) ++ (scopedDecls map (readVarsDecl(_).toSet)).fold(Set())(_ ++ _)
      case sil.If(cond, thn, els) => readVarsExp(cond) ++ read(thn) ++ read(els)
      case ast.LocalVarAssign(lhs, rhs) => Set(lhs) ++ readVarsExp(rhs)
      case ast.FieldAssign(ast.FieldAccess(rcv, _), rhs) => readVarsExp(rcv) ++ readVarsExp(rhs)
      case ast.MethodCall(methodName, args, targets) =>
        (args map readVarsExp).fold(Set())(_ ++ _) ++ (targets map (Set(_))).fold(Set())(_ ++ _)
      case ast.Exhale(exp) => readVarsExp(exp)
      case ast.Inhale(exp) => readVarsExp(exp)
      case ast.Assert(exp) => readVarsExp(exp)
      case ast.Assume(exp) => readVarsExp(exp)
      case ast.Fold(acc) => readAccPredicate(acc)
      case ast.Unfold(acc) => readAccPredicate(acc)
      case ast.Package(wand, proofScript) => readWand(wand) ++ read(proofScript)
      case ast.Apply(wand) => readWand(wand)
      case ast.While(cond, invs, body) => readVarsExp(cond) ++ (invs map readVarsExp).fold(Set())(_ ++ _) ++ read(body)
      case ast.Label(name, scope) => (scope map readVarsExp).fold(Set())(_ ++ _)
      case ast.Goto(_) => Set()
      case ast.NewStmt(lhs, fields) => Set(lhs)
      case ast.LocalVarDeclStmt(decl) => readVarsDecl(decl).toSet
      case ast.WhileInl(_,_,_) =>
        assert(false);  Set() //should not happen
      case _: ast.ExtensionStmt => Set()

    }
  }

  def inlineSil(s: sil.Stmt, n: Int): sil.Stmt = {
    namesAlreadyUsed ++= read(s).toSet
    currentRenaming = Map()
    inRenaming = Set()
    inlineSilAux(s, n)
  }

  // Wrapper for modular approximation
  def checkFraming(body1: sil.Stmt, body2: ast.Stmt, checkMono: Boolean = false, checkWFM: Boolean = false, modif_vars: Seq[LocalVar] = Seq()): Stmt = {
    //println("CHECK FRAMING", old_body1, old_body2)
    //val body1 = transformLabelsAndOld(old_body1)
    //val body2 = transformLabelsAndOld(old_body2)
    if (modularSC) {
      if (checkMono) {
        if (inside_initial_method) {
          checkFramingAux(body1, body2, true, checkWFM, modif_vars)
        }
        else {
          checkFramingAux(body1, body2, false, checkWFM, modif_vars)
        }
      }
      else {
        if (!inlinable(body1)) {
          checkFramingAux(body1, body2, checkMono, checkWFM, modif_vars)
        }
        else {
          // Avoiding to check framing thanks to compositional property
          Statements.EmptyStmt
        }
      }
    }
    else {
      checkFramingAux(body1, body2, checkMono, checkWFM, modif_vars)
    }
  }

  var n_syntactic = 0
  var n_syntactic_not = 0

  def checkFramingAux(pre_body1: sil.Stmt, pre_body2: ast.Stmt, checkMono: Boolean = false, checkWFM: Boolean = false, modif_vars: Seq[LocalVar] = Seq()): Stmt = {
    namesAlreadyUsed = Set()
    val body1: ast.Stmt = inlineSil(pre_body1, maxDepth - current_depth)
    val body2: ast.Stmt = inlineSil(pre_body2, maxDepth - current_depth)
    // val orig_s: ast.Stmt = pre_orig_s
    if (verifier.printSC)
      println("checkFraming", current_depth, "framing", !checkMono, "length", length(body1))

    var ignore = false


    if (first_block && inside_initial_method && checkMono) {
      if (verifier.printSC)
        println("Ignoring first part of the code (trivial)")
      ignore = true
    }
    else if (isCheckingFraming()) {
      ignore = true
    }
    else if (syntacticFraming(body1, checkMono)) {
      if (!checkWFM) {
        n_syntactic += 1
      }
      if (verifier.printSC) {
        println("___________________________________________________________")
        if (checkMono) {
          println("Syntactically mono")
        }
        else {
          println("Syntactically framing")
        }
        println("-----------------------------------------------------------")
        println(body1)
        println("¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯")
      }
      ignore = true
    }

    first_block = false

    if (ignore) {
      if (verifier.printSC)
        println("IGNORING...")
      Statements.EmptyStmt
    }
    else {

      if (!checkWFM) {
        n_syntactic_not += 1
      }

      if (verifier.printSC) {
        println("___________________________________________________________")
      }

      if (checkMono) {if (checkWFM) {id_checkWfm += 1} else {id_checkMono += 1}} else {id_checkFraming += 1}
      val id_error = {if (checkMono) {if (checkWFM) id_checkWfm else id_checkMono} else id_checkFraming}
      val errorType = {if (checkMono) {if (checkWFM) "WFM" else "MONO"} else "FRAMING"}

      if (verifier.printSC) {
        println(errorType + " " + id_error)
        println("-----------------------------------------------------------")
        println(body1)
        println("¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯")
      }

      val aa = body1.pos
      val bb = body1.info
      val cc = body1.errT

      val silExistsDecl: ast.LocalVarDecl = sil.LocalVarDecl(silNameNotUsed("exists"), sil.Bool)(aa, bb, cc)
      val exists: LocalVar = mainModule.env.define(silExistsDecl.localVar)

      //val silCheckDecl: ast.LocalVarDecl = sil.LocalVarDecl(silNameNotUsed("checkFraming"), sil.Bool)(aa, bb, cc)
      // val check: LocalVar = mainModule.env.define(silCheckDecl.localVar)
      val (check, id_check) = getCheckBool()


      // val orig_s1: sil.Stmt = sil.Seqn(Seq(sil.LocalVarAssign(silExistsDecl.localVar, sil.TrueLit()(aa, bb, cc))(aa, bb, cc),
      val orig_s1: sil.Stmt = recordVarsSil(body1, silExistsDecl.localVar)
        //Seq(silExistsDecl))(aa, bb, cc)
        //Seq())(aa, bb, cc)
      val orig_s2: sil.Stmt = assignVarsSil(body2, silExistsDecl.localVar)
      // val orig_s1 = orig_s

      val converted_vars: Seq[LocalVar] = (body1.writtenVars filter (v => mainModule.env.isDefinedAt(v))) map translateLocalVar
      // val oldVars = converted_vars map ((v: LocalVar) => newVar(v.typ).l)
      val oldVars = converted_vars map ((v: LocalVar) => getVarDecl(v.name.name, v.typ).l)
      // val tempVars = converted_vars map ((v: LocalVar) => newVar(v.typ).l)
      val tempVars = converted_vars map ((v: LocalVar) => getVarDecl(v.name.name, v.typ).l)


      // val check = getVarDecl("checkFraming", Bool)
      val maskPhi1 = getVarDecl("MaskPhi1", maskType)
      val heapPhi1 = getVarDecl("HeapPhi1", heapType)
      val maskR = getVarDecl("MaskR", maskType)
      val heapR = getVarDecl("HeapR", heapType)
      val maskPhi2 = getVarDecl("MaskPhi2", maskType)
      val heapPhi2 = getVarDecl("HeapPhi2", heapType)

      checkingFraming = true

      var s1: Stmt = Statements.EmptyStmt
      var s2: Stmt = Statements.EmptyStmt
      val old_current_exists = current_exists
      current_exists = Some(exists)
      recordingSil = true
      s1 = stmtModule.translateStmt(orig_s1)
      recordingSil = false
      assigningSil = true
      current_exists = old_current_exists
      s2 = stmtModule.translateStmt(orig_s2)

      s1 = s1.optimize.asInstanceOf[Stmt]
      s2 = s2.optimize.asInstanceOf[Stmt]


      val text = {if (checkWFM) "WFM" else "monoOut"}
      val nm_exists: VerificationError = SoundnessFailed(body1, DummyReason, text + " (trace may disappear)", id_error, errorType)
      val nm_smaller: VerificationError = SoundnessFailed(body1, DummyReason, text + " (order not preserved)", id_error, errorType)
      val nm_variables: VerificationError = SoundnessFailed(body1, DummyReason, text + " (variables)", id_error, errorType)


      val nf: VerificationError = SoundnessFailed(body1, DummyReason, "framing", id_error, errorType)
      val error_ignore: VerificationError = SoundnessFailed(body1, DummyReason, "monoOut (structural)", id_error, errorType)
      val nsm: VerificationError = SoundnessFailed(body1, DummyReason, "safeMono", id_error, errorType)

      declareFalseAtBegin = Seq()
      val (modif_s, l) = recordDeterminism(assumify(addIfExists(changeStateWfState(s1, exists), exists)))
      val assign_false_branches_taken: Seq[Stmt] = declareFalseAtBegin map ((x) => Assign(x.l, FalseLit()))

      val (modif_s2, ll) = determinize(doubleErrorSafeMono(s2, body2, id_error, errorType, check, id_check), l, check, id_check, error_ignore)

      val sumState = (getVarDecl("sumMask", maskType), getVarDecl("sumHeap", heapType))

      assert(ll.isEmpty)

      val statement: Seq[Stmt] =
        assignSeqToSeq(oldVars, converted_vars) ++
        assign_false_branches_taken ++
        // {
          /*
          if (checkMono) {
              Assume(smallerState(maskPhi2.l, heapPhi2.l, normalState._1, normalState._2)) ++
              Assume(wfMask(Seq(maskPhi2.l))) ++
              Assume(smallerState(maskPhi1.l, heapPhi1.l, maskPhi2.l, heapPhi2.l)) ++
              Assume(wfMask(Seq(maskPhi1.l)))
          }
          else {
           */ {
          if (checkWFM) {
            Havoc(modif_vars) // WFM should be theoretically unbounded
          }
          Assume(smallerState(maskPhi2.l, heapPhi2.l, normalState._1, normalState._2))
        } ++
              Assume(wfMask(Seq(maskPhi2.l))) ++
              // Assume(sumStateNormal(maskPhi1.l, heapPhi1.l, maskR.l, heapR.l, maskPhi2.l, heapPhi2.l)) ++
              Assume(sumMasksFunc(maskPhi2.l, maskPhi1.l, maskR.l)) ++
              Assume(heapPhi1.l === heapR.l) ++
              Assume(heapPhi2.l === heapR.l) ++
              Assume(heapPhi1.l === heapPhi2.l) ++
              Assume(smallerState(maskPhi1.l, heapPhi1.l, maskPhi2.l, heapPhi2.l)) ++
              Assume(wfMask(Seq(maskPhi1.l))) ++ Assume(wfMask(Seq(maskR.l))) ++
          //}
        //}
          MaybeComment("State is phi1", Assign(normalState._1, maskPhi1.l) ++ Assign(normalState._2, heapPhi1.l)) ++
          MaybeComment("Init exists boolean", Assign(exists, TrueLit())) ++
          MaybeComment("s1 and phi1", modif_s) ++
          MaybeComment("Back to phi1", Assign(maskPhi1.l, normalState._1) ++ Assign(heapPhi1.l, normalState._2)) ++
          assignSeqToSeq(tempVars, converted_vars) ++
          MaybeComment("State is phi2", Assign(normalState._1, maskPhi2.l) ++ Assign(normalState._2, heapPhi2.l)) ++
          assignSeqToSeq(converted_vars, oldVars) ++
          MaybeComment("s2 and phi2", modif_s2) ++
          Assert(exists, nm_exists) ++
          Assert(smallerState(maskPhi1.l, heapPhi1.l, normalState._1, normalState._2), nm_smaller) ++
          Assert(equalSeq(converted_vars, tempVars), nm_variables) ++ {
        if (!checkMono) {
            Assert(equalOnInterFunc(heapPhi1.l, heapR.l, maskPhi1.l, maskR.l), nf) ++
            Assume(
              sumStateNormal(maskPhi1.l, heapPhi1.l, maskR.l, heapR.l, sumState._1.l, sumState._2.l)
              // sumMask(maskPhi1.l, maskR.l, sumState._1.l)
            ) ++
            Assert(exists && smallerState(sumState._1.l, sumState._2.l, normalState._1, normalState._2), nf)
        }
        else {
          Statements.EmptyStmt
        }
      }

      val r: Stmt = MaybeComment(id_checkFraming + {if (checkWFM) ": Check WFM" else if (checkMono) ": Check MONO" else ": Check FRAMING"},
        NondetIf(If(getBounded.l, statement, Statements.EmptyStmt) ++ Assume(FalseLit()), Statements.EmptyStmt))
      checkingFraming = false
      checkingFraming = false
      mainModule.env.undefine(silExistsDecl.localVar)
      r
    }
  }


  /**
   * Only checks if the code contains method calls or loops. Does not check soundness.
   *
   * @param stmt a Viper statement
   * @return True if stmt contains a method call of a defined method or a loop
   */
  def inlinable(stmt: sil.Stmt): Boolean = {
    stmt match {
      case sil.MethodCall(methodName, _, _) =>
        val method = verifier.program.findMethod(methodName)
        method.body.isDefined
      case sil.While(_, _, _) => true
      case sil.If(_, thn, els) => inlinable(thn) || inlinable(els)
      case sil.Seqn(ss, _) => ss.exists(inlinable)
      case _ => false
    }
  }

  /**
   * The first and second type of p1 and p2 respectively have to match.
   *
   * @param p1 tupel of two sequences of independet types
   * @param p2 tupel of two sequences of independet types
   * @return returns tuple where Seq[A] of p2 is appended to Seq[A] of p1 and Seq[B] of p2 is appended to  Seq[B] of p1
   */
  def combine[A, B](p1: (Seq[A], Seq[B]), p2: (Seq[A], Seq[B])): (Seq[A], Seq[B]) = {
    (p1._1 ++ p2._1, p1._2 ++ p2._2)
  }

  /**
   * Returns a sequence of statements (potentially longer) such that none of the statement is a sequence.
   *
   * @param s Sequence of Viper statements
   * @return returns pair with a sequence of Viper statements of which none are a sequence and their corresponding
   *         declaration. If the statement has no declaration then the corresponding declaration is Nil. If the
   *         sequence of statements itself is Nil it returns a the tuple (Nil,Nil). --> and are semantically equivalent
   */
  def flattenSeqn(s: Seq[sil.Stmt]): (Seq[sil.Stmt], Seq[sil.Declaration]) = {
    s match {
      case Nil => (Nil, Nil)
      case sil.Seqn(stmts, scopedDecls) +: xs => combine(combine(flattenSeqn(stmts), (Nil, scopedDecls)), flattenSeqn(xs))
      case x +: xs => combine((Seq(x), Nil), flattenSeqn(xs))
    }
  }

  /**
   * Transforms statements recursively such that no statement of type Seqn has an element in its sequence
   * of statements with type Seqn.
   *
   * @param s a Viper statement
   * @return If s is not of Viper type Seqn, if, or While it will simply return s. For if and while statements it will
   *         return the same if or while statement after recursively applying itself to the body. If s is a Seqn
   *         then it will travers s in order, split up/flatten all statements of type Seqn into Stmt's though
   *         flattenStmtSeqn(), and add the corresponding declarations to s.
   */
  def flattenStmt(s: sil.Stmt): sil.Stmt = {
    val (a, b, c) = (s.pos, s.info, s.errT)
    s match {
      case ast.Seqn(ss, scope) => {
        val (stmts, decls) = flattenSeqn(ss)
        sil.Seqn(stmts, scope ++ decls)(a, b, c)
      }
      case ast.If(cond, thn, els) => ast.If(cond, flattenStmt(thn).asInstanceOf[sil.Seqn], flattenStmt(els).asInstanceOf[sil.Seqn])(a, b, c)
      case ast.While(cond, invs, body) => sil.While(cond, invs, flattenStmt(body).asInstanceOf[sil.Seqn])(a, b, c)
      case _ => s
    }
  }

  def alreadyGroupedInlinableStmts(ss: Seq[sil.Stmt]): Boolean = {
    (ss forall inlinable) || (ss forall (!inlinable(_)))
  }

  def groupNonInlinableStmts(ss: Seq[sil.Stmt], orig_s: sil.Stmt, locals: Seq[sil.LocalVarDecl]): (Seq[sil.Stmt], Seq[sil.LocalVarDecl]) = {

      var currentNonInlinable: Seq[sil.Stmt] = Seq()
      var r: Seq[sil.Stmt] = Seq()
      for (s <- ss) {
        if (!inlinable(s)) {
          currentNonInlinable :+= s
        }
        else {
          if (currentNonInlinable.nonEmpty) {
            if (currentNonInlinable.size == 1) {
              r :+= currentNonInlinable.head
            }
            else {
              r :+= sil.Seqn(currentNonInlinable, Seq())(orig_s.pos, orig_s.info, orig_s.errT)
            }
            currentNonInlinable = Seq()
          }
          r :+= s
        }
      }
      if (currentNonInlinable.nonEmpty) {
        if (currentNonInlinable.size == 1) {
          r :+= currentNonInlinable.head
        }
        else {
          r :+= sil.Seqn(currentNonInlinable, Seq())(orig_s.pos, orig_s.info, orig_s.errT)
        }
      }

    // Reorganizing variable declarations to capture more patterns

    var count: Map[sil.Declaration, Int] = Map()
    for (d <- locals) {
      count += (d -> 0)
    }
    for (s <- r) {
      for (d <- locals) {
        if (s.undeclLocalVars.contains(d.localVar)) {
          count += (d -> (count(d) + 1))
        }
      }
    }

    for (d <- locals) {
      if (count(d) == 1) {
        for ((s, i) <- r.zipWithIndex) {
          if (s.undeclLocalVars.contains(d.localVar)) {
            s match {
              case sil.Seqn(ss, scopedDecls) => r = r.updated(i, sil.Seqn(ss, scopedDecls ++ Seq(d))(s.pos, s.info, s.errT))
              case _ => count += (d -> 2) // We return it if not caught
            }
          }
        }
      }
    }

    (r, locals.filter(count(_) > 1))
    }

  // ----------------------------------------------------------------
  // ACTUAL INLINING
  // ----------------------------------------------------------------

  def ignoreErrorsWhenBounded(stmt: Stmt): Stmt = {
    if (staticInlining.isDefined && closureSC) {
      stmt match {
        case Seqn(stmts) => stmts map ignoreErrorsWhenBounded
        case CommentBlock(c, ss) => CommentBlock(c, ignoreErrorsWhenBounded(ss))
        case If(cond: Var, _, _) if (cond.name.name == getBounded.l.name.name) =>
          stmt
        case If(cond, thn, els) => If(cond, ignoreErrorsWhenBounded(thn), ignoreErrorsWhenBounded(els))
        case NondetIf(thn, els) => NondetIf(ignoreErrorsWhenBounded(thn), ignoreErrorsWhenBounded(els))
        case Assert(exp, _) => If(getBounded.l, Assume(exp), stmt)
        case ss => ss
      }
    }
    else {
      stmt
    }
  }

  def annotateMethod(m: ast.Method): ast.Method = {
    val (pos, info, errT) = (m.pos, m.info, m.errT)
    val pre = foldStar(m.pres, pos, info, errT)
    val post = foldStar(m.posts, pos, info, errT)
    val annotated_body = ast.Seqn(Seq(ast.Assert(pre)(pos, info, errT), annotateStmt(m.body.get), ast.Assert(post)(pos, info, errT)), Seq())(pos, info, errT)
    m.copy(body = Some(annotated_body))(pos, info, errT)
  }

  private def getUniqueTempArgName() : String = {
    //FIXME: we are assuming that there are no other variables with such a prefix
    val result = "tempArg$$_"+currentArgInt
    currentArgInt += 1
    result
  }

  private def getUniqueLabelName() : String = {
    //FIXME: we are assuming that there are no other labels with such a prefix
    var result = "label_$_"+currentLabelInt
    currentLabelInt += 1
    var i:Int = 1
    while (mainModule.env.allDefinedNames(verifier.program).contains(result)) {
      val temp: Int = i +currentLabelInt
      result = "label_$_"+temp
    }
    result
  }

  private def rewriteOldToLabelledOld[T <: sil.Node](n: T, labelName: String) : T = {
    n.transform({
      case oldE@sil.Old(e) =>
        sil.LabelledOld(e, labelName)(oldE.pos, oldE.info, oldE.errT).asInstanceOf[sil.Node]
    })
  }

  /**
   * Recursively traverses a statement and applies transformations with regard to the annothations to ast.stmt
   * of type ast.MethodCall and ast.While.
   *
   * @param s s is a Viper Statement.
   * @return Returns the same statement but adds the conjunction of all pre-conditions, post-conditions, or invariants
   *         for method calls or loops as ast.Assert statements to the start and/or end of the body as well as the start
   *         and/or end of the method or loop
   */
  def annotateStmt(s: ast.Stmt): ast.Stmt = {
    val (a, b, c) = (s.pos, s.info, s.errT)
    s match {
      case ast.MethodCall(methodName, args, targets) =>
      {
        val method = verifier.program.findMethod(methodName)
        if (!method.body.isDefined) {
          return s
        }

        /**
          * we rename "z1, z2, ... := m(e1,e2,...)" to
          * tempArg1 := e1
          * tempArg2 := e2
          * ...
          * assert pre_m[tempArg1/mArg1, tempArg2/mArg2,...]
          * z1, z2, ... := m(tempArg1, tempArg2, ...)
          * assert post_m[tempArg1/mArg1, tempArg2/mArg2,...]
          *
          * The assignments are required due to expressions that are dependent on where they are evaluated such as
          * field accesses, old expressions, target variables.
          * In some cases we omit the assignment and instead use the original expression for the argument
          * if it's safe to do so.
          *
          * This code is similar to the translation of method calls in the statement module
          * */
        val actualArgs : Seq[(sil.Exp, sil.Stmt, Option[sil.LocalVarDecl])] = args.zipWithIndex map (a => {
          val (actual, i) = a
          // use the concrete argument if it is just a variable or constant (to avoid code bloat)
          val useConcrete = actual match {
            case v: sil.LocalVar if !targets.contains(v) => true
            case _: sil.Literal => true
            case _ => false
          }
          if (!useConcrete) {
            val silFormal = method.formalArgs(i)
            val tempArgDecl = sil.LocalVarDecl(getUniqueTempArgName(), silFormal.typ)()
            val stmt = sil.LocalVarAssign(tempArgDecl.localVar, actual)()
            (tempArgDecl.localVar, stmt, Some(tempArgDecl))
          } else {
            (actual, sil.utility.Statements.EmptyStmt, None)
          }
        })

        val argVars = actualArgs.collect {
          case actualArg if actualArg._1.isInstanceOf[sil.LocalVar] => actualArg._1.asInstanceOf[sil.LocalVar].name
        }.toSet

        val argDecls : Seq[sil.Declaration] = actualArgs.collect( {
          case actualArg if actualArg._3.isDefined => actualArg._3.get
        })

        val argAssignments : sil.Stmt = sil.Seqn(actualArgs.map(arg => arg._2), Nil)(a, b, c)

        val pre = foldStar(method.pres map (e => Expressions.instantiateVariables(e, method.formalArgs ++ method.formalReturns, (actualArgs map (_._1)) ++ targets, argVars)), a, b, c)
        val post = foldStar(method.posts map (e => Expressions.instantiateVariables(e, method.formalArgs ++ method.formalReturns, (actualArgs map (_._1)) ++ targets, argVars)), a, b, c)

        /** if the pre or post contain old expressions, then we need to create a new unique label before the call,
          * otherwise the old expressions in the corresponding assertions will point evaluate incorrectly */
        val (rewrittenPre, rewrittenPost, newLabelOpt) =
          if(List(pre,post).exists( a => a.existsDefined( { case sil.Old(_) => true }))) {
            val newLabelName = getUniqueLabelName()
            val newLabel = sil.Label(newLabelName, Seq())(a, b, c)
            (rewriteOldToLabelledOld(pre, newLabelName), rewriteOldToLabelledOld(post, newLabelName), Some(newLabel))
          } else {
            (pre, post, None)
          }

        //renamed method call
        val renamedMethodCall = ast.MethodCall(methodName, actualArgs.map(arg => arg._1), targets)(a, b, c)

        ast.Seqn(
          newLabelOpt.fold[Seq[sil.Stmt]](Seq())(lbl => Seq(lbl)) ++
          Seq(argAssignments, sil.Assert(rewrittenPre)(a, b, c), renamedMethodCall, sil.Assert(rewrittenPost)(a, b, c)), argDecls)(a, b, c)
      }
      case ast.Seqn(ss, scope) => ast.Seqn(ss map annotateStmt, scope)(a, b, c)
      case ast.If(cond, thn, els) => ast.If(cond, annotateStmt(thn).asInstanceOf[ast.Seqn], annotateStmt(els).asInstanceOf[ast.Seqn])(a, b, c)
      case ast.While(cond, invs, body) =>
        val inv = foldStar(invs, a, b, c)
        val assert = ast.Assert(inv)(a, b, c)
        //"Seq() represents the scope (Seq[Declaration])
        val annotated_body = ast.Seqn(Seq(assert, body, assert), Seq())(a, b, c)
        val new_while = ast.While(cond, invs, annotated_body.asInstanceOf[ast.Seqn])(a, b, c)
        ast.Seqn(Seq(assert, new_while, assert), Seq())(a, b, c)
      case _ => s // Probably useless
    }
  }

  /**
   * Contains all labels from the program and maps labels (Strings) to labels (Strings).
   * The first time a label appears we map it to itself. After we create a new label, map the new label to
   * itself, and map the existing label to the new one.
   * The newest label acts as fixed point when traversing the mapping.
   * The labels and the renaming are used for "old[]"-expressions when inlining.
   *
   * @note: All label keys should point directly to a fixed point.
  */
  var renamingLabels: Map[String, String] = Map()
  var allNamesSet: Set[String] = Set()

  var labelCounter: Int = 0

  def getFreshName(s: String): String = {
    //FIXME: We rely on the assumption that this label name is unique and fresh
    allNamesSet = allNamesSet ++ mainModule.env.allDefinedNames(verifier.program)

    var result: String = s
    if (result.contains("$$_"))
      result = result.substring(0, s.length-s.indexOf("$$_"))
    result += "$$_" +labelCounter
    var i:Int = 1
    while (allNamesSet.contains(result)) {
      result = result.substring(0, result.length- labelCounter.toString.length) + (labelCounter + i)
    }
    labelCounter += 1
    allNamesSet += result
    result
  }

  /**
   * Follows the path until it reaches a fixed point.
   * Needed to safely apply the transformation several times on same code
   * @param s s is a label that is contained in the mapping "renamingLabels". All labels get added to "renamingLabels"
   *          through the method "updateLabels"
   * @return follows the path of "renamingLabels" until it reaches fixed point
   *
   * @note: renamingLabels should always directly point to a fixed point because of updateLabel method. So it should
   * be enought to just return "renamingLabels(s)"
   */
  def getLabel(s: String): String = {
    //the datastructure is always compact
    assert(renamingLabels(s) == renamingLabels(renamingLabels(s)))
    if (renamingLabels(s) == s)
      s
    else {
      val r = getLabel(renamingLabels(s))
      renamingLabels += (s -> r)
      r
    }
  }

  /**
   * Needs to always ensure that at the end of each path there is a fixed point
   *
   * @param s Label from program
   * @return Returns the fixed point of the label s in the mapping "renamingLabels"
   *
   * @note: Should ensures that a label always points to a fixed point.
   */
  def updateLabel(s: String): String = {
    if (renamingLabels contains s) {
      if (renamingLabels(s) == s) {
        // We reached the fixed point, we create a new fresh name
        val ss = getFreshName(s)
        renamingLabels += (s -> ss)
        renamingLabels += (ss -> ss)
      }
      else {
        // We only* update the fixed point
        val r = updateLabel(renamingLabels(s))
        renamingLabels += (s -> r)
      }
    }
    else {
      renamingLabels += (s -> s)
    }
    renamingLabels(s)
  }

  /*
  // TODO: Continue here
  // MAYBE ONLY rename exps usually?
  def transformLabelsAndOld(s: ast.Stmt): ast.Stmt = {
    println("TRANFORM BEFORE", s)
    val r = s.transform(
      {
        case l@sil.Label(name, invs) =>
          println("Inside transform...", l, l.pos) ; sil.Label(updateLabel(name), invs)(l.pos, l.info, l.errT)
        case e@sil.LabelledOld(exp, label) => sil.LabelledOld(exp, renamingLabels(label))(e.pos, e.info, e.errT)
      },
      Traverse.TopDown)
    println("TRANFORM AFTER", r)
    println("CURRENT TRANSFORMATION", renamingLabels)
    r
  }

  def transformOld(s: ast.Stmt): ast.Stmt = {
    s.transform(
      {
        case e@sil.LabelledOld(exp, label) => (if (renamingLabels contains label) sil.LabelledOld(exp, renamingLabels(label))(e.pos, e.info, e.errT) else e)
      },
      Traverse.TopDown)
  }
   */


  def inlineLoop(w: sil.WhileInl): Stmt = {

    val cond: sil.Exp = w.w.cond
    val invs: Seq[ast.Exp] = w.w.invs
    val body: ast.Seqn = w.w.body

    extendCallstack(w)

    if (verifier.printSC)
      println("inlineLoop", current_depth, cond, "length", length(body), n_inl)

    val guard = translateExp(cond)
    val depth = maxDepth - current_depth

    if (stopInlining) {
      val cond_neg: sil.Stmt = sil.Inhale(sil.Not(cond)(cond.pos, cond.info, cond.errT))(cond.pos, cond.info, cond.errT)
      val wfm: Stmt = checkFraming(cond_neg, cond_neg, true, true)
      extendCallstack(pop(callStack)._1, true) //remove top s.t. we do not push the same iteration twice
      MaybeCommentBlock("0: Check SC and cut branch (loop)", wfm ++ Assume(guard ==> FalseLit()))
    }
    else {
      // Remembering some parameters to restore at the end of the method
      val old_inside_initial_method = inside_initial_method
      inside_initial_method = false
      val old_renaming = renamingLabels

      current_depth += 1
      // Real inlining
      n_inl += 1

      val r1 = checkFraming(body, body)

      //val body_labels_renamed = transformLabelsAndOld(body).asInstanceOf[ast.Seqn]

      val modif_vars: Seq[LocalVar] = (body.writtenVars filter (v => mainModule.env.isDefinedAt(v))) map translateLocalVar

      val check_wfm = {
        val cond_pos: sil.Stmt = sil.Inhale(cond)(cond.pos, cond.info, cond.errT)
        val cond_neg: sil.Stmt = sil.Inhale(sil.Not(cond)(cond.pos, cond.info, cond.errT))(cond.pos, cond.info, cond.errT)
        MaybeCommentBlock("Check WFM", checkFraming(cond_pos, cond_pos, true, true, modif_vars=modif_vars)
          ++ checkFraming(cond_neg, cond_neg, true, true, modif_vars=modif_vars))
      }

      val oldCheckingFraming = checkingFraming
      if (!inlinable(body)) {
        checkingFraming = true
      }
      val r2 = MaybeCommentBlock(depth + ": Loop body", stmtModule.translateStmt(body))
      checkingFraming = oldCheckingFraming

      val remaining = inlineLoop(sil.WhileInl(w.w, w.id, w.iteration+1)(w.pos, w.info, w.errT))


      // Restoring...
      current_depth -= 1
      inside_initial_method = old_inside_initial_method
      renamingLabels = old_renaming
      MaybeCommentBlock(depth + ": Inlined loop", check_wfm ++ If(guard, r1 ++ getBoundedComplete() ++ r2 ++ remaining, Statements.EmptyStmt) ++ getBoundedComplete())
    }
  }

  /**
   * @return True if maxDepth for inlining is reached or if max number of inlined loops or methods, if defined by user,
   *         is reached  */
  def stopInlining(): Boolean = {
    var temp = (current_depth == maxDepth || (verifier.maxInl.isDefined && (n_inl >= verifier.maxInl.get)))
    if ((verifier.maxInl.isDefined && (n_inl >= verifier.maxInl.get)))
      maxInlineReached = true
    temp
  }

  /**
   * Used for pre-conditions, post-conditions, and invariants of loops and methods. Aggregates the invariants into a
   * conjunction
   *
   * @param s Sequence of Viper expressions
   * @param a Position of the sequence s
   * @param b Info of the sequence s
   * @param c ErrorTrafo of the sequence s
   * @return Returns a Viper Expression with position a, info b, and ErrorTrafo c; If s is empty it returns a True
   *         Boolean Literal; Else it returns the conjunction of all elements of s;
   */
  def foldStar(s: Seq[ast.Exp], a: ast.Position, b: ast.Info, c: ast.ErrorTrafo): ast.Exp =
  {
    if (s.isEmpty) {
      ast.BoolLit(true)(a, b, c)
    }
    else {
      (s.tail fold (s.head))((e1: ast.Exp, e2: ast.Exp) => ast.And(e1, e2)(a, b, c))
    }
  }

  var n_label = 0


  def inlineMethod(mc: sil.MethodCall, m: Method, args: Seq[ast.Exp], targets: Seq[ast.LocalVar]): Stmt = {

    extendCallstack(mc)
    var addInfo: String = "At depth: "+ current_depth + "; Stacktrace: "+ callStackToString()
    mc.inlMsg = Some(addInfo)

    if (verifier.printSC)
      println("inlineMethod", current_depth, m.name, "length", length(m.body.get), n_inl)

    if (stopInlining) {
      extendCallstack(mc, true)
      MaybeComment("0: Cut branch (method call)", Assume(FalseLit()))
    }
    else {
      val old_inside_initial_method = inside_initial_method
      inside_initial_method = false

      // LABELS: We save the current state of "Renaming", and we restore it at the end
      val old_renaming: Map[String, String] = renamingLabels

      // Real inlining
      n_inl += 1
      current_depth += 1
      val other_vars: Seq[ast.LocalVar] = (m.formalArgs map (_.localVar)) ++ (m.formalReturns map (_.localVar))

      currentRenaming = Map()
      inRenaming = Set()

      val t1: (PartialFunction[viper.silver.ast.Node,viper.silver.ast.Node]) = {
        case sil.Old(e) => sil.LabelledOld(e, n_label.toString)(e.pos, m.info, m.errT)
      }
      val t2: (PartialFunction[viper.silver.ast.Node,viper.silver.ast.Node]) = {
        case sil.Old(e) => sil.LabelledOld(e, (n_label + 1).toString)(e.pos, m.info, m.errT)
      }
      val t3: (PartialFunction[viper.silver.ast.Node,viper.silver.ast.Node]) = {
        case sil.Old(e) => sil.LabelledOld(e, (n_label + 2).toString)(e.pos, m.info, m.errT)
      }



      val pre_body: ast.Stmt = alphaRename(m.body.get)
      // Partial annotation:
      // We assert the precondition and the postcondition in Silver, before inlining
      // such that it also help to prove the soundness condition
      /*
      val prec: ast.Exp = foldStar(m.pres map renameExp, m.pos, m.info, m.errT)
      val pre_post: ast.Exp = foldStar(m.posts map renameExp, m.pos, m.info, m.errT)
       */
      val lab1 = ast.Label(n_label.toString, Seq())(m.pos, m.info, m.errT)
      val lab2 = ast.Label((n_label + 1).toString, Seq())(m.pos, m.info, m.errT)
      val lab3 = ast.Label((n_label + 2).toString, Seq())(m.pos, m.info, m.errT)

      /** For checking framing */
      val body1 = ast.Seqn(Seq(lab1, pre_body.transform(t1)), Seq())(m.pos, m.info, m.errT)
      /** For checking framing */
      val body2 = ast.Seqn(Seq(lab2, pre_body.transform(t2)), Seq())(m.pos, m.info, m.errT)
      /** For inlining in boogie */
      val body3 = ast.Seqn(Seq(lab3, pre_body.transform(t3)), Seq())(m.pos, m.info, m.errT)


      n_label += 3

      val renamedFormalArgsVars: Seq[ast.LocalVar] = (m.formalArgs map (_.localVar)) map renameVar
      val renamedFormalReturnsVars: Seq[ast.LocalVar] = ((m.formalReturns map (_.localVar))) map renameVar

      (renamedFormalArgsVars filter (x => !mainModule.env.isDefinedAt(x))) map mainModule.env.define
      (renamedFormalReturnsVars filter (x => !mainModule.env.isDefinedAt(x))) map mainModule.env.define


      val r1 = checkFraming(body1, body2)
      val oldCheckingFraming = checkingFraming
      if (!inlinable(body1)) {
        checkingFraming = true
      }
      /** r2 contains the translation of the method body  */
      val r2 = stmtModule.translateStmt(body3)
      checkingFraming = oldCheckingFraming

      current_depth -= 1

      val assignArgsPre: Seq[(Exp, Exp)] = ((renamedFormalArgsVars map translateExp) zip (args map translateExp)) filter ((x) => x._1 != x._2)
      val assignRetsPre: Seq[(Exp, Exp)] = ((targets map translateExp) zip (renamedFormalReturnsVars map translateExp)) filter ((x) => x._1 != x._2)

      val assignArgs = assignArgsPre map (x => Assign(x._1, x._2))
      val assignRets = assignRetsPre map (x => Assign(x._1, x._2))

      (renamedFormalArgsVars filter (x => mainModule.env.isDefinedAt(x))) map mainModule.env.undefine
      (renamedFormalReturnsVars filter (x => mainModule.env.isDefinedAt(x))) map mainModule.env.undefine

      // Restoring...
      inside_initial_method = old_inside_initial_method
      renamingLabels = old_renaming

      extendCallstack(mc, true)

      Seqn(assignArgs) ++ r1  ++ getBoundedComplete() ++ r2 ++ Seqn(assignRets) ++ getBoundedComplete()
    }
  }

  // ----------------------------------------------------------------
  // RENAMING
  // ----------------------------------------------------------------

  /** Map from the original name of a local Variable to their renamed declaration    */
  var currentRenaming: Map[ast.LocalVar, ast.LocalVar] = Map()
  /** set that contains all local variables that have already been renamed once */
  var inRenaming: Set[sil.LocalVar] = Set()
  /** Set with all names already used in the boogie file */
  var namesAlreadyUsed: Set[sil.LocalVar] = Set()


  /**
   * @param e a Viper expression
   * @return recursively reads expressions and returns all nested local variables as a set
   */
  def readVarsExp(e: ast.Exp): Set[ast.LocalVar] = {
    e match {
      case ast.Let(decl, e1, e2) => Set(decl.localVar)
      case ast.LocalVar(name, typ) => Set(ast.LocalVar(name, typ)(e.pos, e.info, e.errT))
      case ast.FieldAccessPredicate(e1, e2) => readVarsExp(e1) ++ readVarsExp(e2)
      case ast.BinExp(e1, e2) => readVarsExp(e1) ++ readVarsExp(e2)
      case ast.UnExp(e) => readVarsExp(e)
      case ast.CurrentPerm(e) => readVarsExp(e)
      case ast.FieldAccess(e1, _) => readVarsExp(e1)
      case _: ast.Literal => Set()
      case _: ast.AbstractConcretePerm => Set()
      case ast.WildcardPerm() => Set()
      case ast.FuncApp(_, args) => (args map readVarsExp).fold(Set())(_ ++ _)
      case ast.CondExp(e1, e2, e3) => readVarsExp(e1) ++ readVarsExp(e2) ++ readVarsExp(e3)
      case ast.Applying(ast.MagicWand(e1, e2), body) => readVarsExp(e1) ++ readVarsExp(e2) ++ readVarsExp(body)
      case ast.EmptySet(_) => Set()
      case ast.EmptySeq(_) => Set()
      case _: ast.ExtensionExp => Set()
      case ast.DomainFuncApp(_, args, _) => (args map readVarsExp).fold(Set())(_ ++ _)
      case ast.EmptyMultiset(_) => Set()
      case ast.EpsilonPerm() => Set()
      case ast.Exists(vars: Seq[ast.LocalVarDecl], _, e) =>
        val vars_set: Set[ast.LocalVar] = (vars map (_.localVar)).toSet
        readVarsExp(e).diff(vars_set)
      case ast.ExplicitMultiset(elems) => (elems map readVarsExp).fold(Set())(_ ++ _)
      case ast.ExplicitSet(elems) => (elems map readVarsExp).fold(Set())(_ ++ _)
      case ast.ExplicitSeq(elems) => (elems map readVarsExp).fold(Set())(_ ++ _)
      case ast.ForPerm(vars, _, body) =>
        val vars_set: Set[ast.LocalVar] = (vars map (_.localVar)).toSet
        readVarsExp(body).diff(vars_set)
      case ast.Forall(vars, _, e) =>
        val vars_set: Set[ast.LocalVar] = (vars map (_.localVar)).toSet
        readVarsExp(e).diff(vars_set)
      case ast.InhaleExhaleExp(in, ex) => readVarsExp(in) ++ readVarsExp(ex)
      case ast.PredicateAccess(args, _) => (args map readVarsExp).fold(Set())(_ ++ _)
      case ast.PredicateAccessPredicate(ast.PredicateAccess(args, _), perm) =>
        (args map readVarsExp).fold(Set())(_ ++ _) ++ readVarsExp(perm)
      case ast.RangeSeq(low, high) => readVarsExp(low) ++ readVarsExp(high)
      case ast.Result(_) => Set()
      case ast.SeqAppend(left, right) => readVarsExp(left) ++ readVarsExp(right)
      case ast.SeqContains(elem, s) => readVarsExp(elem) ++ readVarsExp(s)
      case ast.SeqDrop(s, n) => readVarsExp(s) ++ readVarsExp(n)
      case ast.SeqIndex(s, n) => readVarsExp(s) ++ readVarsExp(n)
      case ast.SeqTake(s, n) => readVarsExp(s) ++ readVarsExp(n)
      case ast.SeqUpdate(a, b, c) => readVarsExp(a) ++ readVarsExp(b) ++ readVarsExp(c)
      case ast.SeqLength(s) => readVarsExp(s)
      case ast.Unfolding(acc, body) => readVarsExp(acc) ++ readVarsExp(body)
    }
  }

  /**
   * @param d a declaration
   * @return if d is a declaration of a local variable then it returns a sequence that contains the local variable
   *         of d. Otherwise it will return an empty sequence.
   */
  def readVarsDecl(d: ast.Declaration): Seq[ast.LocalVar] = {
    d match {
      case decl: ast.LocalVarDecl => Seq(decl.localVar)
      case _ => Seq()
    }
  }

  /**
   *
   * @param s
   * @param n Interger; default n = 1
   * @return
   */
  def newString(s: String, n: Int = 1): String = {
    var definedVars = (mainModule.env.allDefinedVariables()) map (_.name)
    definedVars ++= (inRenaming map (_.name))
    definedVars ++= ((currentRenaming.keySet) map ((x: sil.LocalVar) => x.name))
    definedVars ++= ((currentRenaming.values.toSet) map ((x: sil.LocalVar) => x.name))
    definedVars ++= (namesAlreadyUsed map (_.name))
    if (definedVars.contains(s + "_" + n.toString)) {
      newString(s, n + 1)
    }
    else {
      s + "_" + n.toString
    }
  }

  /**
   * Creates and adds the mapping from x to its renamed counterpart to "currentRenaming" if x was not renamed before.
   * Otherwise it only returns the currentrenaming(x)
   *
   * @param x a local variable
   * @return returns a local variable that only differs from x by the name of its declaration
   */
  def renameVar(x: ast.LocalVar): ast.LocalVar = {
    if (!inRenaming.contains(x)) {
      val new_name = newString(x.name)
      val xx = ast.LocalVar(new_name, x.typ)(x.pos, x.info, x.errT)
      currentRenaming += (x -> xx)
      inRenaming += x
    }
    currentRenaming(x)
  }

  /**
   * renames all nested local variables in the argument exp by applying renameVar(sil.localVar)
   *
   * @param exp A Viper expression.
   * @return returns an expression with the same nested structure as exp but all local variables that might be
   *         captured are replaced with renamed and instantiated local variables.
   */
  def renameExp(exp: ast.Exp): ast.Exp = {
    val vars = readVarsExp(exp).toSeq
    val renamedVars = vars map renameVar
    val r = Expressions.instantiateVariables(exp, vars, renamedVars)
    r
  }

  def renameAccPredicate(acc: ast.PredicateAccessPredicate): ast.PredicateAccessPredicate = {
    acc match {
      case sil.PredicateAccessPredicate(pred, perm) =>
        pred match {
          case sil.PredicateAccess(args, name) =>
            val new_pred = sil.PredicateAccess(args map renameExp, name)(pred.pos, pred.info, pred.errT)
            sil.PredicateAccessPredicate(new_pred, renameExp(perm))(acc.pos, acc.info, acc.errT)
        }
    }
  }

  /**
   * @param d a Viper declaration
   * @return if d is a local variable declaration then it returns a new local variable declaration where the local
   *         variable of d is renamed while type and position are the same. Otherwise it will simply return d.
   */
  def renameDecl(d: sil.Declaration): sil.Declaration = {
    d match {
      case decl: ast.LocalVarDecl =>
        val new_x = renameVar(decl.localVar)
        ast.LocalVarDecl(new_x.name, new_x.typ)(decl.pos, decl.info, decl.errT)
      case _ => d // Unknown case
    }
  }

  def renameWand(wand: sil.MagicWand): sil.MagicWand = {
    wand match {
      case sil.MagicWand(e1, e2) => sil.MagicWand(renameExp(e1), renameExp(e2))(wand.pos, wand.info, wand.errT)
    }
  }

  def alphaRename(s: ast.Stmt): ast.Stmt = {
    val a = s.pos
    val b = s.info
    val c = s.errT
    s match {
      case ast.LocalVarAssign(lhs, rhs) =>
        LocalVarAssign(renameVar(lhs), renameExp(rhs))(a, b, c)
      case ast.FieldAssign(ast.FieldAccess(rcv, field), rhs) => FieldAssign(FieldAccess(renameExp(rcv), field)(a, b, c), renameExp(rhs))(a, b, c)
      case ast.MethodCall(methodName, args, targets) => ast.MethodCall(methodName, args map renameExp, targets map renameVar)(a, b, c)
      case ast.Exhale(exp) => ast.Exhale(renameExp(exp))(a, b, c)
      case ast.Inhale(exp) =>
        ast.Inhale(renameExp(exp))(a, b, c)
      case ast.Assert(exp) => ast.Assert(renameExp(exp))(a, b, c)
      case ast.Assume(exp) => ast.Assume(renameExp(exp))(a, b, c)
      case ast.Fold(acc) => ast.Fold(renameAccPredicate(acc))(a, b, c)
      case ast.Unfold(acc) => ast.Unfold(renameAccPredicate(acc))(a, b, c)
      case ast.Package(wand, proofScript) => ast.Package(renameWand(wand), alphaRename(proofScript).asInstanceOf[sil.Seqn])(a, b, c)
      case ast.Apply(wand) => ast.Apply(renameWand(wand))(a, b, c)
      case ast.Seqn(ss, scope) => ast.Seqn(ss map alphaRename, scope map renameDecl)(a, b, c)
      case ast.If(cond, thn, els) => ast.If(renameExp(cond), alphaRename(thn).asInstanceOf[ast.Seqn], alphaRename(els).asInstanceOf[ast.Seqn])(a, b, c)
      case ast.While(cond, invs, body) => ast.While(renameExp(cond), invs map renameExp, alphaRename(body).asInstanceOf[ast.Seqn])(a, b, c)
      case ast.Label(name, scope) => ast.Label(name, scope map renameExp)(a, b, c)
      case ast.Goto(_) => s
      case ast.NewStmt(lhs, fields) => ast.NewStmt(renameVar(lhs), fields)(a, b, c)
      case ast.LocalVarDeclStmt(decl) => ast.LocalVarDeclStmt(renameDecl(decl).asInstanceOf[sil.LocalVarDecl])(a, b, c)
      case ast.WhileInl(_,_,_) =>
        assert(false) ; s //should not happen
      case _: ast.ExtensionStmt => s // Probably useless
    }
  }

}
