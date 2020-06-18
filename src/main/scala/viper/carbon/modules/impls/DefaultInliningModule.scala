package viper.carbon.modules.impls

import viper.carbon.modules.InliningModule
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import Implicits._
import viper.carbon.modules.components.Component
import viper.silver.ast.{CurrentPerm, ErrorTrafo, FieldAccess, FieldAssign, ForPerm, Info, LocalVarAssign, LocationAccess, Method, Position, WildcardPerm}
import viper.silver.verifier.{DummyReason, VerificationError}
import viper.silver.ast.utility.Expressions
import viper.silver.verifier.errors.SoundnessFailed
import viper.silver.ast

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

  private val smallerState = Identifier("SmallerState")
  private val sumState = Identifier("SumState")
  private val mask1 = LocalVarDecl(Identifier("Mask1"),maskType)
  private val mask2 = LocalVarDecl(Identifier("Mask2"),maskType)
  private val smallHeap = LocalVarDecl(Identifier("SmallHeap"), heapType)
  private val bigHeap = LocalVarDecl(Identifier("BigHeap"), heapType)

  private val axiomNamespace = verifier.freshNamespace("inlining.axiom")

  var current_depth = 0

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
  // MATCH DETERMINISM
  // ----------------------------------------------------------------

  var recordedScopes: Seq[Seq[sil.LocalVar]] = Seq()

  // Record the values of variables at the beginning of scopes, and ensure return variables are the same (neither sound nor complete)
  def recordVarsSil(s: sil.Stmt): sil.Stmt = {
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
        sil.Seqn(assign ++ ss map recordVarsSil, scopedDecls)(a, b, c)
      // case sil.Inhale(exp) if (exp.isPure) => sil.LocalVarAssign(exists, sil.And(exists, exp)(exp.pos, exp.info, exp.errT))(a, b, c)
      // Assume
      case sil.MethodCall(methodName, args, targets: Seq[ast.LocalVar]) if program.findMethod(methodName).body.isEmpty
        && program.findMethod(methodName).pres.isEmpty =>
        // Abstract method
        val formalArgs: Seq[ast.LocalVarDecl] = program.findMethod(methodName).formalArgs
        val tempArgs: Seq[ast.LocalVar] = (args zip formalArgs) map ((x: (sil.Exp, sil.LocalVarDecl)) => {
          val name = silNameNotUsed("arg_temp")
          val tempLocalVar = sil.LocalVar(name, x._2.typ)(x._1.pos, x._1.info, x._1.errT)
          mainModule.env.define(tempLocalVar)
          println(tempLocalVar)
          tempLocalVar
        })
        val tempRets: Seq[ast.LocalVar] = targets map ((x: ast.LocalVar) => {
          val name = silNameNotUsed(x.name + "_temp")
          val tempLocalVar = sil.LocalVar(name, x.typ)(x.pos, x.info, x.errT)
          mainModule.env.define(tempLocalVar)
          tempLocalVar
        })

        recordedScopes :+= tempArgs
        recordedScopes :+= tempRets
        val assignArgs: Seq[LocalVarAssign] = (tempArgs zip args) map { (x: (sil.LocalVar, sil.Exp)) => sil.LocalVarAssign(x._1, x._2)(a, b, c) }
        val assignRets: Seq[LocalVarAssign] = (tempRets zip targets) map { (x: (sil.LocalVar, sil.LocalVar)) => sil.LocalVarAssign(x._1, x._2)(a, b, c) }
        sil.Seqn(assignArgs ++ Seq(s) ++ assignRets, Seq())(a, b, c)
      case sil.If(cond, s1: sil.Seqn, s2: sil.Seqn) =>
        val ss1 = recordVarsSil(s1).asInstanceOf[sil.Seqn]
        val ss2 = recordVarsSil(s2).asInstanceOf[sil.Seqn]
        sil.If(cond, ss1, ss2)(a, b, c)
      case _ => s
    }
  }

  def assignVarsSil(s: sil.Stmt): sil.Stmt = {
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
        sil.Seqn(assign ++ ss map assignVarsSil, scopedDecls)(a, b, c)
      case sil.MethodCall(methodName, args, targets: Seq[ast.LocalVar]) if program.findMethod(methodName).body.isEmpty
        && program.findMethod(methodName).pres.isEmpty =>
        val tempArgs: Seq[ast.LocalVar] = recordedScopes.head
        recordedScopes = recordedScopes.tail
        val tempRets: Seq[ast.LocalVar] = recordedScopes.head
        recordedScopes = recordedScopes.tail
        assert(args.size == tempArgs.size)
        assert(targets.size == tempRets.size)

        // We need to make sure the arguments from the two method calls are the same, with a boolean variable
        val same_seq: Seq[sil.Exp] = (tempArgs zip args) map { (x: (sil.LocalVar, sil.Exp)) => sil.EqCmp(x._1, x._2)(a, b, c) }
        val same_args_name = silNameNotUsed("sameArgs")
        val same_args: ast.LocalVar = sil.LocalVar(same_args_name, sil.Bool)(a, b, c)
        mainModule.env.define(same_args)
        val same_args_true: LocalVarAssign = LocalVarAssign(same_args, sil.TrueLit()(a, b, c))(a, b, c)
        val assign_same_args: Seq[LocalVarAssign] = same_seq map ((exp: sil.Exp) => sil.LocalVarAssign(same_args, sil.And(same_args, exp)(a, b, c))(a, b, c))

        val assign: Seq[LocalVarAssign] = (tempRets zip targets) map { (x: (sil.LocalVar, sil.LocalVar)) => sil.LocalVarAssign(x._2, x._1)(a, b, c) }
        val if_assign: ast.Stmt = sil.If(same_args, sil.Seqn(assign, Seq())(a, b, c), sil.Seqn(Seq(), Seq())(a, b, c))(a, b, c)
        sil.Seqn(Seq(same_args_true) ++ assign_same_args ++ Seq(s) ++ Seq(if_assign), Seq())(a, b, c)
      case sil.If(cond, s1, s2) =>
        val ss1 = assignVarsSil(s1).asInstanceOf[sil.Seqn]
        val ss2 = assignVarsSil(s2).asInstanceOf[sil.Seqn]
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

  // Records:
  // - exhale heaps
  // - wildcard values
  // - new version of predicates unfolded (?)
  // - values of "freshObj"
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
      case HavocImpl(Seq(v)) =>
        if (v.name.name == "ExhaleHeap") {
          val b = getVarDecl("BranchTakenForExhale", Bool)
          declareFalseAtBegin :+= b
          val pre = getVarDecl("PreExhaleHeap", heapType)
          val h = getVarDecl("ExhaleHeap", heapType)
          (Seqn(Seq(Assign(b.l, TrueLit()), Assign(pre.l, currentHeap.head), s, Assign(h.l, v))), Seq(b, pre, h))
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
      /*case If(cond, thn, els) if conditionToAvoid(cond, id_check) =>
      // (used_checks.contains(cond.name.name) && cond.name.name != check.name.name) =>
        // println("AVOID IF", cond, check)
        val (nels, l2) = determinize(els, l, check, id_check, e)
        (If(cond, thn, nels), l2)
       */
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
          val h = l.tail.tail.head
          /*val ss = If(check,
            Assert(b.l ==> (pre.l === currentHeap.head), e) ++
              Assume(v === h.l), Statements.EmptyStmt)
           */
          val ss = If(b.l,
            Assert(
              equalOnMaskFunc(pre.l, currentHeap.head.asInstanceOf[Var], currentMask.head.asInstanceOf[Var])
              //pre.l === currentHeap.head
            , e) ++
              Assume(v === h.l), Statements.EmptyStmt)
          (s ++ ss, l.tail.tail.tail)
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
          (args forall (!containsPermOrForperm(_))) && method.body.isEmpty
        case ast.Exhale(exp) => !containsPermOrForperm(exp) && (!containsWildcard(exp) || checkMono)
        case ast.Inhale(exp) => !containsPermOrForperm(exp)
        case ast.Assert(exp) => !containsPermOrForperm(exp)
        case ast.Assume(exp) => !containsPermOrForperm(exp) && !containsAcc(exp)
        case ast.Fold(acc) => !containsPermOrForperm(acc)
        case ast.Unfold(acc) => !containsPermOrForperm(acc)
        case ast.Package(_, proofScript) => syntacticFraming(proofScript, checkMono)
        case ast.Apply(_) => true
        case ast.Seqn(ss, _) => ss forall (syntacticFraming(_, checkMono))
        case ast.If(cond, thn, els) => !containsPermOrForperm(cond) && syntacticFraming(thn, checkMono) && syntacticFraming(els, checkMono)
        case ast.While(cond, invs, body) => println("While loop in syntactic condition: Should not happen!"); assert(false); false
        case ast.Label(_, _) => true
        case ast.Goto(_) =>
          println("GOTO in SYNTACTIC CHECK, maybe not supported")
          false
        case ast.NewStmt(lhs, fields) => true
        case ast.LocalVarDeclStmt(decl) => true
        case _: ast.ExtensionStmt => println("EXTENSION STMT???")
          assert(false)
          false
      }
    }
  }

  def wfMask(args: Seq[Exp], typ: Type = Bool): Exp = FuncApp(wfMask, args, typ)
  def equalOnMaskFunc(heap1: Var, heap2: Var, mask: Var): Exp = FuncApp(equalOnMask, Seq(heap1, heap2, mask), Bool)

  def sumStateNormal(mask1: Var, heap1: Var, mask2: Var, heap2: Var, mask: Var, heap: Var): Exp = {
    FuncApp(sumState, Seq(mask1, heap1, mask2, heap2, mask, heap), Bool)
  }

  def smallerState(smallMask: Var, smallHeap: Var, bigMask: Var, bigHeap: Var): Exp = {
    FuncApp(smallerState, Seq(smallMask, smallHeap, bigMask, bigHeap), Bool)
  }

  def smallerMask(smallMask: Var, bigMask: Var): Exp = {
    FuncApp(smallerMask, Seq(smallMask, bigMask), Bool)
  }

  def doubleErrorSafeMono(s: Stmt, error: VerificationError, check: Exp, id_check: Int): Stmt = {
    s match {
      case Seqn(stmts) => stmts map (doubleErrorSafeMono(_, error, check, id_check))
      case CommentBlock(c, ss) => CommentBlock(c, doubleErrorSafeMono(ss, error, check, id_check))
      // case If(cond: LocalVar, thn, els) if (used_checks.contains(cond.name.name) && cond.name.name != check.name.name) =>
      case If(cond, thn, els) if conditionToAvoid(cond, id_check) =>
        If(cond, thn, doubleErrorSafeMono(els, error, check, id_check))
      case If(cond, thn, els) => If(cond, doubleErrorSafeMono(thn, error, check, id_check), doubleErrorSafeMono(els, error, check, id_check))
      // case Assert(BinExp(e1, Implies,  _), _) if conditionToAvoid(e1, id_check) => s
      case Assert(exp, _) => Assert(exp, error)
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
        ))) ++
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
          && heap1.l === normalHeap.l
          && heap2.l === normalHeap.l
          )))
  }

  var current_exists: Option[Var] = None
  var id_checkFraming = 0
  var id_checkMono = 0

  var beginning: Boolean = true

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

  def inlineSil(s: sil.Stmt, n: Int): sil.Stmt = {

    val (a, b, c) = (s.pos, s.info, s.errT)
    s match {
      case sil.MethodCall(methodName, args, targets) if program.findMethod(methodName).body.isDefined =>
        if (n > 0) {
          val m = program.findMethod(methodName)
          val pre_body = m.body.get

          currentRenaming = Map()
          val body = alphaRename(pre_body)
          val renamedFormalArgsVars: Seq[sil.LocalVar] = (m.formalArgs map (_.localVar)) map renameVar
          val renamedFormalReturnsVars: Seq[ast.LocalVar] = (m.formalReturns map (_.localVar)) map renameVar

          val scopeArgs: Seq[ast.LocalVarDecl] = renamedFormalArgsVars map (x => sil.LocalVarDecl(x.name, x.typ)(a, b, c))
          val scopeRets: Seq[ast.LocalVarDecl] = renamedFormalReturnsVars map (x => sil.LocalVarDecl(x.name, x.typ)(a, b, c))

          val inlined_m: ast.Stmt = inlineSil(body, n - 1)

          val assignArgsPre: Seq[(sil.LocalVar, sil.Exp)] = (renamedFormalArgsVars zip args) filter ((x) => x._1 != x._2)
          val assignRetsPre: Seq[(sil.LocalVar, sil.Exp)] = (targets zip renamedFormalReturnsVars) filter ((x) => x._1 != x._2)
          val assignArgs: Seq[sil.LocalVarAssign] = assignArgsPre map (x => sil.LocalVarAssign(x._1, x._2)(a, b, c))
          val assignRets: Seq[sil.LocalVarAssign] = assignRetsPre map (x => sil.LocalVarAssign(x._1, x._2)(a, b, c))

          sil.Seqn(assignArgs ++ Seq(inlined_m) ++ assignRets, scopeArgs ++ scopeRets)(a, b, c)
        }
        else {
          sil.Inhale(sil.FalseLit()(a, b, c))(a, b, c)
        }
      case sil.While(cond, invs, body) =>
        if (n > 0) {
          val s_inl: sil.Stmt = inlineSil(body, n - 1)
          val w_inl: sil.Stmt = inlineSil(s, n - 1)
          val seq: sil.Seqn = sil.Seqn(Seq(s_inl, w_inl), Seq())(a, b, c)
          val empty: sil.Seqn = sil.Seqn(Seq(), Seq())(a, b, c)
          sil.If(cond, seq, empty)(a, b, c)
        }
        else {
          sil.Inhale(sil.Not(cond)(a, b, c))(a, b, c)
        }
      case sil.If(cond, thn, els) => sil.If(cond, inlineSil(thn, n).asInstanceOf[sil.Seqn], inlineSil(els, n).asInstanceOf[sil.Seqn])(a, b, c)
      case sil.Seqn(ss, scopedDecls) => sil.Seqn(ss map (inlineSil(_, n)), scopedDecls)(a, b, c)
      case _ => s
    }

  }

  def checkFraming(pre_orig_s: sil.Stmt, orig: ast.Stmt, checkMono: Boolean = false, checkWFM: Boolean = false, modif_vars: Seq[LocalVar] = Seq()): Stmt = {

    val orig_s: ast.Stmt = inlineSil(pre_orig_s, maxDepth - current_depth)
    println("checkFraming", current_depth, "framing", !checkMono, "length", length(orig_s))

    var ignore = false


    if (beginning && checkMono) {
      println("Ignoring first part of the code (trivial)")
      ignore = true
    }
    else if (syntacticFraming(orig_s, checkMono)) {
      if (checkMono) {
        println("Syntactically mono")
      }
      else {
        println("Syntactically framing")
      }
      if (verifier.printSC) {
        println(orig_s)
      }
      ignore = true
    }
    else if (isCheckingFraming()) {
      ignore = true
    }

    beginning = false

    if (ignore) {
      println("IGNORING...")
      Statements.EmptyStmt
    }
    else {

      if (checkMono) {id_checkMono += 1} else {id_checkFraming += 1}
      val id_error = {if (checkMono) id_checkMono else id_checkFraming}
      val errorType = {if (checkMono) "MONO" else "FRAMING"}
      println(errorType + " " + id_error)

      if (verifier.printSC) {
        println(orig_s)
      }

      val aa = orig_s.pos
      val bb = orig_s.info
      val cc = orig_s.errT

      val silExistsDecl: ast.LocalVarDecl = sil.LocalVarDecl(silNameNotUsed("exists"), sil.Bool)(aa, bb, cc)
      val exists: LocalVar = mainModule.env.define(silExistsDecl.localVar)

      //val silCheckDecl: ast.LocalVarDecl = sil.LocalVarDecl(silNameNotUsed("checkFraming"), sil.Bool)(aa, bb, cc)
      // val check: LocalVar = mainModule.env.define(silCheckDecl.localVar)
      val (check, id_check) = getCheckBool()


      // val orig_s1: sil.Stmt = sil.Seqn(Seq(sil.LocalVarAssign(silExistsDecl.localVar, sil.TrueLit()(aa, bb, cc))(aa, bb, cc),
      val orig_s1: sil.Stmt = recordVarsSil(orig_s)
        //Seq(silExistsDecl))(aa, bb, cc)
        //Seq())(aa, bb, cc)
      val orig_s2: sil.Stmt = assignVarsSil(orig_s)
      // val orig_s1 = orig_s

      val converted_vars: Seq[LocalVar] = (orig_s.writtenVars filter (v => mainModule.env.isDefinedAt(v))) map translateLocalVar
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


      val nm: VerificationError = SoundnessFailed(orig, DummyReason, if (checkWFM) "WFM" else "monoOut", id_error, errorType)
      val nf: VerificationError = SoundnessFailed(orig, DummyReason, "framing", id_error, errorType)
      val error_ignore: VerificationError = SoundnessFailed(orig, DummyReason, "monoOut (structural)", id_error, errorType)
      val nsm: VerificationError = SoundnessFailed(orig, DummyReason, "safeMono", id_error, errorType)

      declareFalseAtBegin = Seq()
      val (modif_s, l) = recordDeterminism(assumify(addIfExists(changeStateWfState(s1, exists), exists)))
      val assign_false_branches_taken: Seq[Stmt] = declareFalseAtBegin map ((x) => Assign(x.l, FalseLit()))

      val (modif_s2, ll) = determinize(doubleErrorSafeMono(s2, nsm, check, id_check), l, check, id_check, error_ignore)

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
          if (checkWFM && !simpleWFM) {
            Havoc(modif_vars)
          }
          else {
            Assume(smallerState(maskPhi2.l, heapPhi2.l, normalState._1, normalState._2))
          }
        } ++
              Assume(wfMask(Seq(maskPhi2.l))) ++
              Assume(sumStateNormal(maskPhi1.l, heapPhi1.l, maskR.l, heapR.l, maskPhi2.l, heapPhi2.l)) ++
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
          Assert(exists && smallerState(maskPhi1.l, heapPhi1.l, normalState._1, normalState._2), nm) ++
          Assert(equalSeq(converted_vars, tempVars), nm) ++ {
        if (!checkMono) {
            Assume(
              sumStateNormal(maskPhi1.l, heapPhi1.l, maskR.l, heapR.l, sumState._1.l, sumState._2.l)
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
      mainModule.env.undefine(silExistsDecl.localVar)
      r
    }
  }

  def inlinable(stmt: sil.Stmt): Boolean = {
    stmt match {
      case mc@sil.MethodCall(methodName, _, _) =>
        val method = verifier.program.findMethod(methodName)
        method.body.isDefined
      case w@sil.While(_, _, _) => true
      case i@sil.If(_, thn, els) => inlinable(thn) || inlinable(els)
      case sil.Seqn(ss, _) => ss.exists(inlinable)
      case _ => false
    }
  }

  def groupNonInlinableStmts(ss: Seq[sil.Stmt], orig_s: sil.Stmt): Seq[sil.Stmt] = {

    if (syntacticFraming(inlineSil(orig_s, maxDepth - current_depth))) {
      ss
    }
    else {

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
      r
    }
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

  def inlineLoop(w: sil.Stmt, cond: ast.Exp, invs: Seq[ast.Exp], body: ast.Seqn): Stmt = {
    println("inlineLoop", current_depth, cond, "length", length(w))
    val guard = translateExp(cond)

    val depth = maxDepth - current_depth

    if (current_depth == maxDepth) {
      val cond_neg: sil.Stmt = sil.Inhale(sil.Not(cond)(cond.pos, cond.info, cond.errT))(cond.pos, cond.info, cond.errT)
      val wfm: Stmt = checkFraming(cond_neg, w, true, true)
      MaybeCommentBlock("0: Check SC and cut branch (loop)", wfm ++ Assume(guard ==> FalseLit()))
    }
    else {
      current_depth += 1

      val r1 = checkFraming(body, w)

      val modif_vars: Seq[LocalVar] = (w.writtenVars filter (v => mainModule.env.isDefinedAt(v))) map translateLocalVar

      val check_wfm = {
        val cond_pos: sil.Stmt = sil.Inhale(cond)(cond.pos, cond.info, cond.errT)
        val cond_neg: sil.Stmt = sil.Inhale(sil.Not(cond)(cond.pos, cond.info, cond.errT))(cond.pos, cond.info, cond.errT)
        MaybeCommentBlock("Check WFM", checkFraming(cond_pos, w, true, true, modif_vars=modif_vars)
          ++ checkFraming(cond_neg, w, true, true, modif_vars=modif_vars))
      }

      val oldCheckingFraming = checkingFraming
      if (!inlinable(body)) {
        checkingFraming = true
      }
      val r2 = MaybeCommentBlock(depth + ": Loop body", stmtModule.translateStmt(body))
      checkingFraming = oldCheckingFraming
      val remaining = inlineLoop(w, cond, invs, body)
      current_depth -= 1
      MaybeCommentBlock(depth + ": Inlined loop", check_wfm ++ If(guard, r1 ++ getBoundedComplete() ++ r2 ++ remaining, Statements.EmptyStmt) ++ getBoundedComplete())
    }
  }

  def inlineMethod(m: Method, args: Seq[ast.Exp], targets: Seq[ast.LocalVar]): Stmt = {
    println("inlineMethod", current_depth, m.name, "length", length(m.body.get))
    if (current_depth == maxDepth) {
      MaybeComment("0: Cut branch (method call)", Assume(FalseLit()))
    }
    else {
      current_depth += 1
      val other_vars: Seq[ast.LocalVar] = (m.formalArgs map (_.localVar)) ++ (m.formalReturns map (_.localVar))

      currentRenaming = Map()
      val pre_body = m.body.get
      val body = alphaRename(pre_body)
      val renamedFormalArgsVars: Seq[ast.LocalVar] = (m.formalArgs map (_.localVar)) map renameVar
      val renamedFormalReturnsVars: Seq[ast.LocalVar] = ((m.formalReturns map (_.localVar))) map renameVar

      renamedFormalArgsVars foreach {
        (x: ast.LocalVar) => if (!mainModule.env.isDefinedAt(x)) {
          mainModule.env.define(x)
        }
      }

      renamedFormalReturnsVars foreach {
        (x: ast.LocalVar) => if (!mainModule.env.isDefinedAt(x)) {
          mainModule.env.define(x)
        }
      }

      val r1 = checkFraming(body, body)
      val oldCheckingFraming = checkingFraming
      if (!inlinable(body)) {
        checkingFraming = true
      }
      val r2 = stmtModule.translateStmt(body)
      checkingFraming = oldCheckingFraming

      current_depth -= 1

      val assignArgsPre: Seq[(Exp, Exp)] = ((renamedFormalArgsVars map translateExp) zip (args map translateExp)) filter ((x) => x._1 != x._2)
      val assignRetsPre: Seq[(Exp, Exp)] = ((targets map translateExp) zip (renamedFormalReturnsVars map translateExp)) filter ((x) => x._1 != x._2)

      val assignArgs = assignArgsPre map (x => Assign(x._1, x._2))
      val assignRets = assignRetsPre map (x => Assign(x._1, x._2))

      renamedFormalArgsVars foreach {
        (x: ast.LocalVar) => if (mainModule.env.isDefinedAt(x)) {
          mainModule.env.undefine(x)
        }
      }
      renamedFormalReturnsVars foreach {
        (x: ast.LocalVar) => if (mainModule.env.isDefinedAt(x)) {
          mainModule.env.undefine(x)
        }
      }

      Seqn(assignArgs) ++ r1  ++ getBoundedComplete() ++ r2 ++ Seqn(assignRets) ++ getBoundedComplete()
    }
  }

  // ----------------------------------------------------------------
  // RENAMING
  // ----------------------------------------------------------------

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

  def readVarsDecl(d: ast.Declaration): Seq[ast.LocalVar] = {
    d match {
      case decl: ast.LocalVarDecl => Seq(decl.localVar)
    }
  }

  var currentRenaming: Map[ast.LocalVar, ast.LocalVar] = Map()

  def newString(s: String): String = {
    val definedVars = (mainModule.env.allDefinedVariables()) map (_.name)
    if (definedVars.contains(s)) {
      newString(s + "_r")
    }
    else {
      s
    }
  }

  def renameVar(x: ast.LocalVar): ast.LocalVar = {
    if (!currentRenaming.contains(x)) {
      val new_name = newString(x.name)
      val xx = ast.LocalVar(new_name, x.typ)(x.pos, x.info, x.errT)
      currentRenaming += (x -> xx)
    }
    currentRenaming(x)
  }

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

  def renameDecl(d: sil.Declaration): sil.Declaration = {
    d match {
      case decl: ast.LocalVarDecl =>
        val new_x = renameVar(decl.localVar)
        ast.LocalVarDecl(new_x.name, new_x.typ)(decl.pos, decl.info, decl.errT)
      case _ => println("OTHER TYPE OF RENAME DECL", d)
        d
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
        // println("Rename exp", exp, renameExp(exp))
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
      case ast.Label(name, scope) => ast.Label(name + "_check", scope map renameExp)(a, b, c)
      case ast.Goto(_) => s
      case ast.NewStmt(lhs, fields) => ast.NewStmt(renameVar(lhs), fields)(a, b, c)
      case ast.LocalVarDeclStmt(decl) => ast.LocalVarDeclStmt(renameDecl(decl).asInstanceOf[sil.LocalVarDecl])(a, b, c)
      case _: ast.ExtensionStmt => s // Probably useless
    }
  }

}
