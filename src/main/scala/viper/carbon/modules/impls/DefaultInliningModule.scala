package viper.carbon.modules.impls

import viper.carbon.modules.{InliningModule, StatelessComponent, StmtModule}
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Havoc, MaybeComment, _}
import viper.carbon.verifier.Verifier
import Implicits._
import viper.carbon.modules.components.Component
import viper.silver.ast.{CurrentPerm, ErrorTrafo, FieldAccess, FieldAssign, ForPerm, Info, LocalVarAssign, LocationAccess, Method, Position, WildcardPerm}
import viper.silver.verifier.{DummyReason, PartialVerificationError, VerificationError, errors}
import viper.silver.ast.utility.Expressions
import viper.silver.verifier.errors.SoundnessFailed
import viper.silver.ast

class DefaultInliningModule(val verifier: Verifier) extends InliningModule with Component {

  import verifier._
  import expModule._

  override def start() {
    // register(this)
  }

  override def reset(): Unit = {}

  val lblNamespace = verifier.freshNamespace("stmt.lbl")

  def name = "Inlining module"


  var current_depth = 0

  def maxDepth: Int = verifier.staticInlining match {
    case None => 0
    case Some(n) => n
  }

  var used_checks: Set[String] = Set()

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
        case ast.While(cond, invs, body) => false
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

  // In order to remove some "indeterminism"
  def recordExhaleHeaps(s: Stmt): (Stmt, Seq[LocalVarDecl]) = {
    s match {
      case Seqn(stmts) => val r = (stmts map recordExhaleHeaps)
        (Seqn(r map (_._1)), r flatMap (_._2))
      case Assume(BinExp(v: LocalVar, LtCmp, right)) if (v.name.name == "wildcard") =>
        // Exhale wildcard
        val w = verifier.permModule.newWildcard()
        val p = verifier.permModule.newPermwild()

        val noPerm = BinExp(IntLit(0), Div, IntLit(1))
        //(LocalVarWhereDecl(w.l.name, w.l > noPerm) ++
        (Assign(w.l, v) ++ Assign(p.l, right) ++ s, Seq(w, p))
      case CommentBlock(c, ss) =>
        val (sss, l) = recordExhaleHeaps(ss)
        (CommentBlock(c, sss), l)
      case If(cond, thn, els) =>
        val (nthn, l1) = recordExhaleHeaps(thn)
        val (nels, l2) = recordExhaleHeaps(els)
        (If(cond, nthn, nels), l1 ++ l2)
      case Assign(LocalVar(Identifier("perm", n1), typ1), v: LocalVar) if (v.name.name == "wildcard") =>
        // Inhale wildcard
        val w = verifier.permModule.newWildcard()
        // val noPerm = BinExp(IntLit(0), Div, IntLit(1))
        // (LocalVarWhereDecl(w.l.name, w.l > noPerm) ++
        (Assign(w.l, v) ++ s, Seq(w))
      case HavocImpl(Seq(v)) =>
        if (v.name.name == "ExhaleHeap") {
          val h = verifier.permModule.newExhaleHeap()
          (Seqn(Seq(s, Assign(h.l, v))), Seq(h))
        }
        else if (v.name.name == "newVersion") {
          val nv = verifier.permModule.newVar(v.typ)
          (Seqn(Seq(s, Assign(nv.l, v))), Seq(nv))
        }
        /*
       else if (v.name.name == "wildcard") {
         val w = verifier.permModule.newWildcard()
         (Seqn(Seq(s, Assign(w.l, v))), Seq(w))
       }
        */
        else if (v.name.name == "freshObj") {
          val obj = verifier.permModule.newFreshObj()
          (Seqn(Seq(s, Assign(obj.l, v))), Seq(obj))
        }
        else {
          (s, Seq())
        }
      case ss => (ss, Seq())
    }
  }

  def assumeExhaleHeap(s: Stmt, l: Seq[LocalVarDecl], check: LocalVar, e: VerificationError): (Stmt, Seq[LocalVarDecl]) = {
    s match {
      case Seqn(stmts) =>
        var new_s: Seq[Stmt] = Seq()
        var ll = l
        for (ss <- stmts) {
          val (sss, lll) = assumeExhaleHeap(ss, ll, check, e)
          ll = lll
          new_s = new_s :+ sss
        }
        (Seqn(new_s), ll)
      case CommentBlock(c, ss) =>
        val (sss, ll) = assumeExhaleHeap(ss, l, check, e)
        (CommentBlock(c, sss), ll)
      case Assume(BinExp(w: LocalVar, LtCmp, right)) if (w.name.name == "wildcard") =>
        val old_w = l.head
        val p = l.tail.head

        /*
        if (checkFraming1) {
          assume wildcard == wildcard2 * (Mask[x_r_7, f_6] / permWild_1);
          assert permWild_1 * Mask[x_r_7, f_6] - wildcard2 * Mask[x_r_7, f_6] >= permWild_1 * permWild_1 - permWild_1 * wildcard2;
        }
        else {
          assume wildcard < Mask[x_r_7, f_6];
        }
         */
        // val s0 = Assume((right - w) / right === (p.l - old_w.l) / p.l)
        //val s1 = Assume((right - w) / right === (p.l - old_w.l) / p.l)
        // val s1 = Assert(right - w === ((p.l - old_w.l) / p.l) * right, e)
        //val s2 = Assert(right >= w, e)
        //val s3 = Assert(right - w >= p.l - old_w.l, e)
        // val s2 = Assert(right - w >= p.l - old_w.l, e)
        val s1 = Assert(right >= p.l, e)
        val s2 = Assume(right - w >= p.l - old_w.l)

        (If(check, s1 ++ s2, s), l.tail.tail)
      case If(cond: LocalVar, thn, els) if (used_checks.contains(cond.name.name) && cond.name.name != check.name.name) =>
        // println("AVOID IF", cond, check)
        val (nels, l2) = assumeExhaleHeap(els, l, check, e)
        (If(cond, thn, nels), l2)
      case If(cond, thn, els) =>
        val (nthn, l1) = assumeExhaleHeap(thn, l, check, e)
        val (nels, l2) = assumeExhaleHeap(els, l1, check, e)
        (If(cond, nthn, nels), l2)
      case Assign(LocalVar(Identifier("perm", n1), typ1), v: LocalVar) if (v.name.name == "wildcard") =>
        // Inhale wildcard
        (If(check, Assign(v, l.head.l), Statements.EmptyStmt) ++ s, l.tail)
      case HavocImpl(Seq(v)) =>
        if (v.name.name == "ExhaleHeap" || v.name.name == "freshObj" || v.name.name == "newVersion") {
          val ss = If(check, Assume(v === l.head.l), Statements.EmptyStmt)
          (s ++ ss, l.tail)
        }
        else {
          (s, l)
        }
      case _ => (s, l)
    }
  }

  def tempState: (LocalVarDecl, LocalVarDecl) = permModule.tempState()

  def normalState: (Var, Var) = (permModule.currentMask.head.asInstanceOf[Var], heapModule.currentHeap.head.asInstanceOf[Var])

  // heapModule.freshTempState("").head)

  var id_checkFraming = 1
  var id_checkMono = 1

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

  // Also for methods
  var recordedScopes: Seq[Seq[sil.LocalVar]] = Seq()

  def removeAssumeRecordVarsSil(s: sil.Stmt, exists: sil.LocalVar): sil.Stmt = {
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
        sil.Seqn(assign ++ ss map (removeAssumeRecordVarsSil(_, exists)), scopedDecls)(a, b, c)
      case sil.Inhale(exp) if (exp.isPure) => sil.LocalVarAssign(exists, sil.And(exists, exp)(exp.pos, exp.info, exp.errT))(a, b, c)
      // Assume
      case sil.MethodCall(_, _, targets: Seq[ast.LocalVar]) =>
        val tempVars: Seq[ast.LocalVar] = targets map ((x: ast.LocalVar) => {
          val name = silNameNotUsed(x.name + "_temp")
          val tempLocalVar = sil.LocalVar(name, x.typ)(x.pos, x.info, x.errT)
          mainModule.env.define(tempLocalVar)
          tempLocalVar
        })
        recordedScopes :+= tempVars
        val assign: Seq[LocalVarAssign] = (tempVars zip targets) map { (x: (sil.LocalVar, sil.LocalVar)) => sil.LocalVarAssign(x._1, x._2)(a, b, c) }
        sil.Seqn(Seq(s) ++ assign, Seq())(a, b, c)
      case sil.If(cond, s1: sil.Seqn, s2: sil.Seqn) =>
        val ss1 = removeAssumeRecordVarsSil(s1, exists).asInstanceOf[sil.Seqn]
        val ss2 = removeAssumeRecordVarsSil(s2, exists).asInstanceOf[sil.Seqn]
        sil.If(cond, ss1, ss2)(a, b, c)
      case _ => sil.If(exists, sil.Seqn(s, Seq())(a, b, c), silEmptyStmt()(a, b, c))(a, b, c)
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
        sil.Seqn(assign ++ ss map assignVarsSil, scopedDecls)(a, b, c)
      case sil.MethodCall(_, _, targets: Seq[ast.LocalVar]) =>
        val tempVars: Seq[ast.LocalVar] = recordedScopes.head
        assert(targets.size == tempVars.size)
        recordedScopes = recordedScopes.tail
        val assign: Seq[LocalVarAssign] = (tempVars zip targets) map { (x: (sil.LocalVar, sil.LocalVar)) => sil.LocalVarAssign(x._2, x._1)(a, b, c) }
        sil.Seqn(Seq(s) ++ assign, Seq())(a, b, c)
      case sil.If(cond, s1, s2) =>
        val ss1 = assignVarsSil(s1).asInstanceOf[sil.Seqn]
        val ss2 = assignVarsSil(s2).asInstanceOf[sil.Seqn]
        sil.If(cond, ss1, ss2)(a, b, c)
      case _ => s
    }
  }


  // Only changes "assume state" into "exists := exists && wfState"
  def removeAssume(s: Stmt, exists: LocalVar): Stmt = {
    s match {
      case Seqn(stmts) => stmts map (removeAssume(_, exists))
      case Assume(FuncApp(Identifier("state", namespace), args, typ)) =>
        Assign(exists, exists && permModule.wfMask(args.tail, typ))
      case CommentBlock(c, ss) =>
        CommentBlock(c, removeAssume(ss, exists))
      case If(cond, thn, els) => If(cond, removeAssume(thn, exists), removeAssume(els, exists))
      case NondetIf(thn, els) => NondetIf(removeAssume(thn, exists), removeAssume(els, exists))
      case ss => ss
    }
  }

  def modifError(s: Stmt, error: VerificationError, check: Var): Stmt = {
    s match {
      case Seqn(stmts) => stmts map (modifError(_, error, check))
      case CommentBlock(c, ss) => CommentBlock(c, modifError(ss, error, check))
      case If(cond, thn, els) => If(cond, modifError(thn, error, check), modifError(els, error, check))
      case Assert(exp, err) => Seqn(Assert(check ==> exp, error) ++ Assert(exp, err))
      case _ => s
    }
  }

  def isEmpty(s: Stmt): Boolean = {
    s match {
      case Seqn(stmts) => stmts forall isEmpty
      case CommentBlock(_, ss) => isEmpty(ss)
      case If(_, thn, els) => isEmpty(thn) && isEmpty(els)
      case _ => false
    }
  }

  def removeEmpty(s: Stmt): Stmt = {
    s match {
      case Seqn(stmts) => (stmts filter (!isEmpty(_))) map removeEmpty
      case CommentBlock(c, ss) => if (isEmpty(ss)) {
        Statements.EmptyStmt
      } else {
        CommentBlock(c, removeEmpty(ss))
      }
      case If(cond, thn, els) => if (isEmpty(thn) && isEmpty(els)) {
        Statements.EmptyStmt
      } else {
        If(cond, removeEmpty(thn), removeEmpty(els))
      }
      case ss => ss
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

  // TODO CHANGE FOR WFM
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

  var id_wfm = 0

  def checkMonoAssume(orig_s: ast.Stmt, orig: ast.Stmt): Stmt = {

    checkingFraming = true

    id_wfm += 1

    val converted_vars: Seq[LocalVar] = (orig_s.writtenVars filter (v => mainModule.env.isDefinedAt(v))) map translateLocalVar
    val oldVars = converted_vars map ((v: LocalVar) => verifier.permModule.newVar(v.typ).l)
    val tempVars = converted_vars map ((v: LocalVar) => verifier.permModule.newVar(v.typ).l)

    val pair: (LocalVarDecl, LocalVarDecl, LocalVarDecl, LocalVarDecl, LocalVarDecl, LocalVarDecl) = verifier.permModule.newPhiRPair()
    used_checks += pair._1.l.name.name

    val s = stmtModule.translateStmt(orig_s)

    val (check, exists, maskPhi, heapPhi, maskR, heapR) = pair

    val nm: VerificationError = SoundnessFailed(orig, DummyReason, "monoOut", id_wfm, "WFM")
    val error_ignore: VerificationError = SoundnessFailed(orig, DummyReason, "true by construct", id_wfm, "WFM")
    // Replaced by assumes
    val nsm: VerificationError = SoundnessFailed(orig, DummyReason, "safeMono", id_wfm, "WFM")

    val modif_s = assumify(removeAssume(s, exists.l))

    val r = MaybeComment(id_wfm + ": Check WFM",
      Havoc(Seq(check.l)) ++
        If(check.l,
          assignSeqToSeq(oldVars, converted_vars) ++
            Assign(exists.l, TrueLit()) ++
            Havoc((Seq(maskPhi, heapPhi) map (_.l)).asInstanceOf[Seq[Var]]) ++
            Assume(verifier.permModule.sumStateNormal(maskPhi.l, heapPhi.l, maskR.l, heapR.l, normalState._1, normalState._2)) ++
            Assume(verifier.permModule.smallerState(maskPhi.l, heapPhi.l, normalState._1, normalState._2)) ++
            Assume(verifier.permModule.wfMask(Seq(maskPhi.l))) ++
            MaybeComment("Record current state", Assign(tempState._1.l, normalState._1) ++ Assign(tempState._2.l, normalState._2)) ++
            MaybeComment("Change state", Assign(normalState._1, maskPhi.l) ++ Assign(normalState._2, heapPhi.l)) ++

            MaybeComment("Small statement without assume", modif_s) ++

            MaybeComment("Back to phi", Assign(maskPhi.l, normalState._1) ++ Assign(heapPhi.l, normalState._2)) ++
            assignSeqToSeq(tempVars, converted_vars) ++
            MaybeComment("Back to current state", Assign(normalState._1, tempState._1.l) ++ Assign(normalState._2, tempState._2.l)) ++
            assignSeqToSeq(converted_vars, oldVars) ++

            MaybeComment("Normal statement", modifError(s, nsm, check.l)) ++

            Assert(exists.l && permModule.smallerState(maskPhi.l, heapPhi.l, normalState._1, normalState._2), nm) ++
            Assert(equalSeq(converted_vars, tempVars), nm) ++
            Assume(FalseLit())
          ,
          Statements.EmptyStmt))

    checkingFraming = false
    r
  }

  def checkFraming(orig_s: sil.Stmt, orig: ast.Stmt, checkMono: Boolean = false, checkWFM: Boolean = false): Stmt = {

    println()
    println("checkFraming", current_depth, "checkMono", checkMono)
    println(orig_s)
    println()
    println()

    if (syntacticFraming(orig_s, checkMono)) {
      if (checkMono) {
        println("Syntactically mono", orig_s)
      }
      else {
        println("Syntactically framing", orig_s)
      }
      if (checkWFM) {
        Statements.EmptyStmt
      }
      else {
        stmtModule.translateStmt(orig_s)
      }
    }
    else {

      val aa = orig_s.pos
      val bb = orig_s.info
      val cc = orig_s.errT

      val silExistsDecl: ast.LocalVarDecl = sil.LocalVarDecl(silNameNotUsed("exists"), sil.Bool)(aa, bb, cc)
      // val silExistsDecl: ast.LocalVarDecl = sil.LocalVarDecl("exists", sil.Bool)(aa, bb, cc)

      val exists = mainModule.env.define(silExistsDecl.localVar)

      val orig_s1: sil.Stmt = sil.Seqn(Seq(sil.LocalVarAssign(silExistsDecl.localVar, sil.TrueLit()(aa, bb, cc))(aa, bb, cc),
        removeAssumeRecordVarsSil(orig_s, silExistsDecl.localVar)),
        //Seq(silExistsDecl))(aa, bb, cc)
        Seq())(aa, bb, cc)
      val orig_s2: sil.Stmt = assignVarsSil(orig_s)
      // val orig_s1 = orig_s

      val converted_vars: Seq[LocalVar] = (orig_s.writtenVars filter (v => mainModule.env.isDefinedAt(v))) map translateLocalVar
      val oldVars = converted_vars map ((v: LocalVar) => verifier.permModule.newVar(v.typ).l)
      val tempVars = converted_vars map ((v: LocalVar) => verifier.permModule.newVar(v.typ).l)

      val pair: (LocalVarDecl, LocalVarDecl, LocalVarDecl, LocalVarDecl, LocalVarDecl, LocalVarDecl) = verifier.permModule.newPhiRPair()
      used_checks += pair._1.l.name.name

      var s1: Stmt = Statements.EmptyStmt
      var s2: Stmt = Statements.EmptyStmt
      checkingFraming = true
      if (checkMono || !inlinable(orig_s)) {
        s1 = stmtModule.translateStmt(orig_s1)
        s2 = stmtModule.translateStmt(orig_s2)
      }
      else {
        s1 = stmtModule.translateStmt(orig_s1)
        checkingFraming = false
        s2 = stmtModule.translateStmt(orig_s2)
        checkingFraming = true
      }

      s1 = s1.optimize.asInstanceOf[Stmt]
      s2 = s2.optimize.asInstanceOf[Stmt]

      val (check, _, maskPhi, heapPhi, maskR, heapR) = pair

      val id_error = {
        if (checkMono) {
          id_checkMono
        } else {
          id_checkFraming
        }
      }
      val errorType = {
        if (checkMono) {
          "MONO"
        } else {
          "FRAMING"
        }
      }

      val nm: VerificationError = SoundnessFailed(orig, DummyReason, "monoOut", id_error, errorType)
      val nf: VerificationError = SoundnessFailed(orig, DummyReason, "framing", id_error, errorType)
      val error_ignore: VerificationError = SoundnessFailed(orig, DummyReason, "ignore", id_error, errorType)
      // Replaced by assumes
      val nsm: VerificationError = SoundnessFailed(orig, DummyReason, "safeMono", id_error, errorType)

      val (modif_s, l) = recordExhaleHeaps(removeEmpty(assumify(removeAssume(s1, exists))))
      val (modif_s2, ll) = assumeExhaleHeap(modifError(s2, nsm, check.l), l, check.l, error_ignore)

      assert(ll.isEmpty)

      val smallStmt: Seq[Stmt] =
        assignSeqToSeq(oldVars, converted_vars) ++ {
          if (checkMono) {
            Havoc((Seq(maskPhi, heapPhi) map (_.l)).asInstanceOf[Seq[Var]]) ++
              Assume(verifier.permModule.sumStateNormal(maskPhi.l, heapPhi.l, maskR.l, heapR.l, normalState._1, normalState._2)) ++
              Assume(verifier.permModule.smallerState(maskPhi.l, heapPhi.l, normalState._1, normalState._2)) ++
              Assume(verifier.permModule.wfMask(Seq(maskPhi.l)))
          }
          else {
            Havoc((Seq(maskPhi, heapPhi, maskR, heapR) map (_.l)).asInstanceOf[Seq[Var]]) ++
              Assume(verifier.permModule.sumStateNormal(maskPhi.l, heapPhi.l, maskR.l, heapR.l, normalState._1, normalState._2)) ++
              Assume(verifier.permModule.wfMask(Seq(maskPhi.l))) ++
              Assume(verifier.permModule.wfMask(Seq(maskR.l)))
          }
        } ++
          MaybeComment("Record current state", Assign(tempState._1.l, normalState._1) ++ Assign(tempState._2.l, normalState._2)) ++
          MaybeComment("Change state", Assign(normalState._1, maskPhi.l) ++ Assign(normalState._2, heapPhi.l)) ++
          MaybeComment("Small statement without assume", modif_s) ++
          MaybeComment("Back to phi", Assign(maskPhi.l, normalState._1) ++ Assign(heapPhi.l, normalState._2)) ++
          assignSeqToSeq(tempVars, converted_vars) ++
          MaybeComment("Back to current state", Assign(normalState._1, tempState._1.l) ++ Assign(normalState._2, tempState._2.l)) ++
          assignSeqToSeq(converted_vars, oldVars)

      val normalStmt: Seqn = MaybeComment("Normal statement", modif_s2)

      val endCheck: Seq[Stmt] = Assert(exists && permModule.smallerState(maskPhi.l, heapPhi.l, normalState._1, normalState._2), nm) ++
        Assert(equalSeq(converted_vars, tempVars), nm) ++ {
        if (!checkMono) {
          Havoc(Seq(tempState._1.l, tempState._2.l)) ++
            Assume(
              verifier.permModule.sumStateNormal(maskPhi.l, heapPhi.l, maskR.l, heapR.l, tempState._1.l, tempState._2.l)
            ) ++
            Assert(exists && permModule.smallerState(tempState._1.l, tempState._2.l, normalState._1, normalState._2), nf)
        }
        else {
          Statements.EmptyStmt
        }
      } ++
        Assume(FalseLit())

      val r = {
        if (checkWFM) {
          MaybeComment(id_checkFraming + ": Check WFM",
            Havoc(Seq(check.l)) ++ If(check.l, smallStmt ++ normalStmt ++ endCheck, Statements.EmptyStmt))
        }
        else {
          MaybeComment(id_checkFraming + ": Check " + {
            if (checkMono) "MONO" else "FRAMING"
          },
            Havoc(Seq(check.l)) ++ If(check.l, smallStmt, Statements.EmptyStmt) ++ normalStmt ++ If(check.l, endCheck, Statements.EmptyStmt))
        }
      }

      if (checkMono) {
        id_checkMono += 1
      }
      else {
        id_checkFraming += 1
      }
      checkingFraming = false
      mainModule.env.undefine(silExistsDecl.localVar)
      r
    }
  }

  def inlineLoop(w: sil.Stmt, cond: ast.Exp, invs: Seq[ast.Exp], body: ast.Seqn): Stmt = {
    println("inlineLoop", current_depth, cond)
    val guard = translateExp(cond)

    val depth = maxDepth - current_depth

    if (current_depth == maxDepth) {
      val cond_neg: sil.Stmt = sil.Inhale(sil.Not(cond)(cond.pos, cond.info, cond.errT))(cond.pos, cond.info, cond.errT)
      val wfm: Stmt = {
        if (!isCheckingFraming()) {
          checkFraming(cond_neg, w, true, true)
        }
        else {
          Statements.EmptyStmt
        }
      }
      MaybeCommentBlock("0: Check SC and cut branch (loop)", wfm ++ Assume(guard ==> FalseLit()))
    }
    else {
      current_depth += 1

      val check_wfm = {
        if (!isCheckingFraming()) {
          val cond_pos: sil.Stmt = sil.Inhale(cond)(cond.pos, cond.info, cond.errT)
          val cond_neg: sil.Stmt = sil.Inhale(sil.Not(cond)(cond.pos, cond.info, cond.errT))(cond.pos, cond.info, cond.errT)
          MaybeCommentBlock("Check WFM", checkFraming(cond_pos, w, true, true) ++ checkFraming(cond_neg, w, true, true))
        }
        else {
          Statements.EmptyStmt
        }
      }

      val r = {
        if (!isCheckingFraming()) {
          checkFraming(body, w)
        }
        else {
          MaybeCommentBlock(depth + ": Loop body", stmtModule.translateStmt(body))
        }
      }
      val remaining = inlineLoop(w, cond, invs, body)
      current_depth -= 1
      MaybeCommentBlock(depth + ": Inlined loop", check_wfm ++ If(guard, r ++ remaining, Statements.EmptyStmt))
    }
  }

  def readVarsExp(e: ast.Exp): Seq[ast.LocalVar] = {
    e match {
      case ast.Let(decl, e1, e2) => Seq(decl.localVar)
      case ast.LocalVar(name, typ) => Seq(ast.LocalVar(name, typ)(e.pos, e.info, e.errT))
      case ast.FieldAccessPredicate(e1, e2) => readVarsExp(e1) ++ readVarsExp(e2)
      case ast.BinExp(e1, e2) => readVarsExp(e1) ++ readVarsExp(e2)
      case ast.UnExp(e) => readVarsExp(e)
      case ast.CurrentPerm(e) => readVarsExp(e)
      case ast.FieldAccess(e1, _) => readVarsExp(e1)
      case _: ast.Literal => Seq()
      case _: ast.AbstractConcretePerm => Seq()
      case ast.WildcardPerm() => Seq()
      case ast.FuncApp(_, args) => (args map readVarsExp).fold(Seq())(_ ++ _)
      case ast.CondExp(e1, e2, e3) => readVarsExp(e1) ++ readVarsExp(e2) ++ readVarsExp(e3)
      case ast.Applying(ast.MagicWand(e1, e2), body) => readVarsExp(e1) ++ readVarsExp(e2) ++ readVarsExp(body)
      case ast.EmptySeq(_) => Seq()
      case ast.EmptySet(_) => Seq()
      case _: ast.ExtensionExp => Seq()
      case ast.DomainFuncApp(_, args, _) => (args map readVarsExp).fold(Seq())(_ ++ _)
      case ast.EmptyMultiset(_) => Seq()
      case ast.EpsilonPerm() => Seq()
      case ast.Exists(_, _, e) => readVarsExp(e)
      case ast.ExplicitMultiset(elems) => (elems map readVarsExp).fold(Seq())(_ ++ _)
      case ast.ExplicitSet(elems) => (elems map readVarsExp).fold(Seq())(_ ++ _)
      case ast.ExplicitSeq(elems) => (elems map readVarsExp).fold(Seq())(_ ++ _)
      case ast.ForPerm(_, _, body) => readVarsExp(body)
      case ast.Forall(_, _, e) => readVarsExp(e)
      case ast.InhaleExhaleExp(in, ex) => readVarsExp(in) ++ readVarsExp(ex)
      case ast.PredicateAccess(args, _) => (args map readVarsExp).fold(Seq())(_ ++ _)
      case ast.PredicateAccessPredicate(ast.PredicateAccess(args, _), perm) =>
        (args map readVarsExp).fold(Seq())(_ ++ _) ++ readVarsExp(perm)
      case ast.RangeSeq(low, high) => readVarsExp(low) ++ readVarsExp(high)
      case ast.Result(_) => Seq()
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

  def seqSeqToSeq(s: Seq[Seq[ast.LocalVar]]): Seq[ast.LocalVar] = {
    s.fold(Seq())(_ ++ _)
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
    val vars = readVarsExp(exp)
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
      case ast.Inhale(exp) => ast.Inhale(renameExp(exp))(a, b, c)
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

  def inlineMethod(m: Method, args: Seq[ast.Exp], targets: Seq[ast.LocalVar]): Stmt = {
    println("inlineMethod", current_depth, m.name)
    if (current_depth == maxDepth) {
      MaybeComment("0: Cut branch (method call)", Assume(FalseLit()))
    }
    else {
      current_depth += 1
      val other_vars: Seq[ast.LocalVar] = (m.formalArgs map (_.localVar)) ++ (m.formalReturns map (_.localVar))

      currentRenaming = Map()
      val body = alphaRename(m.body.get)
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

      val r = {
        if (!isCheckingFraming()) {
          checkFraming(body, body)
        }
        else {
          stmtModule.translateStmt(body)
        }
      }
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

      Seqn(assignArgs) ++
        r ++
        Seqn(assignRets)
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
