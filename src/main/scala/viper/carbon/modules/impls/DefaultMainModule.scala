// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.silver.ast.utility.Expressions
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._

import java.text.SimpleDateFormat
import java.util.Date
import viper.carbon.boogie.CommentedDecl
import viper.carbon.boogie.Procedure
import viper.carbon.boogie.Program
import viper.carbon.verifier.Environment
import viper.silver.verifier.{TypecheckerWarning, errors}
import viper.carbon.verifier.Verifier
import viper.silver.ast.HasLineColumn
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.reporter.{Reporter, WarningsDuringTypechecking}

import scala.collection.mutable

/**
 * The default implementation of a [[viper.carbon.modules.MainModule]].
 */
class DefaultMainModule(val verifier: Verifier) extends MainModule with StatelessComponent {

  import verifier._
  import typeModule._
  import stmtModule._
  import exhaleModule._
  import heapModule._
  import funcPredModule._
  import domainModule._
  import expModule._

  def name = "Main module"

  override val silVarNamespace = verifier.freshNamespace("main.silver")
  implicit val mainNamespace = verifier.freshNamespace("main")

  override def translateLocalVarSig(typ:sil.Type, v:sil.LocalVar): LocalVarDecl = {
    val t: Type = translateType(typ)
    val name: Identifier = env.get(v).name
    LocalVarDecl(name, t)
  }

  override def translate(p: sil.Program, reporter: Reporter): (Program, Map[String, Map[String, String]]) = {

    def replaceInhExhWithTrue(e: sil.Exp) : sil.Exp = {
      e.transform(
        {
          case inhExh: sil.InhaleExhaleExp => sil.TrueLit()(inhExh.pos, inhExh.info, inhExh.errT)
        }
      )
    }

    def replaceInhExhWithTrueSeq(es: Seq[sil.Exp]) : Seq[sil.Exp] =
      es.map(replaceInhExhWithTrue).filter(e => !e.equals(sil.TrueLit()()))

    val progTriggersWithoutInhExhSpec =
      p.transform(
        {
          case f: sil.Forall => {
            val res = f.autoTrigger
            if (res.triggers.isEmpty) {
              reporter.report(WarningsDuringTypechecking(Seq(TypecheckerWarning("No triggers provided or inferred for quantifier.", res.pos))))
            }
            res
          }
          case e: sil.Exists => {
            val res = e.autoTrigger
            if (res.triggers.isEmpty) {
              reporter.report(WarningsDuringTypechecking(Seq(TypecheckerWarning("No triggers provided or inferred for quantifier.", res.pos))))
            }
            res
          }
          case m: sil.Method =>
            /**
              * For all potentially inlined methods except the entry method:
              * Replace inhale-exhale assertions in specifications with "true", since taking them into account
              * for inlining does not work in the standard approach.
              * Specifications for abstract methods are left unchanged (since they cannot be inlined).
              * Once this has been done, we "maximize" the sequences
              */
            if (staticInlining.isDefined && !ignoreAnnotations && m.body.isDefined && entry.fold(true)(entryName => !m.name.equals(entryName))) {
              m.copy(
                pres = replaceInhExhWithTrueSeq(m.pres),
                posts = replaceInhExhWithTrueSeq(m.posts)
              )(m.pos, m.info, m.errT)
            } else {
              m
            }
          case w: sil.While =>
            if(staticInlining.isDefined && !ignoreAnnotations) {
              w.copy(invs = replaceInhExhWithTrueSeq(w.invs))(w.pos, w.info, w.errT)
            } else {
              w
            }
        },
        Traverse.TopDown)

    val backendFuncs = new mutable.HashSet[sil.BackendFunc]()
    p.visit {
      case sf: sil.BackendFuncApp => backendFuncs.add(sf.backendFunc)
    }

    /* we replace the program already here even though we may replace it again later, since the annotation refers to the
     * program via the verifier
     */
    verifier.replaceProgram(progTriggersWithoutInhExhSpec)

    if (staticInlining.isDefined && !ignoreAnnotations) {
      verifier.replaceProgram(
        progTriggersWithoutInhExhSpec.transform(
          {
            case m: sil.Method =>
              if (m.body.isDefined) {
                if (entry.fold(true)(entryName => !m.name.equals(entryName)))
                  inliningModule.annotateMethod(m.copy(
                    body = Some(inliningModule.flattenStmt(m.body.get).asInstanceOf[sil.Seqn])
                  )(m.pos, m.info, m.errT))
                else m.copy(body = Some(inliningModule.flattenStmt(inliningModule.annotateStmt(m.body.get)).asInstanceOf[sil.Seqn]))(m.pos, m.info, m.errT)
              } else {
                m
              }
          },
          Traverse.TopDown)
      )
    }

    // We record the Boogie names of all Viper variables in this map.
    // The format is Viper member name -> (Viper variable name -> Boogie variable name).
    var nameMaps : Map[String, mutable.HashMap[String, String]] = null

    val output = verifier.program match {
      case sil.Program(domains, fields, functions, predicates, old_methods, extensions) =>
        // translate all members
        var methods = old_methods

        if (staticInlining.isDefined) {
          entry match {
            case None =>
              methods = Seq(methods.head)
              inliningModule.entryMethod = methods.head.name
            case Some(s) =>
              methods = Seq(program.findMethod(s))
              inliningModule.entryMethod = entry.toString
          }
          verboseCallstack match {
            case None =>
              inliningModule.verboseSet = Set()
            case Some("()") =>
              inliningModule.verboseSet = Set()
            case Some(s) =>
              var temp = s.substring(1, s.length-1)
              var sequence: Set[String] = Set()
              var str: String = ""
              for (char <- temp)
                if (!char.equals(',')) str += char
                else {sequence += str ; str = ""}
              if (!str.equals("")) sequence+=str
              for (i <- sequence) {
                println(i)
                if (i.startsWith("L@")) {
                  //case we get a method name
                  inliningModule.verboseSet += i.substring(2).toDouble.toInt
                } else {
                  //case that we get a line number of a loop
                  inliningModule.verboseSet += program.findMethod(i).pos.asInstanceOf[HasLineColumn].line
                  println(inliningModule.verboseSet.toString())
                }
              }
          }
        }

        // important to convert Seq to List to force the methods to be translated, otherwise it's possible that
        // evaluation happens lazily, which can lead to incorrect behaviour (evaluation order is important here)
        val translateFields =
          MaybeCommentedDecl("Translation of all fields", (fields flatMap translateField).toList)
        nameMaps = (methods ++ functions ++ predicates).map(_.name -> new mutable.HashMap[String, String]()).toMap
        val members = (domains flatMap translateDomainDecl) ++
          translateFields ++
          (functions flatMap (f => translateFunction(f, nameMaps.get(f.name)))) ++
          (predicates flatMap (p => translatePredicate(p, nameMaps.get(p.name)))) ++
          (methods flatMap (m => translateMethodDecl(m, nameMaps.get(m.name)))) ++
          (backendFuncs flatMap translateBackendFunc)

        // get the preambles (only at the end, even if we add it at the beginning)
        val preambles = verifier.allModules flatMap {
          m =>
            if (m.preamble.size > 0) Seq(CommentedDecl(s"Preamble of ${m.name}.", m.preamble))
            else Nil
        }

        // some header information for debugging
        val deps = verifier.dependencyDescs map ("  " + _)
        val header = Seq(
          "",
          s"Translation of Viper program.",
          "",
          "Date:         " + new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(new Date()),
          "Tool:         " + verifier.toolDesc) ++
          (verifier.getDebugInfo map (a => a._1 + ": " + (" " * (12 - a._1.size)) + a._2)) ++
          Seq("Dependencies:") ++
          deps ++
          Seq("")
        Program(header, preambles ++ members)
    }

    if (staticInlining.isDefined && printSC) {
      println("Number of blocks (syntactic, not): " + inliningModule.n_syntactic.toString + ", " + inliningModule.n_syntactic_not.toString)
    }

    (output.optimize.asInstanceOf[Program], nameMaps.map(e => e._1 -> e._2.toMap))
  }

  def translateMethodDecl(m: sil.Method, names: Option[mutable.Map[String, String]]): Seq[Decl] = {
    val mWithLoopInfo = loopModule.initializeMethod(m)

    env = Environment(verifier, mWithLoopInfo)
    ErrorMemberMapping.currentMember = mWithLoopInfo
        val res = mWithLoopInfo match {
          case method @ sil.Method(name, formalArgs, formalReturns, pres, posts, _) =>
            val initOldStateComment = "Initializing of old state"
            val ins: Seq[LocalVarDecl] = formalArgs map translateLocalVarDecl
            val outs: Seq[LocalVarDecl] = formalReturns map translateLocalVarDecl
            val init = MaybeCommentBlock("Initializing the state", stateModule.initBoogieState ++ assumeAllFunctionDefinitions ++ stmtModule.initStmt(method.bodyOrAssumeFalse))
            val initOld = MaybeCommentBlock("Initializing the old state", stateModule.initOldState)
            val paramAssumptions = mWithLoopInfo.formalArgs map (a => allAssumptionsAboutValue(a.typ, translateLocalVarDecl(a), true))
            val inhalePre = translateMethodDeclPre(pres)
            val checkPost: Stmt = if (posts.nonEmpty) {
              translateMethodDeclCheckPosts(posts)
            }
            else Nil
            val postsWithErrors = posts map (p => (p, errors.PostconditionViolated(p, mWithLoopInfo)))
            val exhalePost = MaybeCommentBlock("Exhaling postcondition", exhale(postsWithErrors))
            val body: Stmt = translateStmt(method.bodyOrAssumeFalse)
              /* TODO: Might be worth special-casing on methods with empty bodies */
            val proc = Procedure(Identifier(name), ins, outs,
              Seq(init,
                MaybeCommentBlock("Assumptions about method arguments", paramAssumptions),
                inhalePre,
                MaybeCommentBlock(initOldStateComment, initOld),
                checkPost, inliningModule.ignoreErrorsWhenBounded(body), inliningModule.ignoreErrorsWhenBounded(exhalePost)))
        CommentedDecl(s"Translation of method $name", proc)
    }

    if (names.isDefined){
      val usedNames = env.currentNameMapping
      // add all local vars
      names.get ++= usedNames
    }

    env = null
    ErrorMemberMapping.currentMember = null
    res
  }

  private def translateMethodDeclCheckPosts(posts: Seq[sil.Exp]): Stmt = {
    val (stmt, state) = stateModule.freshTempState("Post")

    val reset = stateModule.resetBoogieState


    // note that the order here matters - onlyExhalePosts should be computed with respect to the reset state
    val onlyExhalePosts: Seq[Stmt] = inhaleModule.inhaleExhaleSpecWithDefinednessCheck(
    posts, {
      errors.ContractNotWellformed(_)
    })

    val stmts = stmt ++ reset ++ (
    if (Expressions.contains[sil.InhaleExhaleExp](posts)) {
      // Postcondition contains InhaleExhale expression.
      // Need to check inhale and exhale parts separately.
      val onlyInhalePosts: Seq[Stmt] = inhaleModule.inhaleInhaleSpecWithDefinednessCheck(
      posts, {
        errors.ContractNotWellformed(_)
      })

          NondetIf(
          MaybeComment("Checked inhaling of postcondition to check definedness",
            MaybeCommentBlock("Do welldefinedness check of the inhale part.",
              NondetIf(onlyInhalePosts ++ Assume(FalseLit()))) ++
              MaybeCommentBlock("Normally inhale the exhale part.",
                onlyExhalePosts)
          ) ++
            MaybeComment("Stop execution", Assume(FalseLit()))
      )
    }
    else {
      NondetIf(
        MaybeComment("Checked inhaling of postcondition to check definedness", onlyExhalePosts) ++
          MaybeComment("Stop execution", Assume(FalseLit()))
      )
    })

    stateModule.replaceState(state)

    stmts
  }

  private def translateMethodDeclPre(pres: Seq[sil.Exp]): Stmt = {
    val res = if (Expressions.contains[sil.InhaleExhaleExp](pres)) {
      // Precondition contains InhaleExhale expression.
      // Need to check inhale and exhale parts separately.
      val onlyExhalePres: Seq[Stmt] = inhaleModule.inhaleExhaleSpecWithDefinednessCheck(
      pres, {
        errors.ContractNotWellformed(_)
      })
      val onlyInhalePres: Seq[Stmt] = inhaleModule.inhaleInhaleSpecWithDefinednessCheck(
      pres, {
        errors.ContractNotWellformed(_)
      })
      MaybeCommentBlock("Checked inhaling of precondition",
        MaybeCommentBlock("Do welldefinedness check of the exhale part.",
          NondetIf(onlyExhalePres ++ Assume(FalseLit()))) ++
          MaybeCommentBlock("Normally inhale the inhale part.",
            onlyInhalePres)
      )
    }
    else {
      val inhalePres: Seq[Stmt] = inhaleModule.inhaleInhaleSpecWithDefinednessCheck(
      pres, {
        errors.ContractNotWellformed(_)
      })
      MaybeCommentBlock("Checked inhaling of precondition", inhalePres)
    }

    res
  }

  override def allAssumptionsAboutValue(typ:sil.Type, arg: LocalVarDecl, isParameter:Boolean): Stmt = {
    val tmp = verifier.allModules map (_.validValue(typ, arg.l, isParameter))
    val assumptions = tmp.filter(_.isDefined).map(_.get)
    assumptions.allOption match {
      case None => Nil
      case Some(e) => Assume(e)
    }
  }

  def translateDomainDecl(d: sil.Domain): Seq[Decl] = {
    env = Environment(verifier, d)
    val res = translateDomain(d)
    env = null
    res
  }
}
