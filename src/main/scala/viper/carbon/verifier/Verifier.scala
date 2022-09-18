// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.verifier

import viper.silver.{ast => sil}
import viper.carbon.modules._
import viper.carbon.boogie.Namespace

/**
 * A verifier for Viper in Carbon (defines what modules need to be available).
 */
trait Verifier {

  // All modules
  // Note: we use vals to make it possible to import methods from other modules for
  // convenience.
  val mainModule: MainModule
  val heapModule: HeapModule
  val stateModule: StateModule
  val stmtModule: StmtModule
  val expModule: ExpModule
  val typeModule: TypeModule
  val exhaleModule: ExhaleModule
  val inliningModule: InliningModule
  val inhaleModule: InhaleModule
  val funcPredModule: FuncPredModule
  val permModule: PermModule
  val domainModule: DomainModule
  val seqModule: SeqModule
  val setModule: SetModule
  val mapModule: MapModule
  val wandModule: WandModule
  val loopModule: LoopModule

  /**
   * A list of all modules.
   */
  lazy val allModules: Seq[Module] = {
    Seq(mainModule, stateModule, heapModule, permModule, stmtModule, expModule, typeModule,
      exhaleModule, inhaleModule, funcPredModule, domainModule, seqModule, setModule,
      loopModule, mapModule, wandModule)
  } ensuring {
    mods => true
  }

  /**
   * Debug information (e.g., the full command used to invoke this verification).
   */
  def getDebugInfo: Seq[(String, Any)]

  /**
   * The tool (including version) used for this translation.
   */
  def toolDesc: String

  /**
   * A descriptive string for every dependency
   */
  def dependencyDescs: Seq[String]

  /**
   * Create a new namespace with a unique ID.
   */
  def freshNamespace(name: String): Namespace

  /**
   * The program currently being verified.
   */
  def program: sil.Program

  /**
   *  Replace the program with the provided one (for instance, to achieve whole-program transformations, including updating lookups of method definitions etc.)
   */
  def replaceProgram(prog : sil.Program): Unit

  def assumeInjectivityOnInhale: Boolean

  /**  Defines max depth of inlining methods or loops  */
  def staticInlining: Option[Int]

  /** Defines if some or all methods or loops in the inlining callstack should not be collapsed. */
  def verboseCallstack: Option[String]
  /** Defines max number of inlined loops or methods when inlining   */
  def maxInl: Option[Int]
  /** Check soundness conditions (mono and framing) for inlining */
  def noCheckSC: Boolean
  /** Print the code when checking soundness conditions (mono and framing)  */
  def printSC: Boolean
  // def simpleWFM: Boolean
  def closureSC: Boolean
  def modularSC: Boolean
  def pureFunctionsSC: Boolean
  def noSyntacticCheck: Boolean
  /** specifies a specific method to start from when inlining a program file */
  def entry: Option[String]
  def ignoreAnnotations: Boolean
}
