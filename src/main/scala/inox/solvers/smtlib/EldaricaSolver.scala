/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers._
import _root_.smtlib.trees.Commands.{CheckSat, Exit}

object OptEldaricaOptions extends SetOptionDef[String] {
  val name = "solver:eldarica"
  val default = Set[String]()
  val elementParser = stringParser
  val usageRhs = "<eldarica-opt>"
}

trait EldaricaSolver extends SMTLIBSolver with EldaricaTarget {
  import context.{given, _}
  import program.trees._
  import SolverResponses._

  def optEldaricaOptions: SetOptionDef[String] = OptEldaricaOptions

  def interpreterOpts = {
    Seq(
      "-log:0", // suppress logging
      "-scex",  // produce counterexamples (in SMTLIB format: ^s ++ _)
      "-ssol",  // produce models (in SMTLIB format: ^s ++ _)
      "-hsmt",  // accept input in Horn SMTLIB format
      "-in"     // read from STDIN
    ) ++ options.findOptionOrDefault(optEldaricaOptions)
  }

  override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]) = {
    for (cl <- assumptions) assertCnstr(cl)
    val res: SolverResponse[Model, Assumptions] = check(Model min config)

    config.cast(res match {
      case Unsat if config.withUnsatAssumptions =>
        UnsatWithAssumptions(Set.empty)
      case _ => res
    })
  }
}

