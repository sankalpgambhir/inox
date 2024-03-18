package inox.solvers.smtlib

import _root_.{smtlib => smtlib_}
import smtlib_.trees.Terms._
import smtlib_.trees.Commands._
import smtlib_.interpreters.ProcessInterpreter
import smtlib.theories.Core._
import scala.collection.mutable.TreeSet
import smtlib.theories.ArraysEx

/**
  * [[ProcessInterpreter]] specific to Eldarica to intercept unsupported
  * uninterpreted function declarations and calls and transform them into Array
  * declarations and selections respectively. 
  *
  * @param executable path to executable
  * @param args command-line arguments for solver executable
  * @param printer printer for SMTLIB expressions
  * @param parserCtor parser (cosntructor) for solver output
  */
class EldaricaInterpreter(executable: String,
                    args: Array[String],
                    override val printer: smtlib_.printer.Printer = smtlib_.printer.RecursivePrinter,
                    parserCtor: java.io.BufferedReader => smtlib_.parser.Parser = out => new smtlib_.parser.Parser(new smtlib_.lexer.Lexer(out)))
extends ProcessInterpreter(executable, args, printer, parserCtor) {
  /**
    * Set default response options to be used via the SMTLIB interface
    */
  def setInterfaceOptions(): Unit = 
    printer.printCommand(SetOption(PrintSuccess(true)), in)
    in.write("\n")
    in.flush()
    parser.parseGenResponse
    
  // on construction :::
  setInterfaceOptions()
}

object EldaricaInterpreter {
  def default = EldaricaInterpreter(defaultName, defaultArgs)

  val defaultName = "/home/sankalp/projects/inox/interfacica/inter"
  val defaultArgs = Array.empty[String]
}
