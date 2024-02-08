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
                    printer: smtlib_.printer.Printer = smtlib_.printer.RecursivePrinter,
                    parserCtor: java.io.BufferedReader => smtlib_.parser.Parser = out => new smtlib_.parser.Parser(new smtlib_.lexer.Lexer(out)))
extends ProcessInterpreter(executable, args, printer, parserCtor) {

  private val uninterpretedSymbols: TreeSet[String] = TreeSet.empty

  def addTransformedSymbol(s: SSymbol): Unit =
    uninterpretedSymbols += s.name

  def isUninterpreted(s: SSymbol): Boolean =
    uninterpretedSymbols.contains(s.name)

  def clearUninterpretedSymbols(): Unit =
    uninterpretedSymbols.clear()

  /**
    * Set default response options to be used via the SMTLIB interface
    */
  def setInterfaceOptions(): Unit = 
    printer.printCommand(SetOption(PrintSuccess(true)), in)
    in.write("\n")
    in.flush()
    parser.parseGenResponse

  /**
    * Transform a function declaration to erase uninterpreted functions. If the
    * function is a predicate or a constant, returns the definition as is, else,
    * creates a new constant array definition from it.
    * 
    * For a function declaration:
    * 
    * `(declare-fun f (s1 s2 ... sn) sOut)` -> `(declare-const f (Array s1 (... (Array sn sOut))))`
    */
  def transformFunctionDeclaration(decl: DeclareFun): DeclareFun | DeclareConst = 
    def toTransform: Boolean =
      decl.returnSort != BoolSort() // is not a predicate
      && decl.paramSorts.length > 0 // is not a constant

    def doTransform: DeclareConst =
      val sort = decl.paramSorts.foldRight(decl.returnSort)((nextInp, inner) => ArraysEx.ArraySort(nextInp, inner))
      DeclareConst(decl.name, sort)

    def registerSymbol(): Unit =
      addTransformedSymbol(decl.name)
    
    if toTransform then 
      registerSymbol()
      doTransform 
    else 
      decl

  /**
    * For any uninterpreted definitions we have captured and transformed to
    * arrays, transform function calls to array selections.
    * 
    * For an application:
    * 
    * `f(x1, x2, ..., xn)` -> `(select (... (select f x1) ...) xn)`
    *
    * @param app function application term
    * @return transformed SExpr or original if unneeded
    */
  def transformCall(app: FunctionApplication): Term = 
    def toTransform: Boolean =
      isUninterpreted(app.fun.id.symbol) // have we seen this as an uninterpreted def?

    def doTransform: Term = 
      // f(x1, x2, ..., xn) -> (select (... (select f x1) ...) xn)
      val args = app.terms.map(transformTerm)
      if toTransform then
        args.foldLeft(app.fun: Term)((inner, nextArg) => ArraysEx.Select(inner, nextArg))
      else
        FunctionApplication(app.fun, args)

    doTransform

  /**
    * Transform a term changing calls to transformed uninterpreted functions
    * into array selections.
    * 
    * Assumes that function symbol names cannot be used in quantifiers. 
    */
  def transformTerm(term: Term): Term = 
    term match
      case Let(binding, bindings, term) => Let(binding, bindings, transformTerm(term))
      case Forall(sortedVar, sortedVars, term) => Forall(sortedVar, sortedVars, transformTerm(term))
      case Exists(sortedVar, sortedVars, term) => Exists(sortedVar, sortedVars, transformTerm(term))
      case QualifiedIdentifier(_, _) => term
      case AnnotatedTerm(term, attribute, attributes) => AnnotatedTerm(transformTerm(term), attribute, attributes)
      case app @ FunctionApplication(_, _) => transformCall(app)
      case _ => term
    

  /**
    * Transform a top-level command to erase uninterpreted functions. See
    * [[transformFunctionDeclaration]] or [[transformCall]] for details.
    */
  def transformCommand(expr: Command): Command =
    expr match
      case Assert(term) => Assert(transformTerm(term))
      case decl @ DeclareFun(_, _, _) => transformFunctionDeclaration(decl)
      case GetValue(term, terms) => GetValue(transformTerm(term), terms.map(transformTerm))
      case _ => expr
    
  /**
    * Transform a top-level SExpr if it is a command. See [[transformCommand]].
    */
  def transformSExpr(expr: SExpr): SExpr =
    expr match
      case cmd: Command => transformCommand(cmd)
      case _ => expr

  override def eval(cmd: SExpr): SExpr = 
    val transformed = transformSExpr(cmd)
    // println(s"[sent] $transformed")
    super.eval(transformed)

  override def free(): Unit = 
    clearUninterpretedSymbols()
    super.free()
  
  override def kill(): Unit = 
    clearUninterpretedSymbols()
    super.kill()

  override def interrupt(): Unit = 
    kill()
    
  // on construction :::
  setInterfaceOptions()
}

object EldaricaInterpreter {
  def default = EldaricaInterpreter(defaultName, defaultArgs)

  val defaultName = "/home/sankalp/projects/inox/interfacica/inter"
  val defaultArgs = Array.empty[String]
}
