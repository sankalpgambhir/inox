/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.{smtlib => smtlib_}
import smtlib_.trees.Terms.{Identifier => SMTIdentifier, _}
import smtlib_.trees.Commands._
import smtlib_.theories._
import smtlib_.theories.cvc._
import smtlib_.interpreters.ProcessInterpreter
import java.io.BufferedWriter
import smtlib_.Interpreter
import scala.collection.mutable.TreeSet

trait EldaricaTarget extends SMTLIBTarget with SMTLIBDebugger {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  // def targetName: String = "eldarica"
  def targetName: String = EldaricaInterpreter.defaultName

  override protected val interpreter: Interpreter = {
    // val opts = interpreterOpts
    val opts = Array.empty[String]
    reporter.debug("Invoking solver with " + opts.mkString(" "))
    new EldaricaInterpreter(targetName, opts.toArray)
  }

  val cvcSets: Sets = CVC5Sets
  import cvcSets._

  override protected def computeSort(t: Type): Sort = t match {
    case SetType(base) => SetSort(declareSort(base))
    case _ => super.computeSort(t)
  }

  override protected def fromSMT(t: Term, otpe: Option[Type] = None)(using Context): Expr = {
    (t, otpe) match {
      // EK: This hack is necessary for sygus which does not strictly follow smt-lib for negative literals
      case (SimpleSymbol(SSymbol(v)), Some(IntegerType())) if v.startsWith("-") =>
        try {
          IntegerLiteral(v.toInt)
        } catch {
          case _: Throwable => super.fromSMT(t, otpe)
        }

      // XXX @nv: CVC4 seems to return some weird representations for certain adt selectors
      case (FunctionApplication(SimpleSymbol(s), Seq(e)), _)
      if s.name.endsWith("'") && selectors.containsB(SSymbol(s.name.init)) =>
        fromSMT(FunctionApplication(SimpleSymbol(SSymbol(s.name.init)), Seq(e)), otpe)

      // XXX @nv: CVC4 seems to return some weird representations for certain adt constructors
      case (FunctionApplication(SimpleSymbol(s), args), _)
      if s.name.endsWith("'") && constructors.containsB(SSymbol(s.name.init)) =>
        fromSMT(FunctionApplication(SimpleSymbol(SSymbol(s.name.init)), args), otpe)

      // XXX @nv: CVC4 seems to return bv literals instead of booleans sometimes
      case (FixedSizeBitVectors.BitVectorLit(bs), Some(BooleanType())) if bs.size == 1 =>
        BooleanLiteral(bs.head)
      case (FixedSizeBitVectors.BitVectorConstant(n, size), Some(BooleanType())) if size == 1 =>
        BooleanLiteral(n == 1)
      case (Core.Equals(e1, e2), _) =>
        fromSMTUnifyType(e1, e2, None)(Equals.apply) match {
          case Equals(IsTyped(lhs, BooleanType()), IsTyped(_, BVType(true, 1))) =>
            Equals(lhs, fromSMT(e2, BooleanType()))
          case Equals(IsTyped(_, BVType(true, 1)), IsTyped(rhs, BooleanType())) =>
            Equals(fromSMT(e1, BooleanType()), rhs)
          case expr => expr
        }
      case (EmptySet(sort), Some(SetType(base))) => FiniteSet(Seq.empty, base)
      case (EmptySet(sort), _) => FiniteSet(Seq.empty, fromSMT(sort))

      case (Singleton(e), Some(SetType(base))) => FiniteSet(Seq(fromSMT(e, base)), base)
      case (Singleton(e), _) =>
        val elem = fromSMT(e)
        FiniteSet(Seq(elem), elem.getType)

      case (Insert(set, es@_*), Some(SetType(base))) => es.foldLeft(fromSMT(set, SetType(base))) {
        case (FiniteSet(elems, base), e) =>
          val elem = fromSMT(e, base)
          FiniteSet(elems.filter(_ != elem) :+ elem, base)
        case (s, e) => SetAdd(s, fromSMT(e, base))
      }

      case (Insert(set, es@_*), _) => es.foldLeft(fromSMT(set)) {
        case (FiniteSet(elems, base), e) =>
          val elem = fromSMT(e, base)
          FiniteSet(elems.filter(_ != elem) :+ elem, base)
        case (s, e) => SetAdd(s, fromSMT(e))
      }

      case (Union(e1, e2), Some(SetType(base))) =>
        (fromSMT(e1, SetType(base)), fromSMT(e2, SetType(base))) match {
          case (FiniteSet(elems1, _), FiniteSet(elems2, _)) => FiniteSet(elems1 ++ elems2, base)
          case (s1, s2) => SetUnion(s1, s2)
        }

      case (Union(e1, e2), _) =>
        (fromSMT(e1), fromSMT(e2)) match {
          case (fs1@FiniteSet(elems1, b1), fs2@FiniteSet(elems2, b2)) =>
            val tpe = leastUpperBound(b1, b2)
            if (tpe == Untyped) unsupported(SetUnion(fs1, fs2), "woot? incompatible set base-types")
            FiniteSet(elems1 ++ elems2, tpe)
          case (s1, s2) => SetUnion(s1, s2)
        }

      case (ArraysEx.Store(e1, e2, e3), Some(MapType(from, to))) =>
        (fromSMT(e1, MapType(from, to)), fromSMT(e2, from), fromSMT(e3, to)) match {
          case (FiniteMap(elems, default, _, _), key, value) => FiniteMap(elems :+ (key -> value), default, from, to)
          case _ => super.fromSMT(t, otpe)
        }

      case (ArraysEx.Store(e1, e2, e3), _) =>
        (fromSMT(e1), fromSMT(e2), fromSMT(e3)) match {
          case (FiniteMap(elems, default, from, to), key, value) => FiniteMap(elems :+ (key -> value), default, from, to)
          case _ => super.fromSMT(t, otpe)
        }

      case (FunctionApplication(SimpleSymbol(SSymbol("__array_store_all__")), Seq(_, elem)), Some(MapType(k, v))) =>
        FiniteMap(Seq(), fromSMT(elem, v), k, v)

      case _ => super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]) = e match {
    case fs@FiniteSet(elems, _) =>
      if (elems.isEmpty) {
        EmptySet(declareSort(fs.getType))
      } else {
        val selems = elems.map(toSMT)

        if (exprOps.variablesOf(elems.head).isEmpty) {
          val sgt = Singleton(selems.head)

          if (selems.size > 1) {
            Insert(selems.tail :+ sgt)
          } else {
            sgt
          }
        } else {
          val sgt = EmptySet(declareSort(fs.getType))
          Insert(selems :+ sgt)
        }
      }
    case SubsetOf(ss, s) => Subset(toSMT(ss), toSMT(s))
    case ElementOfSet(e, s) => Member(toSMT(e), toSMT(s))
    case SetDifference(a, b) => Setminus(toSMT(a), toSMT(b))
    case SetUnion(a, b) => Union(toSMT(a), toSMT(b))
    case SetAdd(a, b) => Insert(toSMT(b), toSMT(a))
    case SetIntersection(a, b) => Intersection(toSMT(a), toSMT(b))

    case FiniteMap(_, default, _, _) if !isValue(default) || exprOps.exists {
      case _: Lambda => true
      case _ => false
    } (default) =>
      unsupported(e, "Cannot encode map with non-constant default value")

    case _ =>
      super.toSMT(e)
  }

  // query transformation
  // uninterpreted function elimination

  import smtlib_.trees.Terms.*

  private val uninterpretedSymbols: TreeSet[String] = TreeSet.empty

  def addTransformedSymbol(s: SSymbol): Unit =
    uninterpretedSymbols += s.name

  def isUninterpreted(s: SSymbol): Boolean =
    uninterpretedSymbols.contains(s.name)

  def clearUninterpretedSymbols(): Unit =
    uninterpretedSymbols.clear()

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
      decl.returnSort != Core.BoolSort() // is not a predicate
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
      case smtlib_.trees.Terms.Let(binding, bindings, term) => smtlib_.trees.Terms.Let(binding, bindings, transformTerm(term))
      case smtlib_.trees.Terms.Forall(sortedVar, sortedVars, term) => smtlib_.trees.Terms.Forall(sortedVar, sortedVars, transformTerm(term))
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

  override def emit(cmd: SExpr, rawOut: Boolean): SExpr = 
    val transformed = transformSExpr(cmd)
    super.emit(transformed, rawOut)

  override def free(): Unit = 
    clearUninterpretedSymbols()
    super.free()

  override def interrupt(): Unit = 
    clearUninterpretedSymbols()
    super.interrupt()
}
