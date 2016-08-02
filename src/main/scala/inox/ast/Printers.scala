/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import utils._
import org.apache.commons.lang3.StringEscapeUtils
import scala.language.implicitConversions

trait Printers { self: Trees =>

  case class PrinterContext(
    current: Tree,
    parents: List[Tree],
    lvl: Int,
    printer: PrettyPrinter) {

    def parent = parents.headOption
  }

  case class PrinterOptions(
    baseIndent: Int = 0,
    printPositions: Boolean = false,
    printUniqueIds: Boolean = false,
    printTypes: Boolean = false,
    symbols: Option[Symbols] = None) {
      require(!printTypes || symbols.isDefined,
        "Can't print types without an available symbol table")
  }

  object PrinterOptions {
    def fromContext(ctx: InoxContext): PrinterOptions = ???
    def fromSymbols(s: Symbols, ctx: InoxContext): PrinterOptions = ???
  }

  trait Printable {
    def asString(implicit opts: PrinterOptions): String
  }

  /** This pretty-printer uses Unicode for some operators, to make sure we
    * distinguish PureScala from "real" Scala (and also because it's cute). */
  class PrettyPrinter(opts: PrinterOptions,
                      osym: Option[Symbols],
                      val sb: StringBuffer = new StringBuffer) {

    override def toString = sb.toString

    protected def optP(body: => Any)(implicit ctx: PrinterContext) = {
      if (requiresParentheses(ctx.current, ctx.parent)) {
        sb.append("(")
        body
        sb.append(")")
      } else {
        body
      }
    }
    
    private val dbquote = "\""

    def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = {

      if (requiresBraces(tree, ctx.parent) && !ctx.parent.contains(tree)) {
        p"""|{
            |  $tree
            |}"""
        return
      }

      if (opts.printTypes) {
        tree match {
          case t: Expr =>
            p"⟨"

          case _ =>
        }
      }
      tree match {
        case id: Identifier =>
          val name = if (opts.printUniqueIds) {
            id.uniqueName
          } else {
            id.toString
          }
          p"$name"

        case Variable(id, _) =>
          p"$id"
          
        case Let(vd, expr, SubString(v2: Variable, start, StringLength(v3: Variable))) if vd == v2 && v2 == v3 =>
          p"$expr.substring($start)"

        case Let(vd, expr, BigSubString(v2: Variable, start, StringLength(v3: Variable))) if vd == v2 && v2 == v3 =>
          p"$expr.bigSubstring($start)"

        case Let(b,d,e) =>
          p"""|val $b = $d
              |$e"""

        case Forall(args, e) =>
          p"\u2200${nary(args)}. $e"

        case e @ CaseClass(cct, args) =>
          p"$cct($args)"

        case And(exprs)           => optP { p"${nary(exprs, " && ")}" }
        case Or(exprs)            => optP { p"${nary(exprs, "| || ")}" } // Ugliness award! The first | is there to shield from stripMargin()
        case Not(Equals(l, r))    => optP { p"$l \u2260 $r" }
        case Implies(l,r)         => optP { p"$l ==> $r" }
        case UMinus(expr)         => p"-$expr"
        case Equals(l,r)          => optP { p"$l == $r" }
        
        
        case Int32ToString(expr)    => p"$expr.toString"
        case BooleanToString(expr)  => p"$expr.toString"
        case IntegerToString(expr)  => p"$expr.toString"
        case CharToString(expr)     => p"$expr.toString"
        case RealToString(expr)     => p"$expr.toString"
        case StringConcat(lhs, rhs) => optP { p"$lhs + $rhs" }
      
        case SubString(expr, start, end) => p"$expr.substring($start, $end)"
        case BigSubString(expr, start, end) => p"$expr.bigSubstring($start, $end)"
        case StringLength(expr)          => p"$expr.length"
        case StringBigLength(expr)       => p"$expr.bigLength"

        case IntLiteral(v)        => p"$v"
        case BVLiteral(bits, size) => p"x${(size to 1 by -1).map(i => if (bits(i)) "1" else "0")}"
        case IntegerLiteral(v) => p"$v"
        case FractionLiteral(n, d) =>
          if (d == 1) p"$n"
          else p"$n/$d"
        case CharLiteral(v)       => p"$v"
        case BooleanLiteral(v)    => p"$v"
        case UnitLiteral()        => p"()"
        case StringLiteral(v)     => 
          if(v.count(c => c == '\n') >= 1 && v.length >= 80 && v.indexOf("\"\"\"") == -1) {
            p"$dbquote$dbquote$dbquote$v$dbquote$dbquote$dbquote"
          } else {
            val escaped = StringEscapeUtils.escapeJava(v)
            p"$dbquote$escaped$dbquote"
          }
        case GenericValue(tp, id) => p"$tp#$id"
        case Tuple(exprs)         => p"($exprs)"
        case TupleSelect(t, i)    => p"$t._$i"
        case AsInstanceOf(e, ct)  => p"""$e.asInstanceOf[$ct]"""
        case IsInstanceOf(e, cct) => p"$e.isInstanceOf[$cct]"
        case CaseClassSelector(e, id)         => p"$e.$id"

        case FunctionInvocation(id, tps, args) =>
          p"${id}${nary(tps, ", ", "[", "]")}"
          if (args.nonEmpty) {
            p"($args)"
          }

        case Application(caller, args) =>
          p"$caller($args)"

        case Lambda(Seq(vd), FunctionInvocation(id, Seq(), Seq(arg))) if vd == arg =>
          p"${id}"

        case Lambda(args, body) =>
          optP { p"($args) => $body" }

        case Plus(l,r)                 => optP { p"$l + $r" }
        case Minus(l,r)                => optP { p"$l - $r" }
        case Times(l,r)                => optP { p"$l * $r" }
        case Division(l,r)             => optP { p"$l / $r" }
        case Remainder(l,r)            => optP { p"$l % $r" }
        case Modulo(l,r)               => optP { p"$l mod $r" }
        case LessThan(l,r)             => optP { p"$l < $r" }
        case GreaterThan(l,r)          => optP { p"$l > $r" }
        case LessEquals(l,r)           => optP { p"$l <= $r" }
        case GreaterEquals(l,r)        => optP { p"$l >= $r" }
        case BVXOr(l,r)                => optP { p"$l ^ $r" }
        case BVShiftLeft(l,r)          => optP { p"$l << $r" }
        case BVAShiftRight(l,r)        => optP { p"$l >> $r" }
        case BVLShiftRight(l,r)        => optP { p"$l >>> $r" }
        case fs @ FiniteSet(rs, _)     => p"{${rs.distinct}}"
        case fs @ FiniteBag(rs, _)     => p"{${rs.toMap.toSeq}}"
        case fm @ FiniteMap(rs, _, _)  => p"{${rs.toMap.toSeq}}"
        case Not(ElementOfSet(e,s))    => p"$e \u2209 $s"
        case ElementOfSet(e,s)         => p"$e \u2208 $s"
        case SubsetOf(l,r)             => p"$l \u2286 $r"
        case Not(SubsetOf(l,r))        => p"$l \u2288 $r"
        case SetAdd(s,e)               => p"$s \u222A {$e}"
        case SetUnion(l,r)             => p"$l \u222A $r"
        case BagUnion(l,r)             => p"$l \u222A $r"
        case SetDifference(l,r)        => p"$l \\ $r"
        case BagDifference(l,r)        => p"$l \\ $r"
        case SetIntersection(l,r)      => p"$l \u2229 $r"
        case BagIntersection(l,r)      => p"$l \u2229 $r"
        case SetCardinality(s)         => p"$s.size"
        case BagAdd(b,e)               => p"$b + $e"
        case MultiplicityInBag(e, b)   => p"$b($e)"
        case MapApply(m,k)             => p"$m($k)"

        case Not(expr) => p"\u00AC$expr"

        case vd @ ValDef(id, tpe) =>
          p"$id : ${tpe}"

        case (tfd: TypedFunDef)   => p"typed def ${tfd.id}[${tfd.tps}]"
        case TypeParameterDef(tp) => p"$tp"
        case TypeParameter(id)    => p"$id"


        case IfExpr(c, t, ie : IfExpr) =>
          optP {
            p"""|if ($c) {
                |  $t
                |} else $ie"""
          }

        case IfExpr(c, t, e) =>
          optP {
            p"""|if ($c) {
                |  $t
                |} else {
                |  $e
                |}"""
          }

        // Types
        case Untyped               => p"<untyped>"
        case UnitType              => p"Unit"
        case Int32Type             => p"Int"
        case IntegerType           => p"BigInt"
        case RealType              => p"Real"
        case CharType              => p"Char"
        case BooleanType           => p"Boolean"
        case StringType            => p"String"
        case SetType(bt)           => p"Set[$bt]"
        case BagType(bt)           => p"Bag[$bt]"
        case MapType(ft,tt)        => p"Map[$ft, $tt]"
        case TupleType(tpes)       => p"($tpes)"
        case FunctionType(fts, tt) => p"($fts) => $tt"
        case c: ClassType =>
          p"${c.id}${nary(c.tps, ", ", "[", "]")}"

        // Definitions
        case Symbols(classes, functions) =>
          p"""${nary(classes.map(_._2).toSeq, "\n\n")}"""
          p"\n\n"
          p"""${nary(functions.map(_._2).toSeq, "\n\n")}"""

        case acd: AbstractClassDef =>
          p"abstract class ${acd.id}${nary(acd.tparams, ", ", "[", "]")}"

        case ccd : CaseClassDef =>
          p"case class ${ccd.id}"
          p"${nary(ccd.tparams, ", ", "[", "]")}"
          p"(${ccd.fields})"

          ccd.parent.foreach { par =>
            // Remember child and parents tparams are simple bijection
            p" extends ${par}${nary(ccd.tparams, ", ", "[", "]")}"
          }

        case fd: FunDef =>
          for (an <- fd.annotations) {
            p"""|@$an
                |"""
          }

          p"def ${fd.id}${nary(fd.tparams, ", ", "[", "]")}"
          if (fd.params.nonEmpty) {
            p"(${fd.params}): "
          }

          p"${fd.returnType} = "

          fd.body match {
            case Some(body) => p"$body"
            case None => p"???"
          }

        case (tree: PrettyPrintable) => tree.printWith(ctx)

        case _ => sb.append("Tree? (" + tree.getClass + ")")
      }
      if (opts.printTypes) {
        tree match {
          case t: Expr=>
            p" : ${t.getType(opts.symbols.get)} ⟩"

          case _ =>
        }
      }
      if (opts.printPositions) {
        tree.getPos match {
          case op: OffsetPosition =>
            p"@($op)"
          case rp: RangePosition =>
            if (rp.lineFrom == rp.lineTo) {
              if (rp.colFrom == rp.colTo) {
                p"@(${rp.lineFrom}:${rp.colFrom})"
              } else {
                p"@(${rp.lineFrom}:${rp.colFrom}-${rp.colTo})"
              }
            } else {
              p"@(${rp.focusBegin}-${rp.focusEnd})"
            }
          case _ =>
            p"@(?)"
        }
      }
    }

    protected def isSimpleExpr(e: Expr): Boolean = e match {
      case _: Let => false
      case p: PrettyPrintable => p.isSimpleExpr
      case _ => true
    }

    protected def noBracesSub(e: Expr): Seq[Expr] = e match {
      case Let(_, _, bd) => Seq(bd)
      case IfExpr(_, t, e) => Seq(t, e) // if-else always has braces anyway
      case _ => Seq()
    }

    protected def requiresBraces(ex: Tree, within: Option[Tree]) = (ex, within) match {
      case (e: Expr, _) if isSimpleExpr(e) => false
      case (e: Expr, Some(within: Expr)) if noBracesSub(within) contains e => false
      case (e: Expr, Some(_)) => true
      case _ => false
    }

    protected def precedence(ex: Expr): Int = ex match {
      case (pa: PrettyPrintable) => pa.printPrecedence
      case (_: ElementOfSet) => 0
      case (_: Modulo) => 1
      case (_: Or) => 2
      case (_: And) => 3
      case (_: GreaterThan | _: GreaterEquals  | _: LessEquals | _: LessThan | _: Implies) => 4
      case (_: Equals | _: Not) => 5
      case (_: Plus | _: Minus | _: SetUnion| _: SetDifference) => 7
      case (_: Times | _: Division | _: Remainder) => 8
      case _ => 9
    }

    protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
      case (pa: PrettyPrintable, _) => pa.printRequiresParentheses(within)
      case (_, None) => false
      case (_, Some(
        _: Definition | _: Let | _: IfExpr | _ : CaseClass | _ : Lambda | _ : Tuple
      )) => false
      case (ex: StringConcat, Some(_: StringConcat)) => false
      case (_, Some(_: FunctionInvocation)) => false
      case (ie: IfExpr, _) => true
      case (e1: Expr, Some(e2: Expr)) if precedence(e1) > precedence(e2) => false
      case (_, _) => true
    }
  }

  implicit class PrintWrapper(val f: PrinterContext => Any) {
    def print(ctx: PrinterContext) = f(ctx)
  }

  implicit class PrintingHelper(val sc: StringContext) {

    def p(args: Any*)(implicit ctx: PrinterContext): Unit = {
      val printer = ctx.printer
      val sb      = printer.sb

      val strings     = sc.parts.iterator
      val expressions = args.iterator

      var extraInd = 0
      var firstElem = true

      while(strings.hasNext) {
        val currval = strings.next
        val s = if(currval != " || ") {
          currval.stripMargin
        } else currval

        // Compute indentation
        val start = s.lastIndexOf('\n')
        if(start >= 0 || firstElem) {
          var i = start+1
          while(i < s.length && s(i) == ' ') {
            i += 1
          }
          extraInd = (i-start-1)/2
        }

        firstElem = false

        // Make sure new lines are also indented
        sb.append(s.replaceAll("\n", "\n"+("  "*ctx.lvl)))

        val nctx = ctx.copy(lvl = ctx.lvl + extraInd)

        if (expressions.hasNext) {
          val e = expressions.next
          if(e == "||")
        	  println("Seen Expression: "+e)

          e match {
            case (t1, t2) =>
              nary(Seq(t1, t2), " -> ").print(nctx)

            case ts: Seq[Any] =>
              nary(ts).print(nctx)

            case t: Tree =>
              // Don't add same tree twice in parents
              val parents = if (nctx.parents.headOption contains nctx.current) {
                nctx.parents
              } else {
                nctx.current :: nctx.parents
              }
              val nctx2 = nctx.copy(parents = parents, current = t)
              printer.pp(t)(nctx2)

            case p: PrintWrapper =>
              p.print(nctx)

            case e =>
              sb.append(e.toString)
          }
        }
      }
    }
  }

  def nary(ls: Seq[Any], sep: String = ", ", init: String = "", closing: String = ""): PrintWrapper = {
    val (i, c) = if(ls.isEmpty) ("", "") else (init, closing)
    val strs = i +: List.fill(ls.size-1)(sep) :+ c

    implicit pctx: PrinterContext =>
      new StringContext(strs: _*).p(ls: _*)
  }

  def typed(t: Tree with Typed)(implicit s: Symbols): PrintWrapper = {
    implicit pctx: PrinterContext =>
      p"$t : ${t.getType}"
  }

  def typed(ts: Seq[Tree with Typed])(implicit s: Symbols): PrintWrapper = {
    nary(ts.map(typed))
  }

  trait PrettyPrintable {
    self: Tree =>

    def printWith(implicit pctx: PrinterContext): Unit

    def printPrecedence: Int = 1000
    def printRequiresParentheses(within: Option[Tree]): Boolean = false
    def isSimpleExpr: Boolean = false
  }

  class EquivalencePrettyPrinter(opts: PrinterOptions, osym: Option[Symbols]) extends PrettyPrinter(opts, osym) {
    override def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = {
      tree match {
        case id: Identifier =>
          p"${id.name}"

        case _ =>
          super.pp(tree)
      }
    }
  }

  abstract class PrettyPrinterFactory {
    def create(opts: PrinterOptions, osym: Option[Symbols]): PrettyPrinter

    def apply(tree: Tree, opts: PrinterOptions = PrinterOptions(), osym: Option[Symbols] = None): String = {
      val printer = create(opts, osym)
      val ctx = PrinterContext(tree, Nil, opts.baseIndent, printer)
      printer.pp(tree)(ctx)
      printer.toString
    }

    def apply(tree: Tree, ctx: InoxContext): String = {
      val opts = PrinterOptions.fromContext(ctx)
      apply(tree, opts, None)
    }

    def apply(tree: Tree, ctx: InoxContext, sym: Symbols): String = {
      val opts = PrinterOptions.fromContext(ctx)
      apply(tree, opts, Some(sym))
    }
  }

  object PrettyPrinter extends PrettyPrinterFactory {
    def create(opts: PrinterOptions, osym: Option[Symbols]) = new PrettyPrinter(opts, osym)
  }

  object EquivalencePrettyPrinter extends PrettyPrinterFactory {
    def create(opts: PrinterOptions, osym: Option[Symbols]) = new EquivalencePrettyPrinter(opts, osym)
  }
}
