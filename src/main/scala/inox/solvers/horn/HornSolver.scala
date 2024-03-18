package inox.solvers.horn

import inox._
import inox.utils._
import inox.evaluators._

import inox.ast._
import inox.solvers.theories._
import inox.solvers.combinators._
import inox.solvers._
import inox.solvers.unrolling.ChooseEncoder
import inox.solvers.SolverResponses.CheckConfiguration
import inox.solvers.SolverResponses.Configuration
import scala.collection.mutable.ListBuffer
import inox.solvers.unrolling.Templates
import inox.solvers.unrolling.AbstractUnrollingSolver

/**
  * An Inox solver wrapping an SMTLIB solver support Horn solving for invariant
  * inference.
  *
  * @param program
  * @param context
  * @param prog
  * @param enc
  * @param chooses
  * @param programEncoder
  * @param semantics
  * @param targetSemantics
  */
private abstract class AbstractHornSolver 
  (override val program: Program,
   override val context: Context)
  // Alias for `program`, as there are some places where `program` is shadowed.
  (val prog: program.type)
  (val enc: transformers.ProgramTransformer {val sourceProgram: program.type})
  (val chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type})
  (val programEncoder: transformers.ProgramTransformer {
    val sourceProgram: program.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  })
  (using val semantics: program.Semantics,
   val targetSemantics: programEncoder.targetProgram.Semantics)
  extends AbstractUnrollingSolver(program, context, enc, chooses, programEncoder) { self =>

    protected final val s: programEncoder.sourceProgram.trees.type = programEncoder.sourceProgram.trees
    protected final val t: programEncoder.targetProgram.trees.type = programEncoder.targetProgram.trees
    protected final val targetProgram: programEncoder.targetProgram.type = programEncoder.targetProgram

    import program._
    import program.trees._
    import program.symbols.{given, _}

    type Encoded = t.Expr
    protected val underlying: AbstractSolver {
      val program: targetProgram.type
      type Trees = t.Expr
      type Model = targetProgram.Model
    } = ???

    def name: String = s"horn-${underlying.name}"

    // context options

    lazy val checkModels = context.options.findOptionOrDefault(optCheckModels)
    lazy val silentErrors = context.options.findOptionOrDefault(optSilentErrors)

    // solver state and actions

    protected val freeVars  = new IncrementalMap[Variable, Encoded]()
    private val constraints = new IncrementalSeq[Expr]()
    private val freeChooses = new IncrementalMap[Choose, Encoded]()

    protected var failures: ListBuffer[Throwable] = new ListBuffer
    protected var abort: Boolean = false
    protected var pause: Boolean = false

    def free(): Unit = 
      ???
    def push(): Unit = 
      ???
    def pop(): Unit = 
      ???
    def reset(): Unit = 
      ???

    def interrupt(): Unit = 
      ???

    override val templates = new TemplatesImpl(targetProgram, context)

    private class TemplatesImpl(override val program: targetProgram.type, override val context: Context)
                              (using override val semantics: targetProgram.Semantics)
      extends Templates {
      import program._
      import program.trees._
      import program.symbols.{given, _}

      type Encoded = Expr

      def asString(expr: Expr): String = expr.asString
      def abort: Boolean = self.abort
      def pause: Boolean = self.pause

      def encodeSymbol(v: Variable): Expr = v.freshen
      def mkEncoder(bindings: Map[Variable, Expr])(e: Expr): Expr = exprOps.replaceFromSymbols(bindings, e)
      def mkSubstituter(substMap: Map[Expr, Expr]): Expr => Expr = (e: Expr) => exprOps.replace(substMap, e)

      def mkNot(e: Expr) = not(e)
      def mkOr(es: Expr*) = orJoin(es)
      def mkAnd(es: Expr*) = andJoin(es)
      def mkEquals(l: Expr, r: Expr) = Equals(l, r)
      def mkImplies(l: Expr, r: Expr) = implies(l, r)

      def extractNot(e: Expr) = e match {
        case Not(e2) => Some(e2)
        case _ => None
      }

      def decodePartial(e: Expr, tpe: Type): Option[Expr] = Some(e)
    }

    protected final def encode(vd: ValDef): t.ValDef = programEncoder.encode(vd)
    protected final def decode(vd: t.ValDef): ValDef = programEncoder.decode(vd)

    protected final def encode(v: Variable): t.Variable = programEncoder.encode(v)
    protected final def decode(v: t.Variable): Variable = programEncoder.decode(v)

    protected final def encode(e: Expr): t.Expr = programEncoder.encode(e)
    protected final def decode(e: t.Expr): Expr = programEncoder.decode(e)

    protected final def encode(tpe: Type): t.Type = programEncoder.encode(tpe)
    protected final def decode(tpe: t.Type): Type = programEncoder.decode(tpe)

    protected def declareVariable(v: t.Variable): Encoded

    def declare(vd: program.trees.ValDef): Unit = context.timers.solvers.declare.run(try {
      context.timers.solvers.declare.sanity.run {
        assert(vd.getType.isTyped)
      }

      // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
      context.interruptManager.registerForInterrupts(this)

      val freeBindings: Map[Variable, Encoded] = (typeOps.variablesOf(vd.tpe) + vd.toVariable).map {
        v => v -> freeVars.cached(v)(declareVariable(encode(v)))
      }.toMap

      val newClauses = context.timers.solvers.declare.clauses.run {
        templates.instantiateVariable(encode(vd.toVariable), freeBindings.map(p => encode(p._1) -> p._2))
      }

      context.timers.solvers.declare.underlying.run {
        for (cl <- newClauses) {
          underlying.assertCnstr(cl)
        }
      }
    } catch {
      case e @ (_: InternalSolverError | _: Unsupported) => failures += e
    })

    def assertCnstr(expression: Trees): Unit = 
      ???

    def check(config: CheckConfiguration): config.Response[Model, Assumptions] = 
      ???
    
    def checkAssumptions(config: Configuration)(assumptions: Set[Trees]): config.Response[Model, Assumptions] = 
      ???

  }

  // class HornSolver extends AbstractHornSolver
