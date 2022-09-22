//test: Test

import org.scalatest.FunSuite

class Test extends FunSuite  {

  import Uniquify.uniquifyProgram
  import RemoveComplexOperands.rcoProgram
  import ExplicateControl.explicateProgram
  import Select.selectProgram
  import Library._
  import Reader.read
  import Lvar._
  import Lint.{Plus, Minus, Read, Num, Prim, Expr}
  import Lvar.Parser._
  import Cvar._
  import scala.collection.mutable.ListBuffer
  import X86int._
  import X86var._
  import X86Interpreter._
  import Week3Lib._
  import Liveness._
  import Interference._
  import ColorGraph._
  import WGraph._

  case class EmptyInfo() extends Info

  def check(inp: String, spaceMax: Long) {
    check(inp, Nil, spaceMax)
  }

  def check(inp: String, reads: List[Long], spaceMax: Long) {
    // Parse program
    val p = parseLvar(read(inp))

    // Run reference program
    val output_reference = new ListBuffer[Long]
    val r_reference = Lvar.Interpreter.interpLvar(p, reads.to[ListBuffer], output_reference)

    // Build & run student program
    val p2 = buildProgram(afterProgram(selectProgram(explicateProgram(rcoProgram(uniquifyProgram(p))))))
    val p_student = assignProgram(p2)

    // Check if solution satisfies properties
    check_no_vars(p_student)
    check_stack(p_student, spaceMax: Long)

    val output_student = new ListBuffer[Long]
    val r_student = interpX86Custom(p_student, reads.to[ListBuffer], output_student)

    // Check if output is equal
    assert(r_student === r_reference, "Program output was not equal (expr output)")
    assert(output_student === output_reference, "Program output was not equal (print output)")
  }

  def interpX86Custom(p: X86int, inputs: ListBuffer[Long], outputs: ListBuffer[Long]): Long = p match {
    case X86int.X86IntProgram(ProgramRegisterInfo(stackSpace, _), blocks) => {
      import scala.collection.mutable.HashMap
      val interpreter = new InterpreterState(blocks, inputs, outputs, strict = true)
      interpreter.registers(RBP()) = Long.MaxValue - 7
      interpreter.registers(RSP()) = Long.MaxValue - 7 - stackSpace
      interpreter.runBlock(0, blocks.head._2)
      interpreter.registers(RAX())
    }
  }

  def check_no_vars(p: X86int): Unit = p match {
    case X86IntProgram(_, blocks) => {
      blocks.map(b => b._2).flatMap {
        case Blk(_, stmts) => stmts
      }.flatMap {
        case Instr(_, as) => as
        case _ => List()
      }.foreach {
        case XVar(_) => assert(false, "Program is not allowed to use variables")
        case _ => {}
      }
    }
  }

  def check_stack(p: X86int, spaceMax: Long): Unit = p match {
    case X86IntProgram(ProgramRegisterInfo(stackUsage, _), blocks) => {
      assert(stackUsage >= 0 && stackUsage <= spaceMax, "Stack usage is unreasonable.")
    }
  }

  // Add your tests below here
  test("Arith 1") {
    check("(+ 32 (- 10))", 0)
  }
}


