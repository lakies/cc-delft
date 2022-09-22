object Uniquify {

  import Lint._
  import Lvar._
  import GenSym._

  def uniquifyProgram(p: Lvar): Lvar = p match {
    case Lvar.Program(body) => Lvar.Program(uniquifyExpr(body, Map()))
  }

  def uniquifyExpr(ex: Expr, env: Map[String, String]): Expr = ex match {
    case Let(x, e1, e2) => {
      val symbol = gensym(x)
      Let(symbol, uniquifyExpr(e1, env), uniquifyExpr(e2, env ++ Map(x -> symbol)))
    }

    case Var(x) => {
      if (!env.contains(x)) {
        throw new RuntimeException("Variable not defined")
      }

      Var(env(x))
    }

    case Prim(op, es) => Prim(op, es.map(e => uniquifyExpr(e, env)))

    case Num(i) => Num(i)
  }

}

object RemoveComplexOperands {

  import Lint.{Num, Expr, Prim, Minus, Plus, Read}
  import Lvar._
  import GenSym._

  def rcoProgram(p: Lvar): Lvar = p match {
    case Program(body) => Program(rcoExp(body))
  }

  def rcoAtom(ex: Expr) : (String, Map[String, Expr]) = ex match {
    case i: Prim => {
      val symbol = gensym("tmp")
      (symbol, Map(symbol -> rcoExp(i)))
    }
    case i: Let => {
      val symbol = gensym("tmp")
      (symbol, Map(symbol -> rcoExp(i)))
    }
    case _ => throw new IllegalStateException()
  }

  def rcoExp(ex: Expr): Expr = ex match {
    case Let(x, e1, e2) => Let(x, rcoExp(e1), rcoExp(e2))

    case i: Var => i

    case Prim(op, es) => {
      var atoms: Map[String, Expr] = Map()
      var varNames: List[String] = List()

      val newEs = es.map {
        case i: Prim => {
          val result = rcoAtom(i)
          val symbol = result._1
          atoms = atoms ++ result._2
          varNames = varNames ++ List(symbol)
          Var(symbol)
        }
        case i: Let => {
          val result = rcoAtom(i)
          val symbol = result._1
          atoms = atoms ++ result._2
          varNames = varNames ++ List(symbol)
          Var(symbol)
        }
        case default => default
      }

      var newEx: Expr  = Prim(op, newEs)

      varNames.foreach(symbol => {
        newEx = Let(symbol, atoms(symbol), newEx)
      })

      newEx
    }

    case i: Num => i
  }

}

object ExplicateControl {

  import Lint.{Num, Expr, Prim, Minus, Plus, Read}
  import Lvar._
  import Cvar._

  def explicateProgram(p: Lvar): Cvar = p match {
    case Lvar.Program(e) => CProgram(List(("start", explicateTail(e))))
  }

  def explicateTail(ex: Expr): Tail = ex match {
    case Let(x, e1, e2) => {
      explicateAssign(e1, x, explicateTail(e2))
    }

    case default => Return(default)
  }


  def explicateAssign(ex: Expr, x: String, t: Tail): Tail = ex match {
    case Let(x, e1, e2) => {
      explicateAssign(e1, x, explicateAssign(e2, x, t))
    }

    case default => Seq(Assign(x, default), t)
  }


}

object Select {

  import Lint.{Num, Expr, Prim, Minus, Plus, Read, PrimOp}
  import Lvar._
  import Cvar._
  import X86int._
  import X86var._

  def selectProgram(p: Cvar): X86var = p match {
    case CProgram(blocks) => X86var.X86VarProgram(new Info, blocks.map({
      case (x, t) => (x, Blk(new BlockInfo, selectTail(t))) }))
  }

  def selectTail(t: Tail): List[Instruction] = t match {
    case Return(e) =>
      selectAtm(Reg(RAX()) , e) ++ List(Retq())
    case Seq(s, t) =>
      val statementInst = selectStmt(s)
      val tailInstr = selectTail(t)
      statementInst ++ tailInstr
  }

  def selectStmt(s: Stmt): List[Instruction] = s match {
    case Assign(x, e) => selectAtm(XVar(x), e)
  }

  def esToArg(es: Expr): Arg = es match {
    case Num(i) => Imm(i)
    case Var(i) => XVar(i)
    case _ => throw new IllegalArgumentException()
  }

  def selectAtm(arg: Arg, e: Expr): List[Instruction] = e match {
    case Num(i) => List(Instr(Movq(), List(Imm(i), arg)))
    case Var(y) => List(Instr(Movq(), List(XVar(y), arg)))
    case Prim(op, es) => op match {
      case Plus() =>
        List(
          Instr(Movq(), List(esToArg(es.head), arg)),
          Instr(Addq(), List(esToArg(es(1)), arg)),
        )
      case Minus() => {
        if(es.length == 1) {
          List(
            Instr(Movq(), List(esToArg(es.head), arg)),
            Instr(Negq(), List(arg)),
          )
        } else {
          List(
            Instr(Movq(), List(esToArg(es.head), arg)),
            Instr(Subq(), List(esToArg(es(1)), arg)),
          )
        }
      }
      case Read() =>
        List(
          Callq("_read_int", 0),
          Instr(Movq(), List(Reg(RAX()), arg))
        )
      case Print() => {
        List(
          Instr(Movq(), List(esToArg(es.head), Reg(RDI()))),
          Callq("_print_int", 1),
          Instr(Movq(), List(esToArg(es.head), arg)),
        )
      }
    }

  }
}

object AssignHomes {

  import X86int._
  import X86var._

  def genProgInfo(blocks: List[(String, Block)]): ProgramInfo = {
    var stackSpace: Long = 0;
    var locals: Set[String] = Set()

    blocks.foreach(block => {
      block._2 match {
        case Blk(_, instrs) => instrs.foreach {
          case Instr(_, args) => args.foreach {
            case XVar(x) =>
              stackSpace += 8
              locals += x
            case default => default
          }
          case default => default
        }
      }
    })

    ProgramInfo(locals.toList, stackSpace)
  }

  def assignBlocks(block: Block, locals: List[String]): Block = {
    block match {
      case Blk(info, instrs) => Blk(info, instrs.map {
        case Instr(c, args) => Instr(c, args.map {
          case XVar(x) => Deref(RBP(), -(locals.indexOf(x) + 1) * 8)
          case default => default
        })
        case default => default
      })
    }
  }

  def assignProgram(p: X86var): X86int = p match {
    case X86var.X86VarProgram(_, blocks) => {
      val programInfo = genProgInfo(blocks)
      X86int.X86IntProgram(programInfo, blocks.map(block => (block._1, assignBlocks(block._2, programInfo.locals))))
    }

  }
}

object PatchInstructions {

  import X86int._

  def patchProgram(p: X86int): X86int = p match {
    case X86IntProgram(info, blocks) => X86IntProgram(info, blocks.map(block => (block._1, patchBlock(block._2))))
  }

  def patchBlock(block: Block): Block = {
    block match {
      case Blk(info, instrs) => Blk(info, patchInstrs(instrs))
    }
  }

  def patchInstrs(instrs: List[Instruction]): List[Instruction] = instrs match {
    case i :: it => patchInstr(i) ++ patchInstrs(it)
    case i :: Nil => patchInstr(i)
    case _ => List()
  }

  def patchInstr(instruction: Instruction): List[Instruction] = instruction match {
    case Instr(c, args) => {
      if (args.length == 2
        && args.head.isInstanceOf[Deref]
        && args(1).isInstanceOf[Deref]) {
        return List(
          Instr(Movq(), List(args.head, Reg(RAX()))),
          Instr(c, List(Reg(RAX()), args(1)))
        )
      }

      List(Instr(c, args))
    }
    case default => List(default)
  }
}

object Conclude {

  import X86int._

  def concludeProgram(p: X86int): X86int = p match {
    case X86IntProgram(info@ProgramInfo(_, stackSpace), ("start", Blk(inf, instrs)) :: Nil) =>
      X86IntProgram(info, List(genMain(stackSpace), genStart(inf, instrs), genEnd(stackSpace)))
  }

  def genMain(stackSpace: Long): (String, Block) = {
    ("main", Blk(new BlockInfo, List(
      Instr(Pushq(), List(Reg(RBP()))),
      Instr(Movq(), List(Reg(RSP()), Reg(RBP()))),
      Instr(Subq(), List(Imm(stackSpace + stackSpace % 16), Reg(RSP()))),
      Jmp("start")
    )))
  }

  def genStart(inf: BlockInfo, instrs: List[Instruction]): (String, Block) = {
    val tail = instrs.last
    var newInstrs = instrs.init

    if (!tail.isInstanceOf[Retq]) {
      newInstrs = newInstrs :+ tail
    }

    newInstrs = newInstrs :+ Jmp("conclusion")

    ("start", Blk(inf, newInstrs))
  }

  def genEnd(stackSpace: Long): (String, Block) = {
    ("conclusion", Blk(new BlockInfo, List(
      Instr(Addq(), List(Imm(stackSpace + stackSpace % 16), Reg(RSP()))),
      Instr(Popq(), List(Reg(RBP()))),
      Retq()
    )))
  }
}

import scala.collection.immutable.Set

object Liveness {

  import X86int._
  import X86var._
  import Week3Lib._

  val callerSaved: Set[W] = Set(Rg(RAX()),Rg(RCX()), Rg(RDX()), Rg(RSI()), Rg(RDI()), Rg(R8()), Rg(R9()), Rg(R10()), Rg(R11()))
  val calleeSaved: Set[W] = Set(Rg(RSP()), Rg(RBP()), Rg(RBX()), Rg(R12()), Rg(R13()), Rg(R14()), Rg(R15()))

  def afterBlock(b: Block, label: String, liveBlocks: Map[String, Set[W]], lb: Set[W]): (Block, Map[String, Set[W]]) = b match {
    case Blk(_, instrs) => {
      val info = blockInfo(instrs, label, liveBlocks, lb)
      (Blk(LiveBlockInfo(info._1), instrs), info._2)
    }
  }

  def argToW(arg: X86int.Arg): W = arg match {
    case Reg(r) => Rg(r)
    case XVar(x) => Id(x)
    case _ => null
  }

  def blockInfo(instrs: List[Instruction], label: String, liveBlocks: Map[String, Set[W]], lb: Set[W]): (List[Set[W]], Map[String, Set[W]]) = {
    val reversed = instrs.reverse
    var liveBefore: Set[W] = lb
    var info: List[Set[W]] = List(liveBefore)

    reversed.foreach {
      case Instr(c, args) => {
        c match {
          case Addq() | Subq() => {
            val a1 = argToW(args.head) // read only
            val a2 = argToW(args.last) // read and write
            liveBefore = liveBefore union Set(a1, a2)
          }
          case Pushq() => {
            val a = argToW(args.head) // read and write
            liveBefore = liveBefore union Set(a)
          }
          case Movq() => {
            val a1 = argToW(args.head) // read only
            val a2 = argToW(args.last) // write only
            liveBefore = liveBefore diff Set(a2)
            liveBefore = liveBefore union Set(a1)
          }
          case Popq() => {
            val a = argToW(args.head) // read and write
            liveBefore = liveBefore diff Set(a)
          }
          case Negq() => {
            // nothing happens
          }
        }

        info = info :+ (liveBefore diff Set(null))
      }
      case Jmp(l) => {
        liveBefore = liveBlocks(l)
        info = info :+ liveBefore
      }
      case Callq(_, _) => {
        liveBefore = liveBefore diff callerSaved
        info = info :+ liveBefore
      }
      case _ => info = info :+ liveBefore
    }

    val list = info.reverse.drop(1)
    (list, liveBlocks + (label -> list.head))
  }

  def afterProgram(p: X86var): X86var = p match {
    case X86var.X86VarProgram(inf, blocks) => {
      var liveBlocks: Map[String, Set[W]] = Map()
      var liveBefore: Set[W] = Set()

      var newBlocks: List[(String, Block)] = List()

      blocks.reverse.foreach(block => {
        val ab = afterBlock(block._2, block._1, liveBlocks, liveBefore)
        liveBlocks = ab._2
        newBlocks = newBlocks :+ (block._1, ab._1)
        liveBefore = liveBlocks(block._1)
      })


      X86var.X86VarProgram(inf, newBlocks.reverse)
    }
  }
}

object Interference {

  import X86int._
  import X86var._
  import WGraph._
  import Week3Lib._

  val callerSaved: Set[W] = Set(Rg(RAX()),Rg(RCX()), Rg(RDX()), Rg(RSI()), Rg(RDI()), Rg(R8()), Rg(R9()), Rg(R10()), Rg(R11()))
  val calleeSaved: Set[W] = Set(Rg(RSP()), Rg(RBP()), Rg(RBX()), Rg(R12()), Rg(R13()), Rg(R14()), Rg(R15()))

  def buildProgram(p: X86var): X86var = p match {
    case X86var.X86VarProgram(_, blocks) =>
      X86var.X86VarProgram(ProgramInterferenceInfo(buildGraph(blocks)), blocks)
  }

  def argToW(arg: X86int.Arg): W = arg match {
    case Reg(r) => Rg(r)
    case XVar(x) => Id(x)
    case _ => null
  }

  def buildGraph(bs: List[(String, Block)]): G = {

    var conflicts = empty

    bs.foreach(b => b._2 match {
      case Blk(info, instrs) =>
        val bi = info match {
          case i: LiveBlockInfo => i
        }

        instrs.zipWithIndex.foreach {
          case (Instr(c, args), i) =>
            val (w, s): (W, W) = c match {
              case Addq() | Subq() => {
                (argToW(args.last), null)
              }
              case Pushq() => {
                (null, null)
              }
              case Movq() => {
                (argToW(args.last), argToW(args.head))
              }
              case Popq() => {
                (argToW(args.last), null)
              }
              case Negq() => {
                (argToW(args.last), null)
              }
            }

            bi.after(i).foreach(aw => {
              if (aw != w && (s == null || aw != s))
                conflicts = addUndirectedEdge(conflicts, aw, w)
            })
          case (Callq(_, _), i) =>
            bi.after(i).foreach(aw => {
              callerSaved.foreach(cw => {
                if (aw != cw) {
                  conflicts = addUndirectedEdge(conflicts, aw, cw)
                }
              })
            })
          case _ => Nil
        }

      case _ => Nil
    })

    conflicts

  }
}