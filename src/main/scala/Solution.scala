object ColorGraph {

  import X86int._
  import X86var._
  import Week3Lib._
  import WGraph._
  import scala.collection.mutable.PriorityQueue

  val callerSaved: Set[W] = Set(Rg(RAX()), Rg(RCX()), Rg(RDX()), Rg(RSI()), Rg(RDI()), Rg(R8()), Rg(R9()), Rg(R10()), Rg(R11()))
  val calleeSaved: Set[W] = Set(Rg(RSP()), Rg(RBP()), Rg(RBX()), Rg(R12()), Rg(R13()), Rg(R14()), Rg(R15()))
  val ignoreRegs: Set[Arg] = Set(Reg(RAX()), Reg(RSP()), Reg(RBP()), Reg(R11()), Reg(R15()))

  def WToInt(w: W): Option[Int] = w match {
    case Rg(RCX()) => Some(0)
    case Rg(RDX()) => Some(1)
    case Rg(RSI()) => Some(2)
    case Rg(RDI()) => Some(3)
    case Rg(R8()) => Some(4)
    case Rg(R9()) => Some(5)
    case Rg(R10()) => Some(6)
    case Rg(RBX()) => Some(7)
    case Rg(R12()) => Some(8)
    case Rg(R13()) => Some(9)
    case Rg(R14()) => Some(10)
    case Rg(RAX()) => Some(-1)
    case Rg(RSP()) => Some(-2)
    case Rg(RBP()) => Some(-3)
    case Rg(R11()) => Some(-4)
    case Rg(R15()) => Some(-5)
    case _ => None
  }

  def IntToArg(i: Int): Arg = i match {
    case 0 => Reg(RCX())
    case 1 => Reg(RDX())
    case 2 => Reg(RSI())
    case 3 => Reg(RDI())
    case 4 => Reg(R8())
    case 5 => Reg(R9())
    case 6 => Reg(R10())
    case 7 => Reg(RBX())
    case 8 => Reg(R12())
    case 9 => Reg(R13())
    case 10 => Reg(R14())
    case -1 => Reg(RAX())
    case -2 => Reg(RSP())
    case -3 => Reg(RBP())
    case -4 => Reg(R11())
    case -5 => Reg(R15())
    case i if i > 10 => Deref(RBP(), -((i - 10) * 8))
  }

  def argToW(arg: X86int.Arg): W = arg match {
    case Reg(r) => Rg(r)
    case XVar(x) => Id(x)
    case _ => null
  }

  def assignBlock(b: Block, m: Map[W, Int]): (Block, Int, List[Register]) = b match {
    case Blk(info, instrs) =>
      var stackSpace: Int = 0
      var calleeRegs: List[Register] = List()

      val newInstrs = instrs.map {
        case Instr(c, args) => c match {
          case Addq() | Movq() | Subq() => {
            var a1 = args.head
            var a2 = args.last
            val w1 = argToW(a1)
            val w2 = argToW(a2)

            if (w1 != null) {
              if (!ignoreRegs.contains(a1)) {
                a1 = IntToArg(m(w1))
              }

              a1 match {
                case Deref(_, _) => stackSpace += 1
                case Reg(r) => {
                  if (calleeSaved.contains(Rg(r))) {
                    calleeRegs = calleeRegs :+ r
                  }
                }
              }
            }

            if (w2 != null) {
              if (!ignoreRegs.contains(a2)) {
                a2 = IntToArg(m(w2))
              }

              a2 match {
                case Deref(_, _) => stackSpace += 1
                case Reg(r) => {
                  if (calleeSaved.contains(Rg(r))) {
                    calleeRegs = calleeRegs :+ r
                  }
                }
              }
            }

            Instr(c, List(a1, a2))
          }
          case Negq() | Pushq() | Popq() => {
            var a = args.head
            val w = argToW(a)
            if (w != null) {
              if (!ignoreRegs.contains(a)) {
                a = IntToArg(m(w))
              }

              a match {
                case Deref(_, _) => stackSpace += 1
                case Reg(r) => {
                  if (calleeSaved.contains(Rg(r))) {
                    calleeRegs = calleeRegs :+ r
                  }
                }
              }
            }

            Instr(c, List(a))
          }
        }
        case default => default
      }

      (Blk(info, newInstrs), stackSpace, calleeRegs)
  }

  def assignProgram(p: X86var): X86int = p match {
    case X86var.X86VarProgram(ProgramInterferenceInfo(g), blocks) =>
      val colors = color(g)
      var stackSpace = 0
      var calleeRegs: Set[Register] = Set()

      val newBlocks = blocks.map(b => {
        val assign = assignBlock(b._2, colors)
        stackSpace += assign._2
        calleeRegs = calleeRegs ++ assign._3
        (b._1, assign._1)
      })

      X86int.X86IntProgram(
        ProgramRegisterInfo(
          stackSpace,
          calleeRegs.toList
        ),
        newBlocks
      )
  }


  def order(i: (W, Set[W])) = i._2.size

  def isColorUsed(i: Int, adj: Set[W], m: Map[W, Int]): Boolean = {
    var used = false

    adj.foreach(a => {
      if (m.contains(a) && m(a) == i) {
        used = true
      }
    })

    used
  }

  def color(g: G): Map[W, Int] = {

    val pq = PriorityQueue.empty[(W, Set[W])](Ordering.by(order))
    var mapping: Map[W, Int] = Map()

    nodes(g).foreach(node => {
      pq.enqueue((node, outNeighbors(g, node)))
    })

    while (pq.nonEmpty) {
      val v = pq.dequeue()
      var i = 0
      while (isColorUsed(i, v._2, mapping)) {
        i += 1
      }
      mapping += v._1 -> i
    }

    mapping
  }
}