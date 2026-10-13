import ClassifierExpr.Expr

namespace EBPF
open ClassifierExpr

/-- The executable slice uses ALU32/ALU64 MOV and ADD, plus outer EXIT. -/
inductive Source where
  | imm (bits : UInt32)
  | reg (index : Nat)
  deriving BEq, Repr, Inhabited

inductive Insn where
  | mov (width : Width) (dst : Nat) (src : Source)
  | add (width : Width) (dst : Nat) (src : Source)
  | exit
  | illegal (word : UInt64)
  deriving BEq, Repr, Inhabited

end EBPF
