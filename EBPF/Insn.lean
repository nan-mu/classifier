import ClassifierExpr.Expr

namespace EBPF
open ClassifierExpr

/-- Immediate and register operands retain the raw 32-bit immediate bits. -/
inductive Source where
  | imm (bits : UInt32)
  | reg (index : Nat)
  deriving BEq, Repr, Inhabited

inductive JumpOp where
  | jeq | jne | jgt
  deriving BEq, Repr, Inhabited

inductive Insn where
  | mov (width : Width) (dst : Nat) (src : Source)
  | add (width : Width) (dst : Nat) (src : Source)
  | exit
  | illegal (word : UInt64)
  | ldx (bytes : Nat) (dst : Nat) (base : Nat) (offset : Int)
  | stx (bytes : Nat) (base : Nat) (src : Nat) (offset : Int)
  | jcond (width : Width) (op : JumpOp) (dst : Nat) (src : Source) (offset : Int)
  | ja (offset : Int)
  | lddw (dst : Nat) (srcType : UInt8) (bits : UInt64)
  | continuation
  | callHelper (id : UInt32)
  deriving BEq, Repr, Inhabited

end EBPF
