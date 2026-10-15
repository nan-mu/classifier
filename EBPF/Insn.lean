import ClassifierExpr.Expr

namespace EBPF
open ClassifierExpr

/-- Immediate and register operands retain the raw 32-bit immediate bits. -/
inductive Source where
  | imm (bits : UInt32)
  | reg (index : Nat)
  deriving BEq, Repr, Inhabited

inductive BinaryOp where
  | add | sub | mul | div | mod | sdiv | smod
  | and | or | xor | lsh | rsh | arsh
  deriving BEq, Repr, Inhabited

inductive EndianOp where
  | little | big | swap
  deriving BEq, Repr, Inhabited

/-- FETCH is optional only for arithmetic atomics. XCHG and CMPXCHG always
return the old memory value, to src and r0 respectively. -/
inductive AtomicOp where
  | add (fetch : Bool)
  | or (fetch : Bool)
  | and (fetch : Bool)
  | xor (fetch : Bool)
  | xchg
  | cmpxchg
  deriving BEq, Repr, Inhabited

def AtomicOp.returnsSource : AtomicOp → Bool
  | .add fetch | .or fetch | .and fetch | .xor fetch => fetch
  | .xchg => true
  | .cmpxchg => false

inductive JumpOp where
  | jeq | jne | jgt | jge | jlt | jle | jsgt | jsge | jslt | jsle | jset
  deriving BEq, Repr, Inhabited

inductive Insn where
  | mov (width : Width) (dst : Nat) (src : Source)
  | binary (width : Width) (op : BinaryOp) (dst : Nat) (src : Source)
  | neg (width : Width) (dst : Nat)
  | movsx (width : Width) (bits : Nat) (dst : Nat) (src : Nat)
  | endian (op : EndianOp) (bits : Nat) (dst : Nat)
  | exit
  | illegal (word : UInt64)
  | ldx (bytes : Nat) (dst : Nat) (base : Nat) (offset : Int)
  | stx (bytes : Nat) (base : Nat) (src : Nat) (offset : Int)
  | st (bytes : Nat) (base : Nat) (bits : UInt32) (offset : Int)
  | memsx (bytes : Nat) (dst : Nat) (base : Nat) (offset : Int)
  | loadAcq (bytes : Nat) (dst : Nat) (base : Nat) (offset : Int)
  | storeRel (bytes : Nat) (base : Nat) (src : Nat) (offset : Int)
  | atomic (width : Width) (op : AtomicOp) (base : Nat) (src : Nat) (offset : Int)
  | jcond (width : Width) (op : JumpOp) (dst : Nat) (src : Source) (offset : Int)
  | ja (offset : Int)
  | lddw (dst : Nat) (srcType : UInt8) (bits : UInt64)
  | continuation
  | callHelper (id : UInt32)
  deriving BEq, Repr, Inhabited

end EBPF
