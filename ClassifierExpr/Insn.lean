import ClassifierExpr.Bits
import ClassifierExpr.Expr
import ClassifierExpr.Direction

namespace ClassifierExpr

/-! ## Raw instruction and history (`doc/NodeInference/路径.md`,
`doc/NodeInference/step.md#正常返回历史`) -/

/-- \(\mathrm{Insn}=\bigsqcup_w(\{w\}\times\mathbb B_w)\). -/
structure Insn where
  width : InsnWidth
  bits  : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def Insn.mk16 (b : Nat) : Insn := ⟨.w16, MNat 16 b⟩
def Insn.mk32 (b : Nat) : Insn := ⟨.w32, MNat 32 b⟩
def Insn.mk64 (b : Nat) : Insn := ⟨.w64, MNat 64 b⟩

inductive HelperKind where
  | lookup | update | delete | clock | printk | checksum | adjustTail
  | unsupported (id : Nat)
  deriving BEq, Repr, Inhabited

def HelperKind.id : HelperKind → Nat
  | .lookup => 1 | .update => 2 | .delete => 3 | .clock => 5
  | .printk => 6 | .checksum => 28 | .adjustTail => 65
  | .unsupported id => id

def helperKind (id : Nat) : HelperKind :=
  match id with
  | 1 => .lookup | 2 => .update | 3 => .delete | 5 => .clock
  | 6 => .printk | 28 => .checksum | 65 => .adjustTail
  | n => .unsupported n

def helperArity : HelperKind → Nat
  | .lookup | .delete | .adjustTail => 2
  | .update => 4
  | .printk | .checksum => 5
  | .clock | .unsupported _ => 0

/-- Selected conditional successor; separate from history's unconditional direction. -/
inductive BranchDirection where
  | taken | notTaken
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Frozen comparison terms. Same-width terms and relation ranges require validation. -/
structure Cond where
  lhs : Term
  rel : Rel
  rhs : Term
  deriving BEq, Repr, Inhabited

/-- Five observation classes (`doc/Predicate/谓词定义.md`).
Resource provenance, byte-valued symbolic keys and dynamic identities are semantic premises. -/
inductive Predicate where
  | helper (event : NodeId) (kind : HelperKind) (args : List Term)
  | branch (position : Nat) (dir : BranchDirection) (cond : Cond)
  | ret (term : Term)
  | mapWrite (event : NodeId) (map : Term) (key : List Term) (offset : Nat) (source : Term)
  | packetWrite (event : NodeId) (packet : Nat) (offset : Nat) (source : Term)
  deriving BEq, Repr, Inhabited

inductive Location where
  | pos (j : Nat)
  | exit
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Semantic state \(\sigma=(\mathcal E,\mathcal P)\). -/
structure SemState where
  exprs      : ExprSet
  predicates : List Predicate
  deriving Repr, Inhabited

def SemState.empty : SemState := ⟨ExprSet.empty, []⟩

/-- One step record (position, direction, successor position, ordered local results).
Position is the document's 1-based instruction position; validity is an external premise. -/
structure Record where
  position : Nat
  dir : Direction
  successor : Location
  increments : List SemState
  deriving Repr, Inhabited

/-- A history consists of its entry state and ordered step records.
Structural well-formedness is an external premise. -/
structure History where
  entry : SemState
  records : List Record
  deriving Repr, Inhabited

end ClassifierExpr
