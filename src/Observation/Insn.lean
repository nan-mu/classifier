import Term.Value.Bits
import Expression.Basic
import Interface.Step.Direction

namespace Observation
open Term Term.Value Expression Interface.Step

/-! ## Raw instruction and history (`doc/NodeInference/路径.md`,
`doc/NodeInference/step.md#正常返回历史`) -/

/-- \(\mathrm{Insn}=\bigsqcup_w(\{w\}\times\mathbb B_w)\). -/
structure Insn where
  width : InsnWidth
  bits  : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

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

/-- Registers the call must have materialized. `printk` is variadic: the format
pointer and its length are required, and later words are kept only when present. -/
def helperRequired : HelperKind → Nat
  | .printk => 2
  | k => helperArity k

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
inductive Observation where
  | helper (kind : HelperKind) (args : List Term)
  | branch (position : Nat) (dir : BranchDirection) (cond : Cond)
  | ret (term : Term)
  | mapWrite (map : Term) (key : List Term) (offset : Nat) (bits : Nat)
      (source : Term)
  | packetWrite (offset : Nat) (bits : Nat) (source : Term)
  deriving BEq, Repr, Inhabited

def Observation.savedMapKey? : Observation → Option (List Term)
  | .mapWrite _ key _ _ _ => some key
  | _ => none

theorem mapWrite_saved_key (map : Term) (key : List Term)
    (offset bits : Nat) (source : Term) :
    (Observation.mapWrite map key offset bits source).savedMapKey? = some key := rfl

inductive Location where
  | pos (j : Nat)
  | exit
  deriving DecidableEq, BEq, Repr, Inhabited

/-- State. Its mathematical notation is \(\sigma\).
Register equalities, including virtual intervals, live in `exprs`. -/
structure State where
  exprs      : List Expr
  predicates : List Observation
  deriving Repr, Inhabited

def State.empty : State := { exprs := Expr.nil, predicates := [] }

theorem savedMapKey_expr_update (p : Observation) (E _updates : List Expr) :
    (State.mk E [p]).predicates = [p] := rfl

/-- One step record (position, direction, successor position, ordered local results).
Position is the document's 1-based instruction position; validity is an external premise. -/
structure Record where
  position : Nat
  dir : Direction
  successor : Location
  increments : List State
  deriving Repr, Inhabited

/-- A history consists of its entry state and ordered step records.
Structural well-formedness is an external premise. -/
structure History where
  entry : State
  records : List Record
  deriving Repr, Inhabited

end Observation
