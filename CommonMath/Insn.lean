import CommonMath.Bits
import CommonMath.Expr
import CommonMath.Direction

namespace CommonMath

/-! ## Raw instruction and history (`doc/common-math.md` §2) -/

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

/-- Comparisons fix their source terms; returns and helper calls are value/event observations. -/
inductive Predicate where
  | cmp (rel : Rel) (lhs : Term) (rhs : Term)
  | ret (value : Term)
  | helper (event : NodeId) (kind : HelperKind) (args : List Term)
  deriving BEq, Repr, Inhabited

/-- RV32 condition interpretation. Unknown source values remain unknown. -/
def Predicate.eval? : Predicate → Option Bool
  | .ret _ | .helper _ _ _ => none
  | .cmp rel lhs rhs => do
    let a ← eval (solve lhs)
    let b ← eval (solve rhs)
    pure (interpretRel 32 rel a b)

/-- \(\mathrm{Inst}_{\mathrm{next}}=\mathrm{Direction}\times\mathrm{NodeId}\) (§13.3). -/
structure InstNext where
  dir    : Direction
  target : NodeId
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One history item \((i,\mathcal P,\mathcal E,\mathcal N)\). -/
structure HistoryItem where
  insn       : Insn
  predicates : List Predicate
  exprs      : ExprSet
  nexts      : List InstNext
  deriving Repr, Inhabited

/-- Ordered execution history. -/
abbrev History := List HistoryItem

/-- Successful output \(\mathcal H\): a finite set of histories. -/
abbrev HistorySet := List History

def HistoryItem.withExprs (h : HistoryItem) (E : ExprSet) : HistoryItem :=
  { h with exprs := E }

def HistoryItem.overrideExprs (h : HistoryItem) (Ei : ExprSet) : HistoryItem :=
  { h with exprs := ExprSet.override h.exprs Ei }

end CommonMath
