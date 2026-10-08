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

/-- Predicate placeholder. Concrete elements TBD. -/
structure Predicate where
  tag : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

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
