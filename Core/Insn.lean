import Core.Bits
import Core.Expr
import Core.Direction
import Core.BitMem

namespace Core

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
inductive Predicate where
  | helper (event : NodeId) (kind : HelperKind) (args : List Term)
  | branch (position : Nat) (dir : BranchDirection) (cond : Cond)
  | ret (term : Term)
  | mapWrite (event : NodeId) (map : Term) (key : List Term) (offset : Nat) (bits : Nat)
      (source : Term)
  | packetWrite (event : NodeId) (packet : Nat) (offset : Nat) (bits : Nat) (source : Term)
      (compound : Option CompoundPacketReg := none)
  deriving BEq, Repr, Inhabited

/-- The lookup event on the address pre-image ties a slot to its saved Map and key. -/
def LookupTie (Pg : List Predicate) (event : NodeId) (map : Term)
    (key : List Term) : Prop :=
  ∃ keyPtr, Predicate.helper event .lookup (map :: keyPtr :: key) ∈ Pg

/-- Select the first lookup at the given event, then read its stored tail. -/
def lookupKeyAt (Pg : List Predicate) (event : NodeId) : Option (Term × List Term) := do
  let p ← Pg.find? fun p => match p with
    | .helper e .lookup _ => e == event
    | _ => false
  match p with
  | .helper _ .lookup (map :: _keyPtr :: key) => some (map, key)
  | _ => none

theorem lookupKeyAt_tie (Pg : List Predicate) (event : NodeId)
    (map : Term) (key : List Term) (h : lookupKeyAt Pg event = some (map, key)) :
    LookupTie Pg event map key := by
  unfold lookupKeyAt at h
  cases hf : Pg.find? (fun p => match p with
    | .helper e .lookup _ => e == event
    | _ => false) with
  | none => simp [hf] at h
  | some p =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    cases p with
    | helper e kind args =>
      cases kind <;> simp_all
      case lookup =>
        cases args with
        | nil => simp at h
        | cons m args =>
          cases args with
          | nil => simp at h
          | cons ptr tail =>
            simp at h
            rcases h with ⟨rfl, rfl⟩
            exact ⟨ptr, hm⟩
    | branch _ _ _ | ret _ | mapWrite _ _ _ _ _ _ | packetWrite _ _ _ _ _ _ =>
      simp_all

def Predicate.savedMapKey? : Predicate → Option (List Term)
  | .mapWrite _ _ key _ _ _ => some key
  | _ => none

theorem mapWrite_saved_key (event : NodeId) (map : Term) (key : List Term)
    (offset bits : Nat) (source : Term) :
    (Predicate.mapWrite event map key offset bits source).savedMapKey? = some key := rfl

inductive Location where
  | pos (j : Nat)
  | exit
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Semantic state. `mem` is the virtual byte store. Real registers stay in `exprs`. -/
structure SemState where
  exprs      : List Expr
  predicates : List Predicate
  mem        : Mem := .empty
  deriving Repr, Inhabited

def SemState.empty : SemState := { exprs := Expr.nil, predicates := [], mem := .empty }

theorem savedMapKey_expr_update (p : Predicate) (E updates : List Expr) :
    (SemState.mk (E.override updates) [p] .empty).predicates = [p] := rfl

theorem lookupKeyAt_expr_update (E updates : List Expr) (Pg : List Predicate)
    (event : NodeId) :
    lookupKeyAt (SemState.mk (E.override updates) Pg .empty).predicates event =
      lookupKeyAt Pg event := rfl

theorem lookupKeyAt_deterministic (Pg : List Predicate) (event : NodeId)
    (map₁ map₂ : Term) (key₁ key₂ : List Term)
    (h₁ : lookupKeyAt Pg event = some (map₁, key₁))
    (h₂ : lookupKeyAt Pg event = some (map₂, key₂)) :
    map₁ = map₂ ∧ key₁ = key₂ := by
  exact Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))

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

end Core
