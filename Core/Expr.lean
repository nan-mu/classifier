import Core.Bits
import Core.Reg
import Core.Numeric
import Core.Term

namespace Core

/-! ## Relations (`doc/Expr/待处理.md#关系符定义`) -/

inductive Rel where
  | eq | ne
  | ltu | leu | gtu | geu
  | lts | les | gts | ges
  | eqN (q : Nat) | neN (q : Nat)
  | ltuN (q : Nat) | leuN (q : Nat) | gtuN (q : Nat) | geuN (q : Nat)
  | ltsN (q : Nat) | lesN (q : Nat) | gtsN (q : Nat) | gesN (q : Nat)
  | bitsnz (q : Nat) | bitsz (q : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Complement \(\overline{\bowtie}\). -/
def Rel.compl : Rel → Rel
  | .eq => .ne
  | .ne => .eq
  | .ltu => .geu
  | .leu => .gtu
  | .gtu => .leu
  | .geu => .ltu
  | .lts => .ges
  | .les => .gts
  | .gts => .les
  | .ges => .lts
  | .eqN q => .neN q
  | .neN q => .eqN q
  | .ltuN q => .geuN q
  | .leuN q => .gtuN q
  | .gtuN q => .leuN q
  | .geuN q => .ltuN q
  | .ltsN q => .gesN q
  | .lesN q => .gtsN q
  | .gtsN q => .lesN q
  | .gesN q => .ltsN q
  | .bitsnz q => .bitsz q
  | .bitsz q => .bitsnz q

def interpretRel (wbits : Nat) (rel : Rel) (a b : Nat) : Bool :=
  let a := MNat wbits a; let b := MNat wbits b
  match rel with
  | .eq => a == b
  | .ne => a != b
  | .ltu => a < b
  | .leu => a ≤ b
  | .gtu => a > b
  | .geu => a ≥ b
  | .lts => s wbits a < s wbits b
  | .les => s wbits a ≤ s wbits b
  | .gts => s wbits a > s wbits b
  | .ges => s wbits a ≥ s wbits b
  | .eqN q => MNat q a == MNat q b
  | .neN q => MNat q a != MNat q b
  | .ltuN q => MNat q a < MNat q b
  | .leuN q => MNat q a ≤ MNat q b
  | .gtuN q => MNat q a > MNat q b
  | .geuN q => MNat q a ≥ MNat q b
  | .ltsN q => s q (MNat q a) < s q (MNat q b)
  | .lesN q => s q (MNat q a) ≤ s q (MNat q b)
  | .gtsN q => s q (MNat q a) > s q (MNat q b)
  | .gesN q => s q (MNat q a) ≥ s q (MNat q b)
  | .bitsnz q => AND q (MNat q a) (MNat q b) != 0
  | .bitsz q => AND q (MNat q a) (MNat q b) == 0

/-! ## Expr = Reg × Rel × Term -/

structure Expr where
  reg  : Reg
  rel  : Rel
  term : Term
  deriving BEq, Repr, Inhabited

def Expr.key (e : Expr) : Reg × Rel := (e.reg, e.rel)

def Expr.mkEq (r : Reg) (t : Term) : Expr := ⟨r, .eq, t⟩

def Expr.mkRel (r : Reg) (rel : Rel) (t : Term) : Expr := ⟨r, rel, t⟩

/-- Decide using the pre-instruction value of the left register. -/
def Expr.decideWith (e : Expr) (lhs : Term) : Option Bool := do
  if lhs.width != e.reg.width || e.term.width != e.reg.width then none else
    let a ← eval (solve lhs)
    let b ← eval (solve e.term)
    pure (interpretRel e.reg.width.bits e.rel a b)

def solveExpr (e : Expr) : Expr := { e with term := solve e.term }

/-- Partial interpretation. Missing external meanings and malformed terms remain undefined. -/
def interpretExpr (ρ : Reg → Nat) (ν : Var → Nat) (θ : ExternalInterpretation)
    (e : Expr) : Option Bool := do
  if !e.reg.valid || e.term.width != e.reg.width then none else
    let value ← interpretTerm ν θ e.term
    pure (interpretRel e.reg.width.bits e.rel (ρ e.reg) value)

/-! ## Expr lists

A state holds `List Expr`, the same shape as `List Predicate`. Each row is
`(Reg, Rel, Term)`. The first `eq` of a register is its value. Later rows,
including another `eq`, are comparisons and do not replace that value.
Assignment prepends and deletes every older row of that register. -/

def Expr.nil : List Expr := []

end Core

namespace List

open Core

/-- The value rows: the first equality of each register, in list order. -/
def bindings (E : List Expr) : List Expr :=
  E.foldl (fun acc e =>
    if e.rel == .eq && !(acc.any (fun v => v.reg == e.reg)) then acc ++ [e] else acc) []

/-- Every row that is not the value equality of its register. -/
def constraints (E : List Expr) : List Expr :=
  E.filter fun e => !(E.bindings.contains e)

def wellTyped (E : List Expr) : Bool :=
  E.all fun e => e.reg.valid && e.reg.width == e.term.width

/-- Rows are structurally unique. Several relations may share one register. -/
def keysUnique (E : List Expr) : Bool :=
  E.eraseDups == E

/-- Source lookup reads the first equality. Other relations read comparisons. -/
def lookupRel (E : List Expr) (r : Reg) (rel : Rel) : Option Term :=
  let rows := if rel == .eq then E.bindings else E.constraints
  (rows.find? (fun e => e.reg == r && e.rel == rel)).map (·.term)

def lookupEq (E : List Expr) (r : Reg) : Option Term :=
  E.lookupRel r .eq

/-- Append a comparison. An equality here does not replace the register's value. -/
def insertConstraint (E : List Expr) (e : Expr) : List Expr :=
  let e := solveExpr e
  if E.contains e then E else E ++ [e]

/-- Insert an equality as an assignment; any other relation is only a comparison. -/
def insertExpr (E : List Expr) (e : Expr) : List Expr :=
  if e.rel != .eq then E.insertConstraint e else
    let e := solveExpr e
    e :: E.filter (fun x => x.reg != e.reg)

def insertEq (E : List Expr) (r : Reg) (t : Term) : List Expr :=
  E.insertExpr (Expr.mkEq r t)

/-- Override \(E_g\times E_i\). Equality rows in \(E_i\) are assignments.
A comparison equality is not an assignment; `applyLocal` appends those from the
branch predicate instead of passing them through this write set. -/
def override (Eg Ei : List Expr) : List Expr :=
  let writes := Ei.bindings
  let keep (e : Expr) := !(writes.any (fun w => w.reg == e.reg))
  Ei.constraints.foldl insertConstraint ((Eg.filter keep) ++ writes)

def mapTerms (E : List Expr) (f : Term → Term) : List Expr :=
  (E.map fun e => { e with term := f e.term }).eraseDups

def solveAll (E : List Expr) : List Expr :=
  E.mapTerms solve

def forReg (E : List Expr) (r : Reg) : List Expr :=
  E.filter (fun e => e.reg == r)

end List
