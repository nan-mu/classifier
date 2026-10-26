import Term.Value.Bits
import Expression.Reg
import Term.Value.Numeric
import Term.Basic

namespace Expression
open Term Term.Value

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

/-- Operand-swap dual. Equality, inequality and bit tests stay. -/
def Rel.swap : Rel → Rel
  | .ltu => .gtu | .gtu => .ltu | .leu => .geu | .geu => .leu
  | .lts => .gts | .gts => .lts | .les => .ges | .ges => .les
  | .ltuN q => .gtuN q | .gtuN q => .ltuN q
  | .leuN q => .geuN q | .geuN q => .leuN q
  | .ltsN q => .gtsN q | .gtsN q => .ltsN q
  | .lesN q => .gesN q | .gesN q => .lesN q
  | r => r

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
  if lhs.semanticBits != e.reg.bits || e.term.semanticBits != e.reg.bits then none else
    let a ← eval (solve lhs)
    let b ← eval (solve e.term)
    pure (interpretRel e.reg.bits e.rel a b)

def solveExpr (e : Expr) : Expr := { e with term := solve e.term }

/-- Partial interpretation. Missing external meanings and malformed terms remain undefined. -/
def interpretExpr (ρ : Reg → Nat) (ν : Var → Nat) (θ : ExternalInterpretation)
    (e : Expr) : Option Bool := do
  if !e.reg.valid || e.term.semanticBits != e.reg.bits then none else
    let value ← interpretTerm ν θ e.term
    pure (interpretRel e.reg.bits e.rel (ρ e.reg) value)

/-! ## Expr lists

A state holds `List Expr`, the same shape as `List Observation`. Each row is
`(Reg, Rel, Term)`. The first `eq` of a register is its value. Later rows,
including another `eq`, are comparisons and do not replace that value.
Assignment prepends and deletes every older row of that register. -/

def Expr.nil : List Expr := []

end Expression

namespace List

open Term Expression

/-- The value rows: the first equality of each register, in list order. -/
def bindings (E : List Expr) : List Expr :=
  E.foldl (fun acc e =>
    if e.rel == .eq && !(acc.any (fun v => v.reg == e.reg)) then acc ++ [e] else acc) []

/-- Every row that is not the value equality of its register. -/
def constraints (E : List Expr) : List Expr :=
  E.filter fun e => !(E.bindings.contains e)

def wellTyped (E : List Expr) : Bool :=
  E.all fun e => e.reg.valid && e.term.semanticBits == e.reg.bits

/-- Rows are structurally unique. Several relations may share one register. -/
def keysUnique (E : List Expr) : Bool :=
  E.eraseDups == E

/-- Source lookup reads the first equality. Other relations read comparisons. -/
def lookupRel (E : List Expr) (r : Reg) (rel : Rel) : Option Term :=
  let rows := if rel == .eq then E.bindings else E.constraints
  (rows.find? (fun e => e.reg == r && e.rel == rel)).map (·.term)

def lookupEq (E : List Expr) (r : Reg) : Option Term :=
  E.lookupRel r .eq

def forReg (E : List Expr) (r : Reg) : List Expr :=
  E.filter (fun e => e.reg == r)

end List
