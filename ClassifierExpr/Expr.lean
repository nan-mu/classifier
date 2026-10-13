import ClassifierExpr.Bits
import ClassifierExpr.Reg
import ClassifierExpr.Numeric
import ClassifierExpr.Term

namespace ClassifierExpr

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

/-- Interpret one Expr under register/value assignments (math §10.3). -/
def interpretExpr (ρ : Reg → Nat) (ν : Var → Nat) (e : Expr) : Bool :=
  let rec termVal : Term → Nat
    | .const _ c => c
    | .var w ξ => ν ⟨w, ξ, none⟩
    | .regVar event r => ν ⟨r.width, r.alpha, some (event, r)⟩
    | .app _ op args =>
        match interpretOp op (args.map termVal) with
        | some v => v
        | none => 0
  interpretRel e.reg.width.bits e.rel (ρ e.reg) (termVal e.term)

/-! ## Value bindings and comparison constraints -/

/-- Value bindings are unique per register; constraints are structurally unique. -/
structure ExprSet where
  entries : List Expr
  constraints : List Expr := []
  deriving BEq, Repr, Inhabited

def ExprSet.empty : ExprSet := { entries := [] }

def ExprSet.toList (E : ExprSet) : List Expr := E.entries ++ E.constraints

def ExprSet.wellTyped (E : ExprSet) : Bool :=
  E.entries.all (fun e => e.rel == .eq) &&
    E.toList.all (fun e => e.reg.valid && e.reg.width == e.term.width)

def ExprSet.keysUnique (E : ExprSet) : Bool :=
  Id.run do
    let mut seen : List (Reg × Rel) := []
    for e in E.entries do
      if seen.elem e.key then return false
      seen := e.key :: seen
    pure (E.constraints.eraseDups == E.constraints)

def ExprSet.find? (E : ExprSet) (k : Reg × Rel) : Option Expr :=
  E.entries.find? (fun e => e.key == k)

def ExprSet.lookup (E : ExprSet) (r : Reg) (rel : Rel) : Option Term :=
  match E.find? (r, rel) with
  | some e => some e.term
  | none => none

def ExprSet.lookupEq (E : ExprSet) (r : Reg) : Option Term :=
  E.lookup r .eq

/-- Add a comparison without replacing the register's value binding. -/
def ExprSet.insertConstraint (E : ExprSet) (e : Expr) : ExprSet :=
  let e := solveExpr e
  { E with constraints := if E.constraints.contains e then E.constraints else E.constraints ++ [e] }

/-- Insert an equality as an assignment; other relations only add constraints. -/
def ExprSet.insert (E : ExprSet) (e : Expr) : ExprSet :=
  if e.rel != .eq then E.insertConstraint e else
    let e := solveExpr e
    { entries := e :: E.entries.filter (fun x => x.reg != e.reg)
      constraints := E.constraints.filter (fun x => x.reg != e.reg) }

def ExprSet.insertEq (E : ExprSet) (r : Reg) (t : Term) : ExprSet :=
  E.insert (Expr.mkEq r t)

/-- Equalities become value bindings; other relations become constraints. -/
def ExprSet.ofList? (es : List Expr) : Option ExprSet :=
  let es := es.map solveExpr
  let E : ExprSet := {
    entries := es.filter (fun e => e.rel == .eq)
    constraints := es.filter (fun e => e.rel != .eq) }
  if E.keysUnique && E.wellTyped then some E else none

def ExprSet.ofList! (es : List Expr) : ExprSet :=
  match ExprSet.ofList? es with
  | some E => E
  | none => { entries := [] }

/-- Override \(E_g\times E_i\) (`doc/Expr/待处理.md#关系集合按键覆写`). -/
def ExprSet.override (Eg Ei : ExprSet) : ExprSet :=
  let untouched (e : Expr) := !(Ei.entries.any (fun ei => ei.reg == e.reg))
  let base : ExprSet := {
    entries := Eg.entries.filter untouched ++ Ei.entries
    constraints := Eg.constraints.filter untouched }
  Ei.constraints.foldl ExprSet.insertConstraint base

def ExprSet.mapTerms (E : ExprSet) (f : Term → Term) : ExprSet :=
  { entries := E.entries.map fun e => { e with term := f e.term }
    constraints := (E.constraints.map fun e => { e with term := f e.term }).eraseDups }

def ExprSet.solveAll (E : ExprSet) : ExprSet :=
  E.mapTerms solve

/-- Filter to a single register's relations. -/
def ExprSet.forReg (E : ExprSet) (r : Reg) : List Expr :=
  E.toList.filter (fun e => e.reg == r)

end ClassifierExpr
