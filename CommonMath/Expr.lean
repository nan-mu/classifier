import CommonMath.Bits
import CommonMath.Reg
import CommonMath.Numeric
import CommonMath.Term

namespace CommonMath

/-! ## Relations (`doc/common-math.md` §6) -/

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
  deriving Repr, Inhabited

def Expr.key (e : Expr) : Reg × Rel := (e.reg, e.rel)

def Expr.mkEq (r : Reg) (t : Term) : Expr := ⟨r, .eq, t⟩

def Expr.mkRel (r : Reg) (rel : Rel) (t : Term) : Expr := ⟨r, rel, t⟩

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

/-! ## Key-unique finite Expr sets \(\mathscr F(\mathrm{Expr})\) -/

/-- Finite Expr set. Invariant: keys unique. Prefer `ExprSet.insert` / `ofList?`. -/
structure ExprSet where
  entries : List Expr
  deriving Repr, Inhabited

def ExprSet.empty : ExprSet := ⟨[]⟩

def ExprSet.toList (E : ExprSet) : List Expr := E.entries

def ExprSet.wellTyped (E : ExprSet) : Bool :=
  E.entries.all (fun e => e.reg.valid && e.reg.width == e.term.width)

def ExprSet.keysUnique (E : ExprSet) : Bool :=
  Id.run do
    let mut seen : List (Reg × Rel) := []
    for e in E.entries do
      if seen.elem e.key then return false
      seen := e.key :: seen
    pure true

def ExprSet.find? (E : ExprSet) (k : Reg × Rel) : Option Expr :=
  E.entries.find? (fun e => e.key == k)

def ExprSet.lookup (E : ExprSet) (r : Reg) (rel : Rel) : Option Term :=
  match E.find? (r, rel) with
  | some e => some e.term
  | none => none

def ExprSet.lookupEq (E : ExprSet) (r : Reg) : Option Term :=
  E.lookup r .eq

/-- Insert with override of the same key. -/
def ExprSet.insert (E : ExprSet) (e : Expr) : ExprSet :=
  let e := solveExpr e
  ⟨e :: E.entries.filter (fun x => x.key != e.key)⟩

def ExprSet.insertEq (E : ExprSet) (r : Reg) (t : Term) : ExprSet :=
  E.insert (Expr.mkEq r t)

/-- Build from a list; `none` if duplicate keys. -/
def ExprSet.ofList? (es : List Expr) : Option ExprSet :=
  let E : ExprSet := ⟨es.map solveExpr⟩
  if E.keysUnique then some E else none

def ExprSet.ofList! (es : List Expr) : ExprSet :=
  match ExprSet.ofList? es with
  | some E => E
  | none => ⟨[]⟩

/-- Override \(E_g\times E_i\) (`doc/rv32imc-expr-value-functions.md` §2.3). -/
def ExprSet.override (Eg Ei : ExprSet) : ExprSet :=
  let kept := Eg.entries.filter (fun e => !(Ei.entries.any (fun ei => ei.key == e.key)))
  ⟨kept ++ Ei.entries⟩

def ExprSet.mapTerms (E : ExprSet) (f : Term → Term) : ExprSet :=
  ⟨E.entries.map fun e => { e with term := f e.term }⟩

def ExprSet.solveAll (E : ExprSet) : ExprSet :=
  E.mapTerms solve

/-- Filter to a single register's relations. -/
def ExprSet.forReg (E : ExprSet) (r : Reg) : List Expr :=
  E.entries.filter (fun e => e.reg == r)

end CommonMath
