import CommonMath.Path

namespace RV32IMC
open CommonMath

/-! RV32 wrapper entry and six XDP context slots (§§1–4 of `doc/RV32初态描述.md`). -/

-- Stable names for the default symbolic calling-environment inputs.
namespace EntryVar
def sp : Nat := 0
def ctx : Nat := 1
def gp : Nat := 2
def tp : Nat := 3
def data : Nat := 4
def len : Nat := 5
def saved (r : Nat) : Nat := 32 + r
end EntryVar

/-- Initialization inputs, not another component of the execution state.
The caller supplies the actual wrapper and address-to-slot bindings.
Symbolic SP alignment and resource validity remain calling-contract premises. -/
structure EntryParams where
  tEntry  : Term
  tReturn : Term
  tFrame  : Term
  tSp     : Term
  tCtx    : Term
  tData   : Term
  tLen    : Term
  ιWifi   : Nat
  αCtx    : Nat
  tGp     : Term
  tTp     : Term
  rEntry  : Reg
  savedVar : Nat → Nat := EntryVar.saved

private def leaf32 : Term → Bool
  | .const .w32 c => c < (1 <<< 32)
  | .var .w32 _ => true
  | _ => false

private def validEntryReg (r : Reg) : Bool :=
  r.kind == .real && r.width == .w32 &&
    (r.alpha == 1 || r.alpha == 8 || r.alpha == 9 || (11 ≤ r.alpha && r.alpha < 32))

private def baseRegs : List Nat := List.range 11 ++ (List.range 10).map (18 + ·)

private def initialTerm (p : EntryParams) (r : Nat) : Term :=
  if r == 0 then Term.C32 0
  else if r == 1 then p.tReturn -- JALR has already overwritten ra, even when rEntry = ra.
  else
    match r with
    | 2 | 5 => p.tSp
    | 3 => p.tGp
    | 4 => p.tTp
    | 6 => p.tReturn
    | 7 => p.tFrame
    | 10 => p.tCtx
    | _ => Term.V32 (p.savedVar r)

/-- The 21 real-register equalities in the §2 base table, before the entry overwrite. -/
def buildEBase (p : EntryParams) : ExprSet :=
  baseRegs.foldl (fun E r => E.insertEq (Reg.real32 r) (initialTerm p r)) ExprSet.empty

/-- The call overwrites ra with tReturn; any other entry register retains tEntry. -/
def buildEReal0 (p : EntryParams) : ExprSet :=
  let Ebase := buildEBase p
  if p.rEntry == Reg.real32 1 then Ebase
  else updateExpr Ebase (ExprSet.empty.insertEq p.rEntry p.tEntry)

/-- Validate the real-register input contract. Concrete entry=0 and misaligned SP fail. -/
def buildRealE0 (p : EntryParams) : Except RejectReason ExprSet := do
  if !validEntryReg p.rEntry then throw .invalidEntry
  if ![p.tEntry, p.tReturn, p.tFrame, p.tSp, p.tCtx, p.tGp, p.tTp].all leaf32 then
    throw .invalidEntry
  match p.tEntry with
  | .const _ 0 => throw .invalidEntry
  | _ => pure ()
  match p.tSp with
  | .const _ c => if c % 16 != 0 then throw .invalidEntry
  | _ => pure ()
  let Ereal := buildEReal0 p
  if !Ereal.keysUnique then throw .invalidEntry
  pure Ereal

/-- Values of the six bound xdp_md stack-word slots (§3); no access Predicates are invented. -/
def buildECtx0 (p : EntryParams) : ExprSet :=
  let tEnd := addStar .w32 p.tData p.tLen
  let fields := [p.tData, tEnd, Term.C32 0, Term.C32 p.ιWifi, Term.C32 0, Term.C32 0]
  ((List.range 6).zip fields).foldl
    (fun E jt => E.insertEq (Reg.sw (p.αCtx + jt.1)) jt.2) ExprSet.empty

/-- E0 is the disjoint union of real-register and context-slot Exprs; P0 is empty for MVP. -/
def buildE0 (p : EntryParams) : Except RejectReason SemState := do
  if ![p.tData, p.tLen].all leaf32 || p.ιWifi ≥ (1 <<< 32) then throw .invalidEntry
  if p.αCtx + 5 ≥ (1 <<< 32) then throw .invalidEntry
  let Ereal ← buildRealE0 p
  let Ectx := buildECtx0 p
  let E0 : ExprSet := { entries := Ereal.entries ++ Ectx.entries }
  if !E0.keysUnique then throw .invalidEntry
  pure ⟨E0, []⟩

/-- Entry state consumed by the existing Expand adapter. -/
def entrySemState (p : EntryParams) : Except RejectReason SemState := buildE0 p

end RV32IMC
