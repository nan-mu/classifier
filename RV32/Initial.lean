import Node.Path

namespace RV32
open Core Node

/-! RV32 wrapper entry and six XDP context slots (RV32 section of `doc/NodeInference/create.md`). -/

-- Stable names for the default symbolic calling-environment inputs.
namespace EntryVar
def sp : Nat := 0
def ctx : Nat := 1
def data : Nat := 4
def len : Nat := 5
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
  rEntries : List Reg

private def leaf32 : Term → Bool
  | .const .w32 c => c < (1 <<< 32)
  | .var .w32 _ => true
  | _ => false

private def validEntryReg (r : Reg) : Bool :=
  r.kind == .real && r.width == .w32 &&
    (r.alpha == 1 || r.alpha == 8 || r.alpha == 9 || (11 ≤ r.alpha && r.alpha < 32))

/-- Callee-saved registers s0..s11 retain the wrapper's entry-position term. -/
def savedRegs : List Reg :=
  [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27].map Reg.real32

/-- The seven intentional real-register entry bindings, before the entry overwrite. -/
def buildEBase (p : EntryParams) : ExprSet :=
  ExprSet.empty
    |>.insertEq (Reg.real32 0) (Term.C32 0)
    |>.insertEq (Reg.real32 1) p.tReturn
    |>.insertEq (Reg.real32 2) p.tSp
    |>.insertEq (Reg.real32 5) p.tSp
    |>.insertEq (Reg.real32 6) p.tReturn
    |>.insertEq (Reg.real32 7) p.tFrame
    |>.insertEq (Reg.real32 10) p.tCtx

/-- The call overwrites ra with tReturn; other entry registers retain tEntry. -/
def buildEReal0 (p : EntryParams) : ExprSet :=
  p.rEntries.foldl (fun E r =>
    if r == Reg.real32 1 then E else E.insertEq r p.tEntry) (buildEBase p)

/-- Validate the real-register input contract. Concrete entry=0 and misaligned SP fail. -/
def buildRealE0 (p : EntryParams) : Except RejectReason ExprSet := do
  if !p.rEntries.all validEntryReg ||
      p.rEntries.eraseDups.length != p.rEntries.length then throw .invalidEntry
  if ![p.tEntry, p.tReturn, p.tFrame, p.tSp, p.tCtx].all leaf32 then
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

/-- Values of the six bound xdp_md Context cells; no access Predicates are invented. -/
def buildECtx0 (p : EntryParams) : ExprSet :=
  let tEnd := addStar .w32 p.tData p.tLen
  let fields := [p.tData, tEnd, Term.C32 0, Term.C32 p.ιWifi, Term.C32 0, Term.C32 0]
  ((List.range 6).zip fields).foldl
    (fun E jt => E.insertEq (Reg.ctx32 (p.αCtx + jt.1)) jt.2) ExprSet.empty

/-- E0 is the disjoint union of real-register and Context-cell Exprs; P0 is empty. -/
def buildE0 (p : EntryParams) : Except RejectReason SemState := do
  if ![p.tData, p.tLen].all leaf32 || p.ιWifi ≥ (1 <<< 32) then throw .invalidEntry
  let Ereal ← buildRealE0 p
  let Ectx := buildECtx0 p
  let E0 : ExprSet := { entries := Ereal.entries ++ Ectx.entries }
  if !E0.keysUnique then throw .invalidEntry
  pure ⟨E0, []⟩

/-- Entry state consumed by the existing Expand adapter. -/
def entrySemState (p : EntryParams) : Except RejectReason SemState := buildE0 p

end RV32
