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
def buildEBase (p : EntryParams) : List Expr :=
  Expr.nil
    |>.insertEq (Reg.real32 0) (Term.C32 0)
    |>.insertEq (Reg.real32 1) p.tReturn
    |>.insertEq (Reg.real32 2) p.tSp
    |>.insertEq (Reg.real32 5) p.tSp
    |>.insertEq (Reg.real32 6) p.tReturn
    |>.insertEq (Reg.real32 7) p.tFrame
    |>.insertEq (Reg.real32 10) p.tCtx

/-- The call overwrites ra with tReturn; other entry registers retain tEntry. -/
def buildEReal0 (p : EntryParams) : List Expr :=
  p.rEntries.foldl (fun E r =>
    if r == Reg.real32 1 then E else E.insertEq r p.tEntry) (buildEBase p)

/-- Validate the real-register input contract. Concrete entry=0 and misaligned SP fail. -/
def buildRealE0 (p : EntryParams) : Except RejectReason (List Expr) := do
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

/-- The six xdp_md fields. Field identity is the index, not an architecture base. -/
def contextTerms (p : EntryParams) : List Term :=
  let tEnd := addStar .w32 p.tData p.tLen
  [p.tData, tEnd, Term.C32 0, Term.C32 p.ιWifi, Term.C32 0, Term.C32 0]

private def putField (mem : Mem) (field : Nat) (t : Term) : Except RejectReason Mem := do
  let tile ← match Tile.ofTerm t 32 with
    | .ok tile => pure tile
    | .error _ => throw .invalidEntry
  match mem.write (.context field) 0 tile with
  | .ok mem => pure mem
  | .error _ => throw .invalidEntry

/-- Context lives in memory. `αCtx` is not a field index. -/
def writeContext (p : EntryParams) : Except RejectReason Mem := do
  match contextTerms p with
  | [t0, t1, t2, t3, t4, t5] => do
      let mem ← putField .empty 0 t0
      let mem ← putField mem 1 t1
      let mem ← putField mem 2 t2
      let mem ← putField mem 3 t3
      let mem ← putField mem 4 t4
      putField mem 5 t5
  | _ => throw .invalidEntry

/-- Real registers stay in `exprs`. The six context fields are `mem`. -/
def buildE0 (p : EntryParams) : Except RejectReason SemState := do
  if ![p.tData, p.tLen].all leaf32 || p.ιWifi ≥ (1 <<< 32) then throw .invalidEntry
  let Ereal ← buildRealE0 p
  if !Ereal.keysUnique then throw .invalidEntry
  let mem ← writeContext p
  pure ⟨Ereal, [], mem⟩

/-- Entry state consumed by the existing Expand adapter. -/
def entrySemState (p : EntryParams) : Except RejectReason SemState := buildE0 p

end RV32
