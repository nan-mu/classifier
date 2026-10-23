import Node.Path
import Core.Interval

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
  rEntries : List Reg

private def leaf32 : Term → Bool
  | .const .w32 c => c < (1 <<< 32)
  | .var .w32 _ => true
  | _ => false

private def validEntryReg (r : Reg) : Bool :=
  match r with
  | .real idx 0 32 => idx == 1 || idx == 8 || idx == 9 || (11 ≤ idx && idx < 32)
  | _ => false

/-- Callee-saved registers s0..s11 retain the wrapper's entry-position term. -/
def savedRegs : List Reg :=
  [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27].map Reg.real32

/-- The seven intentional real-register entry bindings, before the entry overwrite. -/
def buildEBase (p : EntryParams) : List Expr :=
  Expr.nil
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 0) (solve (Term.C32 0))], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 1) (solve p.tReturn)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve p.tSp)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 5) (solve p.tSp)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 6) (solve p.tReturn)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 7) (solve p.tFrame)], predicates := [] }).exprs)
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve p.tCtx)], predicates := [] }).exprs)

/-- The call overwrites ra with tReturn; other entry registers retain tEntry. -/
def buildEReal0 (p : EntryParams) : List Expr :=
  p.rEntries.foldl (fun E r =>
    if r == Reg.real32 1 then E else (update ⟨E, []⟩ { exprs := [Expr.mkEq r (solve p.tEntry)], predicates := [] }).exprs) (buildEBase p)

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

private def putField (E : List Expr) (j : ContextField) (t : Term) :
    Except RejectReason (List Expr) :=
  match putContext E j t with
  | some E => pure E
  | none => throw .invalidEntry

/-- The six `xdp_md` fields are context intervals, including the intentional zeros. -/
def writeContext (p : EntryParams) : Except RejectReason (List Expr) := do
  match contextTerms p, xdpFields with
  | [t0, t1, t2, t3, t4, t5], [j0, j1, j2, j3, j4, j5] => do
      let E ← putField Expr.nil j0 t0
      let E ← putField E j1 t1
      let E ← putField E j2 t2
      let E ← putField E j3 t3
      let E ← putField E j4 t4
      putField E j5 t5
  | _, _ => throw .invalidEntry

/-- Real registers and the six context intervals share `exprs`. -/
def buildE0 (p : EntryParams) : Except RejectReason SemState := do
  if ![p.tData, p.tLen].all leaf32 || p.ιWifi ≥ (1 <<< 32) then throw .invalidEntry
  let Ereal ← buildRealE0 p
  let Ectx ← writeContext p
  let E := (update ⟨Ereal, []⟩ { exprs := Ectx, predicates := [] }).exprs
  if !E.keysUnique then throw .invalidEntry
  pure ⟨E, []⟩

/-- Entry state consumed by the existing Expand adapter. -/
def entrySemState (p : EntryParams) : Except RejectReason SemState := buildE0 p

end RV32
