import Node.Path
import Interface.Update
import Expression.Resource.Anchor

namespace Cross.EBPF
open Term Term.Value Expression Observation Interface Interface.Step Inbox.Wire Node

/-! External correspondence TBD.
The entry binds r1=tCtx, r10=tSp, xdp_md.data=tData and data_end=tData+packetBytes.
The other four xdp_md fields, packet resource validity and stack region contents
are not bound here. Uninitialized registers have no equality.
RV32's context layout, wrapper bindings and return address are not equated here. -/
structure EntryParams where
  tCtx : Term
  tSp : Term
  tData : Term
  packetBytes : Nat
  deriving Repr, Inhabited

private def leaf (w : Width) : Term → Bool
  | .const v c => v == w && c < (1 <<< w.bits)
  | .var v _ => v == w
  | _ => false

private def put (E : List Expr) (j : ContextField) (t : Term) : Except RejectReason (List Expr) :=
  match putContext E j t with
  | some E => pure E
  | none => throw .invalidEntry

def buildE0 (p : EntryParams) : Except RejectReason State := do
  if !leaf .w64 p.tCtx || !leaf .w64 p.tSp || !leaf .w32 p.tData ||
      p.packetBytes ≥ (1 <<< 32) then throw .invalidEntry
  let E ← put Expr.nil .ctx p.tCtx
  let E ← put E .sp p.tSp
  let E ← put E .data p.tData
  let E ← put E .dataEnd (addStar .w32 p.tData (Term.C32 p.packetBytes))
  let E ← put E .packetBytes (Term.C32 p.packetBytes)
  let E := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real64 1) (solve p.tCtx)], predicates := [] }).exprs |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real64 10) (solve p.tSp)], predicates := [] }).exprs)
  pure ⟨E, []⟩

def entryState := buildE0

def entryParams? (E : List Expr) : Option EntryParams := do
  let tCtx ← contextValue E .ctx
  let tSp ← contextValue E .sp
  let tData ← contextValue E .data
  let packetBytes ← contextNat E .packetBytes
  if packetBytes ≥ (1 <<< 32) then none
  else some { tCtx, tSp, tData, packetBytes }

/-- Install the frozen entry facts, then map layouts. A failed map install keeps the entry facts. -/
def host (p : EntryParams) (E : List Expr) (maps : List MapLayout := []) : List Expr :=
  let withEntry := match buildE0 p with
    | .ok σ =>
      let fresh := σ.exprs.filter fun e =>
        match e.reg with
        | .real .. => !(E.bindings.any fun old => old.reg.overlaps e.reg)
        | _ => true
      (update ⟨E, []⟩ { exprs := fresh, predicates := [] }).exprs
    | .error _ => E
  (Anchor.installMaps withEntry maps).getD withEntry

#guard match buildE0 ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64⟩ with
  | .ok σ =>
      contextValue σ.exprs .data == some (Term.V32 2) &&
        contextValue σ.exprs .dataEnd ==
          some (addStar .w32 (Term.V32 2) (Term.C32 64)) &&
        contextValue σ.exprs .ctx == some (Term.V64 1) &&
        contextValue σ.exprs .sp == some (Term.V64 0) &&
        contextNat σ.exprs .packetBytes == some 64 &&
        σ.exprs.lookupEq (Reg.real64 1) == some (Term.V64 1) &&
        σ.exprs.lookupEq (Reg.real64 10) == some (Term.V64 0) &&
        (contextValue σ.exprs .dataMeta).isNone &&
        σ.predicates.isEmpty
  | _ => false
#guard match buildE0 ⟨Term.V64 1, Term.V64 0, Term.V64 2, 64⟩ with
  | .error .invalidEntry => true
  | _ => false
#guard match buildE0 ⟨Term.V64 1, Term.V64 0, .const .w32 (1 <<< 32), 64⟩ with
  | .error .invalidEntry => true
  | _ => false

end Cross.EBPF
