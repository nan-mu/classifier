import Node.Path
import Core.Anchor

namespace EBPF
open Core Node

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
  αCtx : Nat
  κPacket : Nat
  φStack : Nat
  deriving Repr, Inhabited

private def leaf (w : Width) : Term → Bool
  | .const v c => v == w && c < (1 <<< w.bits)
  | .var v _ => v == w
  | _ => false

def buildE0 (p : EntryParams) : Except RejectReason SemState := do
  if !leaf .w64 p.tCtx || !leaf .w64 p.tSp || !leaf .w32 p.tData ||
      p.packetBytes ≥ (1 <<< 32) then throw .invalidEntry
  pure ⟨Expr.nil.insertEq (Reg.real64 1) p.tCtx
    |>.insertEq (Reg.real64 10) p.tSp
    |>.insertEq (Reg.ctx32 p.αCtx) p.tData
    |>.insertEq (Reg.ctx32 (p.αCtx + 1))
      (addStar .w32 p.tData (Term.C32 p.packetBytes)), []⟩

def entrySemState := buildE0

def entryRows (p : EntryParams) : List (Anchor × Term) :=
  [(.entry (.ctx .w64), p.tCtx), (.entry (.sp .w64), p.tSp), (.entry (.data .w32), p.tData),
    (.entry .packetBytes, Term.C32 p.packetBytes), (.entry .alphaCtx, Term.C32 p.αCtx),
    (.entry .packetId, Term.C32 p.κPacket), (.entry .stackId, Term.C32 p.φStack)]

def entryParams? (E : List Expr) : Option EntryParams := do
  let tCtx ← E.lookupEq (Reg.anchor (.entry (.ctx .w64)))
  let tSp ← E.lookupEq (Reg.anchor (.entry (.sp .w64)))
  let tData ← E.lookupEq (Reg.anchor (.entry (.data .w32)))
  let packetBytes ← anchorNat E (.entry .packetBytes)
  let αCtx ← anchorNat E (.entry .alphaCtx)
  let κPacket ← anchorNat E (.entry .packetId)
  let φStack ← anchorNat E (.entry .stackId)
  if packetBytes ≥ (1 <<< 32) || αCtx ≥ (1 <<< 32) || κPacket ≥ (1 <<< 32) ||
      φStack ≥ (1 <<< 32) then none
  else some { tCtx, tSp, tData, packetBytes, αCtx, κPacket, φStack }

/-- Install entry anchors, then map layouts. A failed map install keeps the entry anchors. -/
def host (p : EntryParams) (E : List Expr) (maps : List MapLayout := []) : List Expr :=
  let withEntry := (Anchor.install E (entryRows p)).getD E
  match Anchor.mapRows (maps.map (·.mapId)) (maps.map (·.keySize)) (maps.map (·.valueSize)) with
  | some rows => (Anchor.install withEntry rows).getD withEntry
  | none => withEntry

#guard match buildE0 ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64, 3, 4, 5⟩ with
  | .ok σ => σ.exprs.lookupEq (Reg.ctx32 3) == some (Term.V32 2) &&
      σ.exprs.lookupEq (Reg.ctx32 4) ==
        some (addStar .w32 (Term.V32 2) (Term.C32 64)) &&
      σ.exprs.lookupEq (Reg.ctx32 5) == none && σ.predicates.isEmpty
  | _ => false
#guard match buildE0 ⟨Term.V64 1, Term.V64 0, Term.V64 2, 64, 3, 4, 5⟩ with
  | .error .invalidEntry => true
  | _ => false
#guard match buildE0 ⟨Term.V64 1, Term.V64 0, .const .w32 (1 <<< 32), 64, 3, 4, 5⟩ with
  | .error .invalidEntry => true
  | _ => false

end EBPF
