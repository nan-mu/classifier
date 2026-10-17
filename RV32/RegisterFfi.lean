import RV32.Expr
import RV32.Initial
import Core.Render

namespace RV32
open Core

private def bindingEntry : ExprSet :=
  let fields := [Term.V32 4, addStar .w32 (Term.V32 4) (Term.C32 64),
    Term.C32 0, Term.C32 0, Term.C32 0, Term.C32 0]
  let E := fields.zipIdx.foldl (fun E (t, j) => E.insertEq (Reg.ctx32 j) t) ExprSet.empty
  E.insertEq (Reg.real32 2) (Term.V32 0)
    |>.insertEq (Reg.real32 10) (Term.V32 1)

private def effectJson (effect : ExprEffect) : String :=
  s!"\{\"inputs\":[{renderExprSetJson effect.inputs}],\"updates\":[{renderExprSetJson effect.updates}]}"

private def packetOverlap (value : Nat) : Option String := do
  let E := bindingEntry.insertEq (Reg.real32 12)
    (addStar .w32 (Term.V32 4) (Term.C32 3))
    |>.insertEq (Reg.real32 13) (Term.C32 value)
  let first ← stepEffects E (.LOAD (0#12, .Regidx 12#5, .Regidx 14#5, true, 4))
  let E := E.override first.delta
  let store ← stepEffects E (.STORE (2#12, .Regidx 13#5, .Regidx 12#5, 2))
  let E := E.override store.delta
  let reload ← stepEffects E (.LOAD (0#12, .Regidx 12#5, .Regidx 15#5, true, 4))
  let E := E.override reload.delta
  let alias := E.insertEq (Reg.real32 16)
    (addStar .w32 (addStar .w32 (Term.V32 4) (Term.C32 1)) (Term.C32 4))
  let byte ← stepEffects alias (.LOAD (0#12, .Regidx 16#5, .Regidx 17#5, false, 1))
  let E := E.override byte.delta
  let compressed := E.insertEq (Reg.real32 8)
    (addStar .w32 (Term.V32 4) (Term.C32 3))
    |>.insertEq (Reg.real32 9) (Term.C32 value)
  let cStore ← stepEffects compressed (.C_SW (0#5, .Cregidx 0#3, .Cregidx 1#3))
  let cRead ← stepEffects (compressed.override cStore.delta)
    (.C_LW (0#5, .Cregidx 0#3, .Cregidx 1#3))
  some s!"\{\"first\":{effectJson first},\"store\":{effectJson store},\"reload\":{effectJson reload},\"byte\":{effectJson byte},\"compressedStore\":{effectJson cStore},\"compressedRead\":{effectJson cRead},\"state\":[{renderExprSetJson E}]}"

private def stackFields (value : Nat) : Option String := do
  let E := bindingEntry.insertEq (Reg.real32 13) (Term.C32 0x11223344)
  let whole ← stepEffects E (.STORE (0#12, .Regidx 13#5, sp, 4))
  let E := E.override whole.delta
    |>.insertEq (Reg.real32 12) (addStar .w32 (Term.V32 0) (Term.C32 1))
    |>.insertEq (Reg.real32 13) (Term.C32 value)
  let byte ← stepEffects E (.STORE (0#12, .Regidx 13#5, .Regidx 12#5, 1))
  let E := E.override byte.delta
  let read ← stepEffects E (.LOAD (0#12, .Regidx 12#5, .Regidx 14#5, true, 2))
  let crosses := (stepEffects E (.LOAD (3#12, sp, .Regidx 14#5, true, 2))).isNone
  some s!"\{\"whole\":{effectJson whole},\"byte\":{effectJson byte},\"read\":{effectJson read},\"crossesRejected\":{crosses}}"

private def rejectionChecks : String :=
  let E := bindingEntry.insertEq (Reg.real32 12) (Term.V32 4)
  let discarded := stepEffects E (.LOAD (0#12, .Regidx 12#5, zreg, true, 1))
  let unbound := E.insertEq (Reg.real32 12) (Term.V32 99)
  let symbolic := E.insertEq (Reg.real32 12)
    (addStar .w32 (Term.V32 4) (Term.V32 99))
  let badWidth := E.insertEq ⟨.packet, .w64, 0, none⟩ (Term.C64 0)
  let emptyCell : CellAccess := ⟨Reg.map64 1, 8, 8⟩
  let noInput : PacketAccess := ⟨0, 0, 1, .little, none, none⟩
  let concrete := bindingEntry.insertEq (Reg.real32 2) (Term.C32 0x3000)
    |>.insertEq (Reg.real32 12) (Term.C32 0x1003)
    |>.insertEq (Reg.ctx32 0) (Term.C32 0x1000)
    |>.insertEq (Reg.ctx32 1) (Term.C32 0x1040)
  let concreteRead := stepEffects concrete (.LOAD (0#12, .Regidx 12#5, .Regidx 14#5, true, 4))
  let independentInput : PacketAccess := ⟨1, 0, 1, .little, some (Term.C32 0x1000), none⟩
  let otherInput := { independentInput with κ := 2 }
  let checks := [
    ("unbound", (stepEffects unbound (.LOAD (0#12, .Regidx 12#5, zreg, true, 1))).isNone),
    ("symbolicOffset", (stepEffects symbolic (.LOAD (0#12, .Regidx 12#5, zreg, true, 1))).isNone),
    ("undefinedSource", (stepEffects E (.STORE (0#12, .Regidx 13#5, .Regidx 12#5, 1))).isNone),
    ("packet64", (stepEffects badWidth (.C_NOP 0#6)).isNone),
    ("bounds", (stepEffects E (.LOAD (63#12, .Regidx 12#5, zreg, true, 2))).isNone),
    ("invalidSize", (stepEffects E (.LOAD (0#12, .Regidx 12#5, zreg, true, 3))).isNone),
    ("partialWithoutOld", (emptyCell.write .empty (Term.C32 1)).isNone),
    ("readWithoutInput", (noInput.read .empty .w32 true).isNone),
    ("concretePacket", match concreteRead with
      | some effect => effect.inputs.entries.length == 4 && effect.updates.entries.length == 1
      | none => false),
    ("unknownConcreteStore", (stepEffects
      (concrete.insertEq (Reg.real32 12) (Term.C32 0x5000))
      (.STORE (0#12, zreg, .Regidx 12#5, 4))).isNone),
    ("independentInputs", match independentInput.read .empty .w32 true,
        otherInput.read .empty .w32 true with
      | some a, some b => a.value != b.value && (eval a.value).isNone
      | _, _ => false),
    ("discardedDestination", match discarded with
      | some effect => effect.updates.entries.isEmpty && effect.inputs.entries.length == 1
      | none => false)]
  let fields := String.intercalate "," (checks.map fun (name, passed) => s!"\"{name}\":{passed}")
  s!"\{{fields}}"

/-- Local register-effect probes for Rust unit tests; no graph, ELF or server involved. -/
@[export lean_rv32_register_effects]
def exportRegisterEffects (caseId value : UInt32) : String :=
  match caseId.toNat with
  | 0 => (packetOverlap value.toNat).getD "null"
  | 1 => (stackFields value.toNat).getD "null"
  | 2 => rejectionChecks
  | _ => "null"

end RV32
