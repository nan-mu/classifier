import RV32.Expr
import RV32.Initial
import Core.Render

namespace RV32
open Core

private def contextMem : Option Mem := do
  let fields := [Term.V32 4, addStar .w32 (Term.V32 4) (Term.C32 64),
    Term.C32 0, Term.C32 0, Term.C32 0, Term.C32 0]
  let mut mem : Mem := .empty
  for (t, j) in fields.zipIdx do
    let tile ← (Tile.ofTerm t 32).toOption
    mem ← (mem.write (.context j) 0 tile).toOption
  pure mem

private def bindingEntry : List Expr :=
  Expr.nil.insertEq (Reg.real32 2) (Term.V32 0)
    |>.insertEq (Reg.real32 10) (Term.V32 1)

private def effectJson (effect : ExprEffect) : String :=
  let writes := match Mem.empty.apply effect.writes with
    | .ok mem => renderMemJson mem
    | .error _ => ""
  s!"\{\"inputs\":[{renderExprsJson effect.inputs}],\"updates\":[{renderExprsJson effect.updates}],\"writes\":[{writes}]}"

private def stepMem (mem : Mem) (E : List Expr) (i : Insn) :
    Option (ExprEffect × Mem × List Expr) := do
  let effect ← stepEffects E i (mem := mem)
  let mem ← (mem.apply effect.writes).toOption
  some (effect, mem, E.override effect.delta)

private def packetOverlap (value : Nat) : Option String := do
  let mem ← contextMem
  let E := bindingEntry.insertEq (Reg.real32 12)
    (addStar .w32 (Term.V32 4) (Term.C32 3))
    |>.insertEq (Reg.real32 13) (Term.C32 value)
  let (first, mem, E) ← stepMem mem E (.LOAD (0#12, .Regidx 12#5, .Regidx 14#5, true, 4))
  let (store, mem, E) ← stepMem mem E (.STORE (2#12, .Regidx 13#5, .Regidx 12#5, 2))
  let (reload, mem, E) ← stepMem mem E (.LOAD (0#12, .Regidx 12#5, .Regidx 15#5, true, 4))
  let alias := E.insertEq (Reg.real32 16)
    (addStar .w32 (addStar .w32 (Term.V32 4) (Term.C32 1)) (Term.C32 4))
  let (byte, mem, E) ← stepMem mem alias (.LOAD (0#12, .Regidx 16#5, .Regidx 17#5, false, 1))
  let compressed := E.insertEq (Reg.real32 8)
    (addStar .w32 (Term.V32 4) (Term.C32 3))
    |>.insertEq (Reg.real32 9) (Term.C32 value)
  let (cStore, mem, compressedE) ← stepMem mem compressed (.C_SW (0#5, .Cregidx 0#3, .Cregidx 1#3))
  let (cRead, _, _) ← stepMem mem compressedE (.C_LW (0#5, .Cregidx 0#3, .Cregidx 1#3))
  some s!"\{\"first\":{effectJson first},\"store\":{effectJson store},\"reload\":{effectJson reload},\"byte\":{effectJson byte},\"compressedStore\":{effectJson cStore},\"compressedRead\":{effectJson cRead},\"state\":[{renderExprsJson E}]}"

private def stackFields (value : Nat) : Option String := do
  let mem ← contextMem
  let E := bindingEntry.insertEq (Reg.real32 13) (Term.C32 0x11223344)
  let (whole, mem, E) ← stepMem mem E (.STORE (0#12, .Regidx 13#5, sp, 4))
  let E := E.insertEq (Reg.real32 12) (addStar .w32 (Term.V32 0) (Term.C32 1))
    |>.insertEq (Reg.real32 13) (Term.C32 value)
  let (byte, mem, E) ← stepMem mem E (.STORE (0#12, .Regidx 13#5, .Regidx 12#5, 1))
  let (read, mem, _) ← stepMem mem E (.LOAD (0#12, sp, .Regidx 14#5, true, 4))
  let crosses := (stepEffects E (.LOAD (1#12, sp, .Regidx 14#5, true, 2)) (mem := mem)).isNone
  some s!"\{\"whole\":{effectJson whole},\"byte\":{effectJson byte},\"read\":{effectJson read},\"crossesRejected\":{crosses}}"

private def rejectionChecks : String := Id.run do
  let some mem := contextMem | return ""
  let E := bindingEntry.insertEq (Reg.real32 12) (Term.V32 4)
  let discarded := stepEffects E (.LOAD (0#12, .Regidx 12#5, zreg, true, 1)) (mem := mem)
  let unbound := E.insertEq (Reg.real32 12) (Term.V32 99)
  let symbolic := E.insertEq (Reg.real32 12)
    (addStar .w32 (Term.V32 4) (Term.V32 99))
  let badWidth := E.insertEq ⟨.packet, .w64, 0, none⟩ (Term.C64 0)
  let emptyCell : CellAccess := ⟨Reg.map64 1, 8, 8⟩
  let noInput : PacketAccess := ⟨0, 0, 1, .little, none, none⟩
  let concrete := bindingEntry.insertEq (Reg.real32 2) (Term.C32 0x3000)
    |>.insertEq (Reg.real32 12) (Term.C32 0x1003)
  let concreteMem := do
    let tile ← (Tile.ofTerm (Term.C32 0x1000) 32).toOption
    let mem ← (mem.write (.context 0) 0 tile).toOption
    let tile ← (Tile.ofTerm (Term.C32 0x1040) 32).toOption
    (mem.write (.context 1) 0 tile).toOption
  let concreteRead := concreteMem.bind fun mem =>
    stepEffects concrete (.LOAD (0#12, .Regidx 12#5, .Regidx 14#5, true, 4)) (mem := mem)
  let independentInput : PacketAccess := ⟨1, 0, 1, .little, some (Term.C32 0x1000), none⟩
  let otherInput := { independentInput with κ := 2 }
  let checks := [
    ("unbound", (stepEffects unbound (.LOAD (0#12, .Regidx 12#5, zreg, true, 1)) (mem := mem)).isNone),
    ("symbolicOffset", (stepEffects symbolic (.LOAD (0#12, .Regidx 12#5, zreg, true, 1)) (mem := mem)).isNone),
    ("undefinedSource", (stepEffects E (.STORE (0#12, .Regidx 13#5, .Regidx 12#5, 1)) (mem := mem)).isNone),
    ("packet64", (stepEffects badWidth (.C_NOP 0#6)).isNone),
    ("bounds", (stepEffects E (.LOAD (63#12, .Regidx 12#5, zreg, true, 2)) (mem := mem)).isNone),
    ("invalidSize", (stepEffects E (.LOAD (0#12, .Regidx 12#5, zreg, true, 3)) (mem := mem)).isNone),
    ("partialWithoutOld", (emptyCell.write Expr.nil (Term.C32 1)).isNone),
    ("readWithoutInput", (noInput.read Expr.nil .w32 true).isNone),
    ("concretePacket", match concreteRead with
      | some effect => effect.inputs.length == 4 && effect.writes.length == 4 &&
          effect.updates.length == 1
      | none => false),
    ("unknownConcreteStore", (concreteMem.bind fun mem =>
      stepEffects (concrete.insertEq (Reg.real32 12) (Term.C32 0x5000))
        (.STORE (0#12, zreg, .Regidx 12#5, 4)) (mem := mem)).isNone),
    ("independentInputs", match independentInput.read Expr.nil .w32 true,
        otherInput.read Expr.nil .w32 true with
      | some a, some b => a.value != b.value && (eval a.value).isNone
      | _, _ => false),
    ("discardedDestination", match discarded with
      | some effect => effect.updates.isEmpty && effect.inputs.length == 1 &&
          effect.writes.length == 1
      | none => false)]
  let fields := String.intercalate "," (checks.map fun (name, passed) => s!"\"{name}\":{passed}")
  return s!"\{{fields}}"

/-- Local register-effect probes for Rust unit tests; no graph, ELF or server involved. -/
@[export lean_rv32_register_effects]
def exportRegisterEffects (caseId value : UInt32) : String :=
  match caseId.toNat with
  | 0 => (packetOverlap value.toNat).getD "null"
  | 1 => (stackFields value.toNat).getD "null"
  | 2 => rejectionChecks
  | _ => "null"

end RV32
