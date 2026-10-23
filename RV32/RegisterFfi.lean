import RV32.Expr
import Core.Update
import RV32.Initial
import Core.Render

namespace RV32
open Core

private def contextState : Option (List Expr) := do
  let fields := [Term.V32 4, addStar .w32 (Term.V32 4) (Term.C32 64),
    Term.C32 0, Term.C32 0, Term.C32 0, Term.C32 0]
  let mut E := (update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve (Term.V32 0))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 10) (solve (Term.V32 1))], predicates := [] }).exprs)
  for (j, t) in xdpFields.zip fields do
    E ← putContext E j t
  pure E

private def effectJson (effect : ExprEffect) : String :=
  s!"\{\"inputs\":[{renderExprsJson effect.inputs}],\"updates\":[{renderExprsJson effect.updates}]}"

private def stepState (E : List Expr) (i : Insn) : Option (ExprEffect × List Expr) := do
  let effect ← stepEffects E i
  some (effect, (update ⟨E, []⟩ { exprs := effect.delta, predicates := [] }).exprs)

private def packetOverlap (value : Nat) : Option String := do
  let E ← contextState
  let E := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve (addStar .w32 (Term.V32 4) (Term.C32 3)))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 13) (solve (Term.C32 value))], predicates := [] }).exprs)
  let (first, E) ← stepState E (.LOAD (0#12, .Regidx 12#5, .Regidx 14#5, true, 4))
  let (store, E) ← stepState E (.STORE (2#12, .Regidx 13#5, .Regidx 12#5, 2))
  let (reload, E) ← stepState E (.LOAD (0#12, .Regidx 12#5, .Regidx 15#5, true, 4))
  let alias := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 16) (solve (addStar .w32 (addStar .w32 (Term.V32 4) (Term.C32 1)) (Term.C32 4)))], predicates := [] }).exprs
  let (byte, E) ← stepState alias (.LOAD (0#12, .Regidx 16#5, .Regidx 17#5, false, 1))
  let compressed := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 8) (solve (addStar .w32 (Term.V32 4) (Term.C32 3)))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 9) (solve (Term.C32 value))], predicates := [] }).exprs)
  let (cStore, compressedE) ← stepState compressed (.C_SW (0#5, .Cregidx 0#3, .Cregidx 1#3))
  let (cRead, _) ← stepState compressedE (.C_LW (0#5, .Cregidx 0#3, .Cregidx 1#3))
  some s!"\{\"first\":{effectJson first},\"store\":{effectJson store},\"reload\":{effectJson reload},\"byte\":{effectJson byte},\"compressedStore\":{effectJson cStore},\"compressedRead\":{effectJson cRead},\"state\":[{renderExprsJson E}]}"

private def stackFields (value : Nat) : Option String := do
  let E ← contextState
  let E := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 13) (solve (Term.C32 0x11223344))], predicates := [] }).exprs
  let (whole, E) ← stepState E (.STORE (0#12, .Regidx 13#5, sp, 4))
  let E := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve (addStar .w32 (Term.V32 0) (Term.C32 1)))], predicates := [] }).exprs
    |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 13) (solve (Term.C32 value))], predicates := [] }).exprs)
  let (byte, E) ← stepState E (.STORE (0#12, .Regidx 13#5, .Regidx 12#5, 1))
  let (read, E) ← stepState E (.LOAD (0#12, sp, .Regidx 14#5, true, 4))
  let crosses := (stepEffects E (.LOAD (1#12, sp, .Regidx 14#5, true, 2))).isNone
  some s!"\{\"whole\":{effectJson whole},\"byte\":{effectJson byte},\"read\":{effectJson read},\"crossesRejected\":{crosses}}"

private def rejectionChecks : String := Id.run do
  let some E := contextState | return ""
  let E := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve (Term.V32 4))], predicates := [] }).exprs
  let discarded := stepEffects E (.LOAD (0#12, .Regidx 12#5, zreg, true, 1))
  let unbound := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve (Term.V32 99))], predicates := [] }).exprs
  let symbolic := (update ⟨E, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve (addStar .w32 (Term.V32 4) (Term.V32 99)))], predicates := [] }).exprs
  let badWidth := (update ⟨E, []⟩ { exprs := [Expr.mkEq (.packet 0 64) (solve (Term.C32 0))], predicates := [] }).exprs
  let emptyCell : CellAccess := ⟨.map 1 [] 0 8⟩
  let noInput : PacketAccess := { displacement := .c 0, bytes := 1 }
  let concreteData := Term.C32 0x1000
  let some concrete := putContext ((update ⟨Expr.nil, []⟩ { exprs := [Expr.mkEq (Reg.real32 2) (solve (Term.C32 0x3000))], predicates := [] }).exprs
      |> (fun acc => (update ⟨acc, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve (Term.C32 0x1003))], predicates := [] }).exprs)) .data concreteData | return ""
  let some concrete := putContext concrete .dataEnd (Term.C32 0x1040) | return ""
  let some concrete := putContext concrete .dataMeta (Term.C32 0) | return ""
  let some concrete := putContext concrete .ingressIfindex (Term.C32 0) | return ""
  let some concrete := putContext concrete .rxQueueIndex (Term.C32 0) | return ""
  let some concrete := putContext concrete .egressIfindex (Term.C32 0) | return ""
  let concreteRead := stepEffects concrete (.LOAD (0#12, .Regidx 12#5, .Regidx 14#5, true, 4))
  let independentInput : PacketAccess :=
    { displacement := .c 0, bytes := 1, inputBase := some (Term.C32 0x1000) }
  let otherInput := { independentInput with inputBase := some (Term.C32 0x2000) }
  let checks := [
    ("unbound", (stepEffects unbound (.LOAD (0#12, .Regidx 12#5, zreg, true, 1))).isNone),
    ("symbolicOffset", (stepEffects symbolic (.LOAD (0#12, .Regidx 12#5, zreg, true, 1))).isNone),
    ("undefinedSource", (stepEffects E (.STORE (0#12, .Regidx 13#5, .Regidx 12#5, 1))).isNone),
    ("packet64", (stepEffects badWidth (.C_NOP 0#6)).isNone),
    ("bounds", (stepEffects E (.LOAD (63#12, .Regidx 12#5, zreg, true, 2))).isNone),
    ("invalidSize", (stepEffects E (.LOAD (0#12, .Regidx 12#5, zreg, true, 3))).isNone),
    ("partialWithoutOld", match emptyCell.write Expr.nil (Term.C32 1) with
      | some rows => (rows.lookupEq (.map 1 [] 0 8)).isSome
      | none => false),
    ("readWithoutInput", (noInput.read Expr.nil .w32 true).isNone),
    ("concretePacket", match concreteRead with
      | some effect => effect.inputs.length == 4 && effect.updates.length == 1
      | none => false),
    ("unknownConcreteStore", (stepEffects ((update ⟨concrete, []⟩ { exprs := [Expr.mkEq (Reg.real32 12) (solve (Term.C32 0x5000))], predicates := [] }).exprs)
        (.STORE (0#12, zreg, .Regidx 12#5, 4))).isNone),
    ("independentInputs", match independentInput.read Expr.nil .w32 true,
        otherInput.read Expr.nil .w32 true with
      | some a, some b => a.value != b.value && (eval a.value).isNone
      | _, _ => false),
    ("discardedDestination", match discarded with
      | some effect => effect.updates.isEmpty && effect.inputs.length == 1
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
