import EBPF.Memory
import RV32.Expand
import Node.Path

namespace CrossArch.CompoundPacketFixture
open Core Node

/- Symbolic packet addresses do not become packet registers.
A constant byte store is one `Packet([8*o, 8*o+8))` equality plus one packetWrite. -/

private def byte : Term := star .w32 (.low 8 32) [Term.V32 8]

#guard packetOffsetFrom Expr.nil (Term.C32 14) == some (.c 14)

#guard Id.run do
  let some E := writeInterval Expr.nil (.packet 0 8) byte | return false
  packetOffsetFrom E byte == some (.packet 0) &&
    packetOffsetFrom E (idStar .w32 byte) == some (.packet 0) &&
    (packetOffsetFrom E (Term.app .w32 (.mullo .w32) [byte, byte])).isNone

#guard Id.run do
  let p := { RV32.smokeEntryParams with tData := Term.C32 0x1000, tLen := Term.C32 16 }
  let .ok σ := RV32.buildE0 p | return false
  let E := σ.exprs.insertEq (Reg.real32 12) p.tData
    |>.insertEq (Reg.real32 11) (Term.C32 0x44)
  let program := #[RV32.Insn.STORE (0#12, .Regidx 11#5, .Regidx 12#5, 1),
    RV32.decodeInsnWord 0x0001]
  let .candidates [c] := RV32.inferStep program 77 0 ⟨E, []⟩ | return false
  let symbolic := E.insertEq (Reg.real32 12) (addStar .w32 p.tData (Term.V32 9))
  let symbolicStep := RV32.inferStep program 78 0 ⟨symbolic, []⟩
  let noPacket (c : Candidate) :=
    c.P_k.isEmpty && !(c.E_k.any fun e => match e.reg with | .packet .. => true | _ => false)
  c.P_k == [.packetWrite 77 0 8 (Term.C32 0x44)] &&
    (c.E_k.lookupEq (.packet 0 8)).isSome &&
    match symbolicStep with
    | .candidates cs => !cs.isEmpty && cs.all noPacket
    | .reject .undefinedSrc => true
    | _ => false

#guard Id.run do
  let params : EBPF.EntryParams := ⟨Term.V64 1, Term.V64 0, Term.C32 0x1000, 16⟩
  let .ok initial := EBPF.buildE0 params | return false
  let E := EBPF.host params (initial.exprs.insertEq (Reg.real64 2) (Term.C64 0x1000))
  let .ok (effect, preds) := EBPF.exprEffects 88 E (.st 1 2 0x44 0) | return false
  preds == [.packetWrite 88 0 8 (Term.C64 0x44)] &&
    (effect.updates.any fun e => match e.reg with | .packet 0 8 => true | _ => false)

end CrossArch.CompoundPacketFixture
