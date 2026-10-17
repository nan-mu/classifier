import EBPF.Memory
import RV32.Expand
import Core.Cross.UnifyProofs

namespace CrossArch.CompoundPacketFixture
open Core
open EBPF

private def data : Term := Term.V32 4
private def ending : Term := addStar .w32 data (Term.C32 128)
private def byte : Term := Term.V32 8

/-- Both carriers encode Ethernet + (((IPv4 IHL byte - 2) mod 16) << 2).
The subtraction stays under the projection so solving the outer address keeps it. -/
private def ihl (w : Width) : Term :=
  let reduced := Term.app .w32 (.sub .w32) [byte, Term.C32 2]
  addStar w (Term.C w 14)
    (shlStar w (zStar 4 w 32 reduced) (Term.C w 2))

private def rvAddress : Term := addStar .w32 data (ihl .w32)
private def rvBase : ExprSet :=
  let fields := [data, ending, Term.C32 0, Term.C32 0, Term.C32 0, Term.C32 0]
  let E := fields.zipIdx.foldl (fun E (t, j) => E.insertEq (Reg.ctx32 j) t) ExprSet.empty
  E.insertEq (Reg.packet 0 0) byte
    |>.insertEq (Reg.real32 12) rvAddress
    |>.insertEq (Reg.real32 13) (addStar .w32 rvAddress (Term.C32 1))

private def rvChecked : ExprSet :=
  rvBase.insertConstraint ⟨Reg.real32 13, .leu, ending⟩

private def params : EntryParams :=
  ⟨Term.V64 1, Term.V64 0, data, 128, 0, 0, 0⟩

private def ebBase : Option (ExprSet × Term × Term) := do
  let initial ← (buildE0 params).toOption
  let E := initial.exprs.insertEq (Reg.packet 0 0) byte
  let root ← packetRoot params E
  let address := addStar .w64 root (ihl .w64)
  let endTerm ← (CellAccess.mk (Reg.ctx32 1) 0 32).read E .w64 true
  pure (E.insertEq (Reg.real64 2) address
    |>.insertEq (Reg.real64 3) (addStar .w64 address (Term.C64 1)), address, endTerm)

private def accesses : Option (PacketAccess × PacketAccess × ExprSet) := do
  let r ← RV32.packetBindingAt rvChecked rvAddress 0 1
  let (base, address, endTerm) ← ebBase
  let E := base.insertConstraint ⟨Reg.real64 3, .leu, endTerm⟩
  let .packet e ← (resolveAddress params E address 0 1).toOption | none
  pure (r, e, E)

/- Positive binding, equal nonempty compound registers, equal normalized raw-wire
return keys, and canonical JSON parsing. These are finite fixtures, not CP-End. -/
#guard Id.run do
  let some (r, e, E) := accesses | return false
  let some rp := r.compound | return false
  let some ep := e.compound | return false
  let expected : CompoundPacketReg :=
    ⟨0, .add (.shl (.zext 4 32 (.sub (.packet (Reg.packet 0 0).alpha) 2)) (.c 2)) (.c 14),
      1, 1, false, 0,
      .add (.shl (.zext 4 32 (.sub (.packet (Reg.packet 0 0).alpha) 2)) (.c 2)) (.c 15)⟩
  if rp != expected || ep != expected || r.byteReg 0 != e.byteReg 0 then return false
  if (r.byteReg 0).toCross != (e.byteReg 0).toCross then return false
  let some rr := r.read rvChecked .w32 true | return false
  let some er := e.read E .w64 true | return false
  let rk := exportCrossPredNormalize "{}" (renderPredicateJson (.ret rr.value))
  let ek := exportCrossPredNormalize "{}" (renderPredicateJson (.ret er.value))
  if rk == "null" || rk != ek || toCrossTerm rr.value != toCrossTerm er.value then return false
  let some parsed := (Lean.Json.parse rk).toOption >>= parseCrossPredJson | return false
  return parsed == toCross {} (.ret rr.value) &&
    parseReg (renderReg (r.byteReg 0)) == some (r.byteReg 0)

/- Neither ISA may infer a symbolic access merely from the offset format. -/
#guard Id.run do
  if (RV32.packetBindingAt rvBase rvAddress 0 1).isSome then return false
  let some (E, address, _) := ebBase | return false
  return (resolveAddress params E address 0 1).toOption.isNone

/- An unrelated free register is not a packet byte, even with the same check. -/
#guard Id.run do
  let address := addStar .w32 data (addStar .w32 (Term.C32 14) (Term.V32 99))
  let E := rvBase.insertEq (Reg.real32 13) (addStar .w32 address (Term.C32 1))
    |>.insertConstraint ⟨Reg.real32 13, .leu, ending⟩
  if (RV32.packetBindingAt E address 0 1).isSome then return false
  let some (base, _, endTerm) := ebBase | return false
  let some root := packetRoot params base | return false
  let address := addStar .w64 root (addStar .w64 (Term.C64 14) (Term.V64 99))
  let E := base.insertEq (Reg.real64 3) (addStar .w64 address (Term.C64 1))
    |>.insertConstraint ⟨Reg.real64 3, .leu, endTerm⟩
  return (resolveAddress params E address 0 1).toOption.isNone

/- A changed witness or access width changes the compare key. -/
#guard Id.run do
  let some (r, _, _) := accesses | return false
  let some p := r.compound | return false
  return p.toCross != ({ p with endCtx := 7 } : CompoundPacketReg).toCross &&
    p.toCross != ({ p with strict := true } : CompoundPacketReg).toCross &&
    p.toCross != ({ p with bytes := 2 } : CompoundPacketReg).toCross

/- Product store generation preserves the compound destination in both Expr
updates and PacketWrite JSON, rather than misreporting it as constant offset 0. -/
#guard Id.run do
  let some (r, e, E) := accesses | return false
  let rvE := rvChecked.insertEq (Reg.real32 11) (Term.C32 123)
  let program := #[RV32.Insn.STORE (0#12, .Regidx 11#5, .Regidx 12#5, 1),
    RV32.decodeInsnWord 0x0001]
  let .candidates [candidate] := RV32.inferStep program {} 77 0 ⟨rvE, []⟩ | return false
  let .ok (effect, [ep]) := EBPF.exprEffects params 88 E (.st 1 2 123 0) | return false
  let [rp] := candidate.P_k | return false
  if candidate.E_k.lookupEq (r.byteReg 0) != effect.updates.lookupEq (e.byteReg 0) then
    return false
  let rk := exportCrossPredNormalize "{}" (renderPredicateJson rp)
  let ek := exportCrossPredNormalize "{}" (renderPredicateJson ep)
  if rk == "null" || rk != ek then return false
  let some parsed := (Lean.Json.parse rk).toOption >>= parseCrossPredJson | return false
  let some p := r.compound | return false
  let mismatch := Predicate.packetWrite 77 p.κ 0 16 (Term.C32 123) (some p)
  return rp.storeBytes? == some 1 && ep.storeBytes? == some 1 &&
    parsed == toCross {} rp &&
    parsed == toCross { storeBytes := some 8 } rp &&
    !predicateWellFormed mismatch &&
    exportCrossPredNormalize "{}" (renderPredicateJson mismatch) == "null" &&
    (Predicate.packetWrite 77 p.κ 0 32 (Term.C32 123) (some p)).storeBytes? == some p.bytes

/- The low-mask machine idiom is parsed as low, not admitted as arbitrary and. -/
#guard packetOffsetFrom rvBase (andStar 32 .w32 byte (Term.C32 15)) ==
  packetOffsetFrom rvBase (star .w32 (.low 4 32) [byte])

/- An offset product and subtraction by a nonconstant packet term stay outside
the address format, even with a passed check on that exact address. -/
#guard Id.run do
  let some (base, _, endTerm) := ebBase | return false
  let some root := packetRoot params base | return false
  for op in [Op.mullo, Op.sub] do
    let offset32 := Term.app .w32 (op .w32) [byte, star .w32 (.low 4 32) [byte]]
    let address32 := addStar .w32 data offset32
    let R := rvBase.insertEq (Reg.real32 13) (addStar .w32 address32 (Term.C32 1))
      |>.insertConstraint ⟨Reg.real32 13, .leu, ending⟩
    if (packetOffsetFrom rvBase offset32).isSome then return false
    if (RV32.packetBindingAt R address32 0 1).isSome then return false
    let wideByte := zStar 32 .w64 32 byte
    let offset64 := Term.app .w64 (op .w64) [wideByte, star .w64 (.low 4 64) [wideByte]]
    let address64 := addStar .w64 root offset64
    let E := base.insertEq (Reg.real64 3) (addStar .w64 address64 (Term.C64 1))
      |>.insertConstraint ⟨Reg.real64 3, .leu, endTerm⟩
    if (packetOffsetFrom base offset64).isSome then return false
    if (resolveAddress params E address64 0 1).toOption.isSome then return false
  return true

/- Wrapper identities are erased; value-changing projections keep their input
width, and metadata/rendering preserves all four added constructors. -/
#guard Id.run do
  let p := PacketOffset.packet (Reg.packet 0 0).alpha
  if packetOffsetFrom rvBase (idStar .w32 byte) != some p then return false
  if packetOffsetFrom rvBase (zStar 32 .w64 32 byte) != some p then return false
  if packetOffsetFrom rvBase (sStar 32 .w32 32 byte) != some p then return false
  if packetOffsetFrom rvBase (zStar 4 .w32 32 byte) != some (.zext 4 32 p) then return false
  if packetOffsetFrom rvBase (sStar 4 .w64 32 byte) != some (.sext 4 32 p) then return false
  let t := PacketOffset.id (.sext 4 32 (.zext 4 64 (.sub p 2)))
  let r := Reg.compoundPacket ⟨0, t, 1, 1, false, 0, .add t (.c 1)⟩
  if parseReg (renderReg r) != some r then return false
  return (PacketOffset.sub (.c 1) 2).toCross ==
      CrossTerm.c (-1) &&
    (PacketOffset.sub (.c 1) 2).value (fun _ => 0) == 2^32 - 1 &&
    (PacketOffset.sext 4 32 (.c 15)).value (fun _ => 0) == 2^32 - 1

/- A passed eight-byte check covers all four admitted access sizes; both keys
retain that actual wider check. A one-byte check cannot authorize two bytes. -/
#guard Id.run do
  let some (base, address, endTerm) := ebBase | return false
  let R := rvBase.insertEq (Reg.real32 13) (addStar .w32 rvAddress (Term.C32 8))
    |>.insertConstraint ⟨Reg.real32 13, .leu, ending⟩
  let E := base.insertEq (Reg.real64 3) (addStar .w64 address (Term.C64 8))
    |>.insertConstraint ⟨Reg.real64 3, .leu, endTerm⟩
  for bytes in [1, 2, 4, 8] do
    let some r := RV32.packetBindingAt R rvAddress 0 bytes | return false
    let .ok (.packet e) := resolveAddress params E address 0 bytes | return false
    if r.compound.isNone || r.byteReg 0 != e.byteReg 0 then return false
    if (r.byteReg 0).toCross != (e.byteReg 0).toCross then return false
  if (RV32.packetBindingAt rvChecked rvAddress 0 2).isSome then return false
  let narrow := base.insertConstraint ⟨Reg.real64 3, .leu, endTerm⟩
  return (resolveAddress params narrow address 0 2).toOption.isNone

end CrossArch.CompoundPacketFixture
