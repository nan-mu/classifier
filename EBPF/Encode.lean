import EBPF.Insn

namespace EBPF

/-- Decode one little-endian 8-byte slot, represented as a UInt64.
Reserved fields and register numbers are checked; unsupported opcodes reject. -/
def decodeInsnWord (word : UInt64) : Insn :=
  let n := word.toNat
  let opcode := n % 256
  let dst := (n >>> 8) % 16
  let src := (n >>> 12) % 16
  let offset := (n >>> 16) % 65536
  let imm := UInt32.ofNat (n >>> 32)
  if opcode == 0x95 then
    if n == 0x95 then .exit else .illegal word
  else
    let width := if opcode % 8 == 4 then ClassifierExpr.Width.w32 else .w64
    let registerSource := opcode % 16 ≥ 8
    let operand := if registerSource then Source.reg src else .imm imm
    if dst ≥ 10 || offset != 0 ||
        (if registerSource then src > 10 || imm != 0 else src != 0) then .illegal word
    else if [0xb4, 0xb7, 0xbc, 0xbf].contains opcode then .mov width dst operand
    else if [0x04, 0x07, 0x0c, 0x0f].contains opcode then .add width dst operand
    else .illegal word

def decodeProgram (words : Array UInt64) : Array Insn := words.map decodeInsnWord

end EBPF
