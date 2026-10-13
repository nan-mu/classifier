import EBPF.Insn

namespace EBPF

/-- Decode one little-endian 8-byte slot. LDDW's upper half is joined only by
`decodeProgram`; its reserved second slot is never an independent instruction. -/
def decodeInsnWord (word : UInt64) : Insn :=
  let n := word.toNat
  let opcode := n % 256
  let dst := (n >>> 8) % 16
  let src := (n >>> 12) % 16
  let offBits := (n >>> 16) % 65536
  let offset := ClassifierExpr.s 16 offBits
  let imm := UInt32.ofNat (n >>> 32)
  let registerSource := opcode % 16 ≥ 8
  let operand := if registerSource then Source.reg src else .imm imm
  let sourceValid := if registerSource then src ≤ 10 && imm == 0 else src == 0
  if opcode == 0x95 then
    if n == 0x95 then .exit else .illegal word
  else if [0x71, 0x69, 0x61, 0x79].contains opcode then
    let bytes := if opcode == 0x71 then 1 else if opcode == 0x69 then 2
      else if opcode == 0x61 then 4 else 8
    if dst ≤ 9 && src ≤ 10 && imm == 0 then .ldx bytes dst src offset
    else .illegal word
  else if [0x73, 0x6b, 0x63, 0x7b].contains opcode then
    let bytes := if opcode == 0x73 then 1 else if opcode == 0x6b then 2
      else if opcode == 0x63 then 4 else 8
    if dst ≤ 10 && src ≤ 10 && imm == 0 then .stx bytes dst src offset
    else .illegal word
  else if [0x15, 0x1d, 0x16, 0x1e, 0x55, 0x5d, 0x56, 0x5e,
      0x25, 0x2d, 0x26, 0x2e].contains opcode then
    let width := if opcode % 8 == 6 then ClassifierExpr.Width.w32 else .w64
    let op := if opcode / 16 == 1 then JumpOp.jeq
      else if opcode / 16 == 5 then .jne else .jgt
    if dst ≤ 9 && sourceValid then .jcond width op dst operand offset
    else .illegal word
  else if opcode == 0x05 then
    if dst == 0 && src == 0 && imm == 0 then .ja offset else .illegal word
  else if opcode == 0x18 then
    if dst ≤ 9 && offBits == 0 then .lddw dst (UInt8.ofNat src) (UInt64.ofNat imm.toNat)
    else .illegal word
  else if opcode == 0x85 then
    if dst == 0 && src == 0 && offBits == 0 then .callHelper imm else .illegal word
  else
    let width := if opcode % 8 == 4 then ClassifierExpr.Width.w32 else .w64
    if dst ≥ 10 || offBits != 0 || !sourceValid then .illegal word
    else if [0xb4, 0xb7, 0xbc, 0xbf].contains opcode then .mov width dst operand
    else if [0x04, 0x07, 0x0c, 0x0f].contains opcode then .add width dst operand
    else .illegal word

/-- One result per raw slot, including LDDW continuation slots and malformed pairs. -/
def decodeProgram (words : Array UInt64) : Array Insn := Id.run do
  let mut result := words.map decodeInsnWord
  let mut j := 0
  while j < words.size do
    match result[j]? with
    | some (.lddw dst srcType low) =>
      match words[j + 1]? with
      | some upper =>
        if upper.toNat % (1 <<< 32) == 0 then
          result := result.set! j (.lddw dst srcType
            (UInt64.ofNat (low.toNat + (upper.toNat >>> 32) * (1 <<< 32))))
          result := result.set! (j + 1) .continuation
          j := j + 2
        else
          result := result.set! j (.illegal words[j]!)
          j := j + 1
      | none =>
        result := result.set! j (.illegal words[j]!)
        j := j + 1
    | _ => j := j + 1
  return result

#guard decodeProgram #[0x5566778800000118, 0x1122334400000000, 0x95] ==
  #[.lddw 1 0 0x1122334455667788, .continuation, .exit]
#guard decodeInsnWord 0x00000000fffc1a63 == .stx 4 10 1 (-4)
#guard decodeInsnWord 0x00000007fffe0115 == .jcond .w64 .jeq 1 (.imm 7) (-2)
#guard decodeInsnWord 0x00000000ffffa12e == .jcond .w32 .jgt 1 (.reg 10) (-1)
#guard decodeInsnWord 0x0000000300010256 == .jcond .w32 .jne 2 (.imm 3) 1
#guard match decodeProgram #[0x0000000100000018] with
  | #[.illegal _] => true
  | _ => false
#guard decodeInsnWord 0x00000000fffcA161 == .ldx 4 1 10 (-4)
#guard decodeInsnWord 0x00000000ffff0005 == .ja (-1)
#guard decodeInsnWord 0x0000000100000085 == .callHelper 1
#guard [0x0000000000000a61, 0x000000000000b173,
    0x0000000000001115, 0x000000010000111d].all (fun word =>
  match decodeInsnWord word with
  | .illegal _ => true
  | _ => false)
#guard match decodeProgram #[0x0000000100000018, 0x0000000200000095] with
  | #[.illegal _, .illegal _] => true
  | _ => false

end EBPF
