import EBPF.Insn

namespace EBPF

private def binaryCode (code off : Nat) : Option BinaryOp :=
  match code, off with
  | 0, 0 => some .add
  | 1, 0 => some .sub
  | 2, 0 => some .mul
  | 3, 0 => some .div
  | 3, 1 => some .sdiv
  | 4, 0 => some .or
  | 5, 0 => some .and
  | 6, 0 => some .lsh
  | 7, 0 => some .rsh
  | 9, 0 => some .mod
  | 9, 1 => some .smod
  | 10, 0 => some .xor
  | 12, 0 => some .arsh
  | _, _ => none

private def jumpCode : Nat → Option JumpOp
  | 1 => some .jeq
  | 2 => some .jgt
  | 3 => some .jge
  | 4 => some .jset
  | 5 => some .jne
  | 6 => some .jsgt
  | 7 => some .jsge
  | 10 => some .jlt
  | 11 => some .jle
  | 12 => some .jslt
  | 13 => some .jsle
  | _ => none

private def atomicCode : Nat → Option AtomicOp
  | 0x00 => some (.add false)
  | 0x01 => some (.add true)
  | 0x40 => some (.or false)
  | 0x41 => some (.or true)
  | 0x50 => some (.and false)
  | 0x51 => some (.and true)
  | 0xa0 => some (.xor false)
  | 0xa1 => some (.xor true)
  | 0xe1 => some .xchg
  | 0xf1 => some .cmpxchg
  | _ => none

/-- Decode one little-endian 8-byte slot. LDDW's upper half is joined only by
`decodeProgram`; its reserved second slot is never an independent instruction. -/
def decodeInsnWord (word : UInt64) : Insn :=
  let n := word.toNat
  let opcode := n % 256
  let cls := opcode % 8
  let code := opcode / 16
  let dst := (n >>> 8) % 16
  let src := (n >>> 12) % 16
  let offBits := (n >>> 16) % 65536
  let offset := ClassifierExpr.s 16 offBits
  let imm := UInt32.ofNat (n >>> 32)
  let registerSource := opcode % 16 ≥ 8
  let operand := if registerSource then Source.reg src else .imm imm
  let sourceValid := if registerSource then src ≤ 10 && imm == 0 else src == 0
  let bytes := match (opcode / 8) % 4 with | 0 => 4 | 1 => 2 | 2 => 1 | _ => 8
  if opcode == 0x95 then
    if n == 0x95 then .exit else .illegal word
  else if cls == 1 && (opcode / 32 == 3 || opcode / 32 == 4) then
    if dst ≤ 9 && src ≤ 10 && imm == 0 then
      if opcode / 32 == 3 then .ldx bytes dst src offset
      else if bytes != 8 then .memsx bytes dst src offset else .illegal word
    else .illegal word
  else if cls == 2 && opcode / 32 == 3 then
    if dst ≤ 10 && src == 0 then .st bytes dst imm offset else .illegal word
  else if cls == 3 && opcode / 32 == 3 then
    if dst ≤ 10 && src ≤ 10 && imm == 0 then .stx bytes dst src offset
    else .illegal word
  else if cls == 3 && opcode / 32 == 6 then
    -- LLVM commit 17bfc00f7c4a424d7b5dc6da575865833701fd1a,
    -- llvm/lib/Target/BPF/BPFInstrInfo.td and assembler-disassembler-v4.s.
    -- LOAD_ACQ is imm 0x100, STORE_REL is imm 0x110, both use STX ATOMIC.
    if imm == 0x100 then
      if dst ≤ 9 && src ≤ 10 then .loadAcq bytes dst src offset else .illegal word
    else if imm == 0x110 then
      if dst ≤ 10 && src ≤ 10 then .storeRel bytes dst src offset else .illegal word
    else if bytes == 4 || bytes == 8 then
      match atomicCode imm.toNat with
      | some op =>
        if dst ≤ 10 && src ≤ 10 && (!op.returnsSource || src ≤ 9) then
          .atomic (if bytes == 4 then .w32 else .w64) op dst src offset
        else .illegal word
      | none => .illegal word
    else .illegal word
  else if (cls == 5 || cls == 6) && (jumpCode code).isSome then
    match jumpCode code with
    | some op =>
      if dst ≤ 10 && sourceValid then
        .jcond (if cls == 6 then .w32 else .w64) op dst operand offset
      else .illegal word
    | none => .illegal word
  else if opcode == 0x05 then
    if dst == 0 && src == 0 && imm == 0 then .ja offset else .illegal word
  else if opcode == 0x06 then
    if dst == 0 && src == 0 && offBits == 0 then
      .ja (ClassifierExpr.s 32 imm.toNat)
    else .illegal word
  else if opcode == 0x18 then
    if dst ≤ 9 && offBits == 0 && src ≤ 6 then
      .lddw dst (UInt8.ofNat src) (UInt64.ofNat imm.toNat)
    else .illegal word
  else if opcode == 0x85 then
    if dst == 0 && src == 0 && offBits == 0 then .callHelper imm else .illegal word
  else if cls == 4 || cls == 7 then
    let width := if cls == 4 then ClassifierExpr.Width.w32 else .w64
    if dst ≥ 10 then .illegal word
    else if code == 13 then
      if src == 0 && offBits == 0 && [16, 32, 64].contains imm.toNat &&
          (cls == 4 || !registerSource) then
        .endian (if cls == 7 then .swap else if registerSource then .big else .little)
          imm.toNat dst
      else .illegal word
    else if code == 8 then
      if !registerSource && src == 0 && offBits == 0 && imm == 0 then .neg width dst
      else .illegal word
    else if code == 11 then
      if !sourceValid then .illegal word
      else if offBits == 0 then .mov width dst operand
      else if registerSource && ([8, 16].contains offBits || (cls == 7 && offBits == 32)) then
        .movsx width offBits dst src
      else .illegal word
    else if !sourceValid then .illegal word
    else match binaryCode code offBits with
      | some op =>
        if !registerSource && [.lsh, .rsh, .arsh].contains op &&
            imm.toNat ≥ width.bits then .illegal word
        else .binary width op dst operand
      | none => .illegal word
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

#guard decodeInsnWord 0x0000000300000114 == .binary .w32 .sub 1 (.imm 3)
#guard decodeInsnWord 0x000000000001213f == .binary .w64 .sdiv 1 (.reg 2)
#guard decodeInsnWord 0x000000000001219c == .binary .w32 .smod 1 (.reg 2)
#guard decodeInsnWord 0x00000000000821bc == .movsx .w32 8 1 2
#guard decodeInsnWord 0x00000000002021bf == .movsx .w64 32 1 2
#guard decodeInsnWord 0x00000040000001d4 == .endian .little 64 1
#guard decodeInsnWord 0x00000010000001dc == .endian .big 16 1
#guard decodeInsnWord 0x00000020000001d7 == .endian .swap 32 1
#guard decodeInsnWord 0x000000000000a191 == .memsx 1 1 10 0
#guard decodeInsnWord 0xfffffffffff80a7a == .st 8 10 0xffffffff (-8)
#guard decodeInsnWord 0x00000100000010d3 == .loadAcq 1 0 1 0
#guard decodeInsnWord 0x00000110000021cb == .storeRel 2 1 2 0
#guard decodeInsnWord 0x00000001fff81adb == .atomic .w64 (.add true) 10 1 (-8)
#guard decodeInsnWord 0x000000f1fffc1ac3 == .atomic .w32 .cmpxchg 10 1 (-4)
#guard [0x00000000002021bc, 0x00000000000801b4, 0x000000000000018c,
    0x00000040000001df, 0x000000000000a199, 0x000000e000001ac3,
    0x000000f000001adb, 0x000000010000aaC3, 0x00000101000010c3].all (fun word =>
  match decodeInsnWord word with
  | .illegal _ => true
  | _ => false)

end EBPF
