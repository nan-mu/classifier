import EBPF.Expand
import RV32IMC.Expand
import ClassifierExpr.ObservationEq

open ClassifierExpr PathMerge
open Lean (Json)

namespace SemanticCheck

private def expect [BEq α] [Repr α] (name : String) (actual expected : α) : Except String Unit :=
  if actual == expected then pure ()
  else throw s!"{name}\n  expected: {reprStr expected}\n  actual:   {reprStr actual}"

private def expectJson (name : String) (actual expected : Json) : Except String Unit :=
  if actual == expected then pure ()
  else throw s!"{name}\n  expected: {expected.compress}\n  actual:   {actual.compress}"

private def liftResult [Repr ε] (name : String) (value : Except ε α) : Except String α :=
  value.mapError fun e => s!"{name}: expected success, actual {reprStr e}"

private def one (name : String) : StepResult → Except String Candidate
  | .candidates [c] => pure c
  | actual => throw s!"{name}: expected exactly one candidate, actual {reprStr actual}"

private def reject (name : String) (actual : StepResult) (expected : RejectReason) : Except String Unit :=
  match actual with
  | .reject reason => expect name reason expected
  | _ => throw s!"{name}: expected reject {reprStr expected}, actual {reprStr actual}"

private def raw (opcode dst src : Nat) (off : Int := 0) (imm : Nat := 0) : UInt64 :=
  UInt64.ofNat (opcode + 256 * dst + 4096 * src + 65536 * M 16 off + 4294967296 * imm)

private def entry : EBPF.EntryParams :=
  ⟨Term.V64 1, Term.V64 0, Term.V32 2, 64, 0, 0, 0⟩

private def context : EBPF.StepContext := { entry := entry }

private def ebpf (words : Array UInt64) (E : ExprSet) (ctx : EBPF.StepContext := context)
    (j : Nat := 0) : StepResult :=
  EBPF.ebpfStep (EBPF.decodeProgram words) ctx 70 j ⟨E, []⟩

private def ebpfValue (name : String) (word : UInt64) (E : ExprSet)
    (r expected : Nat) : Except String Unit := do
  let c ← one name (ebpf #[word, 0x95] E)
  let σ ← liftResult name (applyLocal ⟨E, []⟩ c.E_k c.P_k)
  expect (name ++ " successor") (c.dir, c.loc) (.ok, .pos 1)
  expect name (σ.exprs.lookupEq (Reg.real64 r)) (some (Term.C64 expected))

private def aluChecks : Except String Unit := do
  let rows : List (String × Nat × Nat × Nat × Nat × Nat) := [
    ("ADD", 0, 0, 15, 3, 18), ("SUB", 1, 0, 15, 3, 12),
    ("MUL", 2, 0, 15, 3, 45), ("UDIV", 3, 0, 15, 3, 5),
    ("OR", 4, 0, 10, 3, 11), ("AND", 5, 0, 10, 3, 2),
    ("LSH", 6, 0, 15, 2, 60), ("RSH", 7, 0, 15, 2, 3),
    ("UREM", 9, 0, 17, 3, 2), ("XOR", 10, 0, 10, 3, 9),
    ("ARSH-positive", 12, 0, 15, 2, 3),
    ("SDIV", 3, 1, 17, 3, 5), ("SREM", 9, 1, 17, 3, 2)]
  for cls in [4, 7] do
    for (name, code, off, a, b, expected) in rows do
      let E := ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 a)
        |>.insertEq (Reg.real64 1) (Term.C64 b)
      ebpfValue s!"ALU{cls}/{name}/reg" (raw (16 * code + 8 + cls) 0 1 off) E 0 expected
      ebpfValue s!"ALU{cls}/{name}/imm" (raw (16 * code + cls) 0 0 off b) E 0 expected
    let max := if cls == 4 then 4294967295 else 18446744073709551615
    let min := if cls == 4 then 2147483648 else 9223372036854775808
    let negThree := if cls == 4 then 4294967293 else 18446744073709551613
    for (name, code, off, a, b, expected) in [
        ("ARSH-negative-one", 12, 0, max, 1, max),
        ("ARSH-negative-odd", 12, 0, negThree, 1, max - 1),
        ("UDIV-zero", 3, 0, 7, 0, 0),
        ("UREM-zero", 9, 0, 7, 0, 7),
        ("SDIV-zero", 3, 1, 7, 0, 0),
        ("SREM-zero", 9, 1, 7, 0, 7),
        ("SDIV-overflow", 3, 1, min, max, min),
        ("SREM-overflow", 9, 1, min, max, 0),
        ("SDIV-negative", 3, 1, negThree, 2, max),
        ("SREM-negative", 9, 1, negThree, 2, max)] do
      let E := ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 a)
        |>.insertEq (Reg.real64 1) (Term.C64 b)
      ebpfValue s!"ALU{cls}/{name}" (raw (16 * code + 8 + cls) 0 1 off) E 0 expected
    ebpfValue s!"ALU{cls}/NEG" (raw (0x80 + cls) 0 0)
      (ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 1)) 0 max
    ebpfValue s!"ALU{cls}/MOV-no-old-dst" (raw (0xb0 + cls) 0 0 0 7) .empty 0 7
  ebpfValue "ALU32-clears-high-half" (raw 0x04 0 0 0 1)
    (ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 4294967295)) 0 0
  ebpfValue "ALU32-shift-count-masked" (raw 0x6c 0 1)
    (ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 1)
      |>.insertEq (Reg.real64 1) (Term.C64 33)) 0 2
  ebpfValue "ALU64-shift-count-masked" (raw 0x6f 0 1)
    (ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 1)
      |>.insertEq (Reg.real64 1) (Term.C64 65)) 0 2
  ebpfValue "ALU32 projects both operands before division" (raw 0x3c 0 1)
    (ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 0x10000000f)
      |>.insertEq (Reg.real64 1) (Term.C64 0x100000003)) 0 5
  ebpfValue "MOV32 projects source without old destination" (raw 0xbc 0 1)
    (ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 0x100000001)) 0 1
  ebpfValue "MOV64 sign extends immediate" (raw 0xb7 0 0 0 0xffffffff)
    .empty 0 18446744073709551615
  ebpfValue "MOV32 zero extends immediate" (raw 0xb4 0 0 0 0xffffffff)
    .empty 0 4294967295
  for (cls, bits, source, expected) in [
      (4, 8, 128, 4294967168), (4, 16, 32769, 4294934529),
      (7, 8, 128, 18446744073709551488), (7, 16, 32769, 18446744073709518849),
      (7, 32, 2147483649, 18446744071562067969)] do
    ebpfValue s!"MOVSX/{cls}/{bits}" (raw (0xb8 + cls) 0 1 (Int.ofNat bits))
      (ExprSet.empty.insertEq (Reg.real64 1) (Term.C64 source)) 0 expected
  for (opcode, bits, expected) in [
      (0xd4, 16, 30600), (0xd4, 32, 1432778632), (0xd4, 64, 1234605616436508552),
      (0xdc, 16, 34935), (0xdc, 32, 2289526357), (0xdc, 64, 9833440827789222417),
      (0xd7, 16, 34935), (0xd7, 32, 2289526357), (0xd7, 64, 9833440827789222417)] do
    ebpfValue s!"END/{opcode}/{bits}" (raw opcode 0 0 0 bits)
      (ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 0x1122334455667788)) 0 expected

private def jumpChecks : Except String Unit := do
  let rows : List (String × Nat × Rel × Rel × Bool × Bool) := [
    ("JEQ", 1, .eq, .eqN 32, false, true),
    ("JGT", 2, .gtu, .gtuN 32, true, false),
    ("JGE", 3, .geu, .geuN 32, true, true),
    ("JSET", 4, .bitsnz 64, .bitsnz 32, true, false),
    ("JNE", 5, .ne, .neN 32, true, false),
    ("JSGT", 6, .gts, .gtsN 32, true, false),
    ("JSGE", 7, .ges, .gesN 32, true, true),
    ("JLT", 10, .ltu, .ltuN 32, false, false),
    ("JLE", 11, .leu, .leuN 32, false, true),
    ("JSLT", 12, .lts, .ltsN 32, false, false),
    ("JSLE", 13, .les, .lesN 32, false, true)]
  for cls in [5, 6] do
    for (name, code, r64, r32, unequal, equal) in rows do
      for (a, b, taken) in [(5, 3, unequal), (0, 0, equal),
          (3, 5, [4, 5, 10, 11, 12, 13].contains code)] do
        for registerSource in [false, true] do
          let opcode := 16 * code + cls + if registerSource then 8 else 0
          let E := ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 a)
            |>.insertEq (Reg.real64 1) (Term.C64 b)
          let word := raw opcode 0 (if registerSource then 1 else 0) 1
            (if registerSource then 0 else b)
          let label := s!"JMP{cls}/{name}/{a}/{registerSource}"
          let c ← one label (ebpf #[word, 0x95, 0x95] E)
          let rel := if cls == 5 then r64 else r32
          let rel := if taken then rel else rel.compl
          expect label (c.dir, c.loc, c.P_k)
            (if taken then .taken else .notTaken, .pos (if taken then 2 else 1),
              [.branch 1 (if taken then .taken else .notTaken) ⟨Term.C64 a, rel, Term.C64 b⟩])
    for (code, taken) in [(6, false), (7, false), (12, true), (13, true)] do
      let E := ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 18446744073709551615)
      let c ← one "signed-negative-jump" (ebpf #[raw (16 * code + cls) 0 0 1 1, 0x95, 0x95] E)
      expect s!"signed-negative-jump/{cls}/{code}" (c.dir, c.loc)
        (if taken then .taken else .notTaken, .pos (if taken then 2 else 1))
  let E := ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 4294967297)
  let c ← one "JMP32-low-view" (ebpf #[raw 0x16 0 0 1 1, 0x95, 0x95] E)
  expect "JMP32-low-view" c.dir .taken
  let c ← one "JMP64-high-view" (ebpf #[raw 0x15 0 0 1 1, 0x95, 0x95] E)
  expect "JMP64-high-view" c.dir .notTaken
  let E := ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 18446744073709551615)
  let c ← one "JMP64 sign extends immediate"
    (ebpf #[raw 0x15 0 0 1 0xffffffff, 0x95, 0x95] E)
  expect "JMP64 sign extends immediate" (c.dir, c.loc) (.taken, .pos 2)
  let E := ExprSet.empty.insertEq (Reg.real64 0) (Term.V64 8)
    |>.insertEq (Reg.real64 1) (Term.C64 5)
  match ebpf #[raw 0x1d 0 1 1, 0x95, 0x95] E with
  | .reject reason => throw s!"symbolic JEQ rejected {reprStr reason}"
  | .candidates cs =>
    expect "symbolic JEQ exhaustive successors" cs.length 2
    for (dir, branchDir, rel, loc) in [
        (Direction.taken, BranchDirection.taken, Rel.eq, 2), (.notTaken, .notTaken, .ne, 1)] do
      let some c := cs.find? (·.dir == dir) | throw s!"symbolic JEQ missing {reprStr dir}"
      expect "symbolic JEQ location" c.loc (.pos loc)
      expect "symbolic JEQ branch observation" c.P_k [.branch 1 branchDir ⟨Term.V64 8, rel, Term.C64 5⟩]
      let σ ← liftResult "symbolic JEQ compose" (applyLocal ⟨E, []⟩ c.E_k c.P_k)
      expect "symbolic JEQ preserves full lhs binding" (σ.exprs.lookupEq (Reg.real64 0)) (some (Term.V64 8))
      expect "symbolic JEQ adds comparison constraint" σ.exprs.constraints [⟨Reg.real64 0, rel, Term.C64 5⟩]
  let E := ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 1)
  let c ← one "known false prunes invalid taken target" (ebpf #[raw 0x15 0 0 99 7, 0x95] E)
  expect "known false prunes invalid taken target" (c.dir, c.loc) (.notTaken, .pos 1)
  let E := ExprSet.empty.insertEq (Reg.real64 0) (Term.C64 7)
  let c ← one "known true prunes invalid fallthrough"
    (ebpf #[0x95, raw 0x15 0 0 (-2) 7] E context 1)
  expect "known true prunes invalid fallthrough" (c.dir, c.loc) (.taken, .pos 0)

private def memoryChecks : Except String Unit := do
  let root ← liftResult "entry" (EBPF.buildE0 entry)
  let E := root.exprs.insertEq (Reg.real64 0) (Term.C64 0xaabbccdd)
  let c ← one "ST-W" (ebpf #[raw 0x62 10 0 (-4) 0x11223344, 0x95] E)
  let σ ← liftResult "ST-W compose" (applyLocal ⟨E, []⟩ c.E_k c.P_k)
  expect "ST-W" (σ.exprs.lookupEq (Reg.sw 0)) (some (Term.C32 0x11223344))
  let c ← one "ST-DW" (ebpf #[raw 0x7a 10 0 (-8) 0xffffffff, 0x95] E)
  expect "ST-DW low/high" (c.E_k.lookupEq (Reg.sw 1), c.E_k.lookupEq (Reg.sw 0))
    (some (Term.C32 4294967295), some (Term.C32 4294967295))
  let old := E.insertEq (Reg.sw 0) (Term.C32 0x11223344)
  for (opcode, off, imm, expected) in [
      (0x72, -3, 0xaa, 0x1122aa44), (0x6a, -4, 0xbbcc, 0x1122bbcc)] do
    let c ← one "ST-partial" (ebpf #[raw opcode 10 0 off imm, 0x95] old)
    expect "ST-partial preserves old lanes" (c.E_k.lookupEq (Reg.sw 0)) (some (Term.C32 expected))
  reject "ST-partial missing old" (ebpf #[raw 0x72 10 0 (-3) 0xaa, 0x95] E) .undefinedSrc
  let old := E.insertEq (Reg.sw 0) (Term.C32 0x800180ff)
  for (opcode, off, expected) in [
      (0x91, -4, 18446744073709551615),
      (0x89, -4, 18446744073709519103),
      (0x81, -4, 18446744071562166527)] do
    ebpfValue s!"MEMSX/{opcode}" (raw opcode 2 10 off) old 2 expected
  for (opcode, off, expected) in [(0xc3, -4, 2147582207), (0xcb, -4, 33023), (0xd3, -4, 255)] do
    ebpfValue s!"LOAD_ACQ/{opcode}" (raw opcode 2 10 off 0x100) old 2 expected
  let c ← one "STORE_REL" (ebpf #[raw 0xc3 10 0 (-4) 0x110, 0x95] old)
  expect "STORE_REL" (c.E_k.lookupEq (Reg.sw 0)) (some (Term.C32 0xaabbccdd))
  for (opcode, expected) in [(0xcb, 0x8001ccdd), (0xd3, 0x800180dd)] do
    let c ← one "STORE_REL narrow" (ebpf #[raw opcode 10 0 (-4) 0x110, 0x95] old)
    expect "STORE_REL narrow preserves untouched lanes" (c.E_k.lookupEq (Reg.sw 0))
      (some (Term.C32 expected))
  let wide := old.insertEq (Reg.sw 1) (Term.C32 0x11223344)
  ebpfValue "LOAD_ACQ DW" (raw 0xdb 2 10 (-8) 0x100) wide 2 0x800180ff11223344
  let c ← one "STORE_REL DW" (ebpf #[raw 0xdb 10 0 (-8) 0x110, 0x95] wide)
  expect "STORE_REL DW simultaneous halves"
    (c.E_k.lookupEq (Reg.sw 1), c.E_k.lookupEq (Reg.sw 0))
    (some (Term.C32 0xaabbccdd), some (Term.C32 0))
  let c ← one "LOAD-context-data" (ebpf #[raw 0x61 2 1, 0x95] root.exprs)
  let loaded ← liftResult "LOAD-context compose" (applyLocal root c.E_k c.P_k)
  let c ← one "ST-packet" (ebpf #[raw 0x6a 2 0 3 0x7788, 0x95] loaded.exprs)
  expect "ST-packet byte values" (c.E_k.lookupEq (Reg.packet 0 3), c.E_k.lookupEq (Reg.packet 0 4))
    (some (Term.C32 0x88), some (Term.C32 0x77))
  expect "ST-packet full-source observation" c.P_k [.packetWrite 70 0 3 16 (Term.C64 0x7788)]
  reject "ST packet boundary" (ebpf #[raw 0x6a 2 0 63 0x7788, 0x95] loaded.exprs) .undefinedSrc

private def atomicChecks : Except String Unit := do
  let root ← liftResult "atomic entry" (EBPF.buildE0 entry)
  for (opcode, off, high) in [(0xc3, -4, false), (0xdb, -8, true)] do
    for (imm, expected) in [(0x00, 13), (0x01, 13), (0x40, 11), (0x41, 11),
        (0x50, 2), (0x51, 2), (0xa0, 9), (0xa1, 9), (0xe1, 3)] do
      let E := root.exprs.insertEq (Reg.real64 1) (Term.C64 3)
        |>.insertEq (Reg.sw (if high then 1 else 0)) (Term.C32 10)
        |>.insertEq (Reg.sw 0) (Term.C32 (if high then 0 else 10))
      let c ← one s!"atomic/{opcode}/{imm}" (ebpf #[raw opcode 10 1 off imm, 0x95] E)
      let σ ← liftResult "atomic compose" (applyLocal ⟨E, []⟩ c.E_k c.P_k)
      expect s!"atomic memory/{opcode}/{imm}"
        (σ.exprs.lookupEq (Reg.sw (if high then 1 else 0))) (some (Term.C32 expected))
      expect s!"atomic old source/{opcode}/{imm}" (σ.exprs.lookupEq (Reg.real64 1))
        (some (Term.C64 (if imm % 2 == 1 then 10 else 3)))
      if high then expect "atomic DW high half" (σ.exprs.lookupEq (Reg.sw 0)) (some (Term.C32 0))
    for (expectedOld, next) in [(10, 3), (9, 10)] do
      let E := root.exprs.insertEq (Reg.real64 0) (Term.C64 expectedOld)
        |>.insertEq (Reg.real64 1) (Term.C64 3)
        |>.insertEq (Reg.sw (if high then 1 else 0)) (Term.C32 10)
        |>.insertEq (Reg.sw 0) (Term.C32 (if high then 0 else 10))
      let c ← one "CMPXCHG" (ebpf #[raw opcode 10 1 off 0xf1, 0x95] E)
      expect "CMPXCHG simultaneous old memory and register"
        (c.E_k.lookupEq (Reg.sw (if high then 1 else 0)), c.E_k.lookupEq (Reg.real64 0))
        (some (Term.C32 next), some (Term.C64 10))
  let E := root.exprs.insertEq (Reg.sw 1) (Term.C32 4294967295)
    |>.insertEq (Reg.sw 0) (Term.C32 1)
    |>.insertEq (Reg.real64 1) (Term.C64 1)
  let c ← one "DW-carry" (ebpf #[raw 0xdb 10 1 (-8) 1, 0x95] E)
  expect "DW single 64-bit carry and old fetch"
    (c.E_k.lookupEq (Reg.sw 1), c.E_k.lookupEq (Reg.sw 0), c.E_k.lookupEq (Reg.real64 1))
    (some (Term.C32 0), some (Term.C32 2), some (Term.C64 8589934591))
  let E := root.exprs.insertEq (Reg.real64 0) (Term.C64 10)
    |>.insertEq (Reg.sw 0) (Term.C32 10)
  let c ← one "CMPXCHG same r0 source" (ebpf #[raw 0xc3 10 0 (-4) 0xf1, 0x95] E)
  expect "CMPXCHG reads source before writing r0"
    (c.E_k.lookupEq (Reg.sw 0), c.E_k.lookupEq (Reg.real64 0))
    (some (Term.C32 10), some (Term.C64 10))
  let concreteContext : EBPF.StepContext := { entry := { entry with tSp := Term.C64 4096 } }
  let E := ExprSet.empty.insertEq (Reg.real64 2) (Term.C64 4092)
    |>.insertEq (Reg.sw 0) (Term.C32 10)
  let c ← one "XCHG base/source alias"
    (ebpf #[raw 0xc3 2 2 0 0xe1, 0x95] E concreteContext)
  expect "XCHG address and source from one pre-state"
    (c.E_k.lookupEq (Reg.sw 0), c.E_k.lookupEq (Reg.real64 2))
    (some (Term.C32 4092), some (Term.C64 10))
  let E := root.exprs.insertEq (Reg.real64 2) (Term.C64 1)
  reject "atomic missing old memory" (ebpf #[raw 0xc3 10 2 (-4) 1, 0x95] E) .undefinedSrc
  reject "atomic missing high half" (ebpf #[raw 0xdb 10 2 (-8) 1, 0x95]
    (E.insertEq (Reg.sw 1) (Term.C32 1))) .undefinedSrc
  reject "CMPXCHG missing r0" (ebpf #[raw 0xc3 10 2 (-4) 0xf1, 0x95]
    (E.insertEq (Reg.sw 0) (Term.C32 1))) .undefinedSrc
  reject "atomic context forbidden" (ebpf #[raw 0xc3 1 2 0 1, 0x95] E) .unsupported
  reject "atomic unaligned forbidden" (ebpf #[raw 0xc3 10 2 (-3) 1, 0x95] E) .undefinedSrc
  let c ← one "packet-base" (ebpf #[raw 0x61 3 1, 0x95] E)
  let loaded ← liftResult "packet-base compose" (applyLocal ⟨E, []⟩ c.E_k c.P_k)
  reject "atomic packet forbidden" (ebpf #[raw 0xc3 3 2 0 1, 0x95] loaded.exprs) .unsupported

private def rvWord (funct : Nat) : UInt32 :=
  UInt32.ofNat (0x02000033 + 9 * 1048576 + 8 * 32768 + funct * 4096 + 10 * 128)

private def rv (words : Array UInt32) (E : ExprSet)
    (ctx : RV32IMC.StepContext := {}) : StepResult :=
  RV32IMC.inferStep (RV32IMC.decodeProgram words) ctx 70 0 ⟨E, []⟩

private def rvMChecks : Except String Unit := do
  let rows : List (Nat × Op × Nat) := [
    (0, .mullo .w32, 4294967293), (1, .mulh .w32, 4294967295),
    (2, .mulhsu .w32, 4294967295), (3, .mulhu .w32, 2),
    (4, .sdiv .w32 4294967295, 0), (5, .udiv .w32 4294967295, 1431655765),
    (6, .srem .w32, 4294967295), (7, .urem .w32, 0)]
  for (funct, op, expected) in rows do
    let E := ExprSet.empty.insertEq (Reg.real32 8) (Term.C32 4294967295)
      |>.insertEq (Reg.real32 9) (Term.C32 3)
    let c ← one s!"RV32-M/{funct}" (rv #[rvWord funct, 0x0001] E)
    expect s!"RV32-M/{funct}" (c.E_k.lookupEq (Reg.real32 10)) (some (Term.C32 expected))
    let E := ExprSet.empty.insertEq (Reg.real32 8) (Term.V32 41)
      |>.insertEq (Reg.real32 9) (Term.V32 42)
    let c ← one s!"RV32-open-M/{funct}" (rv #[rvWord funct, 0x0001] E)
    expect s!"RV32-open-M/{funct}" (c.E_k.lookupEq (Reg.real32 10))
      (some (.app .w32 op [Term.V32 41, Term.V32 42]))
  for (funct, a, b, expected) in [
      (4, 7, 0, 4294967295), (5, 7, 0, 4294967295),
      (6, 7, 0, 7), (7, 7, 0, 7),
      (4, 2147483648, 4294967295, 2147483648),
      (6, 2147483648, 4294967295, 0),
      (4, 4294967293, 2, 4294967295), (6, 4294967293, 2, 4294967295)] do
    let E := ExprSet.empty.insertEq (Reg.real32 8) (Term.C32 a)
      |>.insertEq (Reg.real32 9) (Term.C32 b)
    let c ← one "RV32-M boundary" (rv #[rvWord funct, 0x0001] E)
    expect s!"RV32-M boundary/{funct}/{a}/{b}" (c.E_k.lookupEq (Reg.real32 10))
      (some (Term.C32 expected))
  reject "RV32-M missing source" (rv #[rvWord 0, 0x0001] .empty) .undefinedSrc
  reject "RV32 privileged encoding" (rv #[0x30200073, 0x0001] .empty) .unsupported

private def helperChecks : Except String Unit := do
  let root ← liftResult "helper entry" (EBPF.buildE0 entry)
  let key64 : Term := .app .w64 (.add .w64) [Term.V64 0, Term.C64 18446744073709551608]
  let value64 : Term := .app .w64 (.add .w64) [Term.V64 0, Term.C64 18446744073709551612]
  let maps : List MapLayout := [⟨42, 3, 2⟩]
  let E := root.exprs.insertEq (Reg.real64 1) (Term.C64 42)
    |>.insertEq (Reg.real64 2) key64
    |>.insertEq (Reg.real64 3) value64
    |>.insertEq (Reg.real64 4) (Term.C64 0)
    |>.insertEq (Reg.sw 1) (Term.C32 0x44332211)
    |>.insertEq (Reg.sw 0) (Term.C32 0x0000bbaa)
  for (id, kind, abi, tail) in [
      (1, HelperKind.lookup, [Term.C64 42, key64], [Term.C64 17, Term.C64 34, Term.C64 51]),
      (3, HelperKind.delete, [Term.C64 42, key64], [Term.C64 17, Term.C64 34, Term.C64 51]),
      (2, HelperKind.update, [Term.C64 42, key64, value64, Term.C64 0],
        [Term.C64 17, Term.C64 34, Term.C64 51, Term.C64 170, Term.C64 187])] do
    let c ← one s!"eBPF helper/{id}" (ebpf #[raw 0x85 0 0 0 id, 0x95] E { context with maps := maps })
    expect s!"eBPF helper frozen/{id}" c.P_k [.helper 70 kind (abi ++ tail)]
    expect s!"eBPF helper return ABI-only/{id}" (c.E_k.lookupEq (Reg.real64 0))
      (some (.app .w64 (.externalResult 70 0) (Term.C64 id :: abi)))
    let changed := E.insertEq (Reg.sw 1) (Term.C32 0x00030201)
    let c' ← one "eBPF helper changed snapshot"
      (ebpf #[raw 0x85 0 0 0 id, 0x95] changed { context with maps := maps })
    let changedTail := [Term.C64 1, Term.C64 2, Term.C64 3] ++
      (if id == 2 then [Term.C64 170, Term.C64 187] else [])
    expect "eBPF helper current bytes" c'.P_k [.helper 70 kind (abi ++ changedTail)]
    expect "eBPF helper old observation frozen" c.P_k [.helper 70 kind (abi ++ tail)]
  let prefix64 := [Term.C64 42, key64, value64, Term.C64 0]
  for incomplete in [
      { E with entries := E.entries.filter (fun e => e.reg != Reg.sw 0) },
      { E with entries := E.entries.filter (fun e => e.reg != Reg.sw 1) }] do
    let c ← one "eBPF update incomplete"
      (ebpf #[raw 0x85 0 0 0 2, 0x95] incomplete { context with maps := maps })
    expect "eBPF update no half tail" c.P_k [.helper 70 .update prefix64]
  let c ← one "eBPF duplicate layout"
    (ebpf #[raw 0x85 0 0 0 2, 0x95] E { context with maps := maps ++ maps })
  expect "eBPF ambiguous layout prefix" c.P_k [.helper 70 .update prefix64]
  let c ← one "eBPF delete missing key" (ebpf #[raw 0x85 0 0 0 3, 0x95]
    { E with entries := E.entries.filter (fun e => e.reg != Reg.sw 1) }
    { context with maps := maps })
  expect "eBPF delete missing key prefix" c.P_k [.helper 70 .delete [Term.C64 42, key64]]
  let key32 : Term := .app .w32 (.add .w32) [Term.V32 0, Term.C32 3]
  let value32 : Term := .app .w32 (.add .w32) [Term.V32 0, Term.C32 4]
  let E := ExprSet.empty.insertEq (Reg.real32 2) (Term.V32 0)
    |>.insertEq (Reg.real32 11) (Term.C32 42)
    |>.insertEq (Reg.real32 12) key32
    |>.insertEq (Reg.real32 13) value32
    |>.insertEq (Reg.real32 14) (Term.C32 0)
    |>.insertEq (Reg.sw 8589934592) (Term.C32 0x04030201)
    |>.insertEq (Reg.sw 8589934596) (Term.C32 0x08070605)
  let ctx : RV32IMC.StepContext := {
    imageBase := some 0x1000, helperAddress := some 0x1100, maps := maps }
  for (id, kind, abi, tail) in [
      (1, HelperKind.lookup, [Term.C32 42, key32], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (3, HelperKind.delete, [Term.C32 42, key32], [Term.C32 4, Term.C32 5, Term.C32 6]),
      (2, HelperKind.update, [Term.C32 42, key32, value32, Term.C32 0],
        [Term.C32 4, Term.C32 5, Term.C32 6, Term.C32 5, Term.C32 6])] do
    let state := E.insertEq (Reg.real32 10) (Term.C32 id)
    let c ← one s!"RV helper/{id}" (rv #[0x100000ef, 0x0001] state ctx)
    expect s!"RV helper full tail/{id}" c.P_k [.helper 70 kind (abi ++ tail)]
    expect s!"RV helper return ABI-only/{id}" (c.E_k.lookupEq (Reg.real32 10))
      (some (.app .w32 (.externalResult 70 0) (Term.C32 id :: abi)))
    let missing := { state with entries := state.entries.filter (fun e => e.reg != Reg.sw 8589934596) }
    let c ← one "RV helper incomplete" (rv #[0x100000ef, 0x0001] missing ctx)
    expect "RV helper no partial tail" c.P_k [.helper 70 kind abi]
  let missingValue : Term := .app .w32 (.add .w32) [Term.V32 0, Term.C32 7]
  let state := E.insertEq (Reg.real32 10) (Term.C32 2)
    |>.insertEq (Reg.real32 13) missingValue
  let c ← one "RV update missing final byte" (rv #[0x100000ef, 0x0001] state ctx)
  expect "RV update missing final byte no half tail" c.P_k
    [.helper 70 .update [Term.C32 42, key32, missingValue, Term.C32 0]]
  let state := E.insertEq (Reg.real32 10) (Term.C32 2)
  let c ← one "RV ambiguous layout" (rv #[0x100000ef, 0x0001] state { ctx with maps := maps ++ maps })
  expect "RV ambiguous layout original prefix" c.P_k
    [.helper 70 .update [Term.C32 42, key32, value32, Term.C32 0]]

private def solverChecks : Except String Unit := do
  let x := Term.V32 1
  let y := Term.V32 2
  let rows : List (String × Term × Term × Nat) := [
    ("R1-whole-closed", .app .w32 (.mullo .w32)
      [.app .w32 (.add .w32) [Term.C32 2, Term.C32 3], Term.C32 4], Term.C32 20, 20),
    ("R2-spine", .app .w32 (.add .w32)
      [.app .w32 (.add .w32) [x, Term.C32 16], Term.C32 4],
      .app .w32 (.add .w32) [x, Term.C32 20], 29),
    ("R3-sub", .app .w32 (.sub .w32) [x, Term.C32 4],
      .app .w32 (.add .w32) [x, Term.C32 4294967292], 5),
    ("R5-sub", .app .w32 (.sub .w32) [x, x], Term.C32 0, 0),
    ("R5-xor", .app .w32 (.xor 32) [x, x], Term.C32 0, 0),
    ("R6-add", .app .w32 (.add .w32) [x, Term.C32 0], x, 9),
    ("R6-or", .app .w32 (.or 32) [x, Term.C32 0], x, 9),
    ("R6-xor", .app .w32 (.xor 32) [x, Term.C32 0], x, 9),
    ("R6-and", .app .w32 (.and 32) [x, Term.C32 4294967295], x, 9),
    ("R6-mul", .app .w32 (.mullo .w32) [x, Term.C32 1], x, 9),
    ("R6-shl", .app .w32 (.shl .w32) [x, Term.C32 0], x, 9),
    ("R6-lshr", .app .w32 (.lshr .w32) [x, Term.C32 0], x, 9),
    ("R6-ashr", .app .w32 (.ashr .w32) [x, Term.C32 0], x, 9)]
  let ν : Var → Nat := fun v => if v.name == 1 then 9 else 13
  let total : ExternalInterpretation := {
    externalResult := fun _ _ _ _ => some 99, inputByte := fun _ _ _ => some 171 }
  have _ : total.Total :=
    ⟨fun _ _ _ _ => ⟨99, rfl⟩, fun _ _ _ => ⟨171, rfl⟩⟩
  for (name, input, expected, value) in rows do
    expect name (solve input) expected
    expect (name ++ "/idempotent") (solve (solve input)) expected
    expect (name ++ "/input meaning") (interpretTerm ν total input) (some value)
    expect (name ++ "/solved meaning") (interpretTerm ν total (solve input)) (some value)
  let unordered : Term := .app .w32 (.add .w32) [y, .app .w32 (.add .w32) [Term.C32 4, x]]
  let reordered : Term := .app .w32 (.add .w32) [x, .app .w32 (.add .w32) [y, Term.C32 4]]
  expect "additive canonical deduplication" (solve unordered == solve reordered) true
  expect "additive canonical meaning" (interpretTerm ν total (solve unordered)) (some 26)
  let untouched : List (String × Term) := [
    ("no-open-subtree-fold", .app .w32 (.mullo .w32)
      [x, .app .w32 (.add .w32) [Term.C32 2, Term.C32 3]]),
    ("no-distributivity", .app .w32 (.mullo .w32)
      [x, .app .w32 (.add .w32) [y, Term.C32 1]]),
    ("no-partial-or-unit", .app .w32 (.or 8) [x, Term.C32 0]),
    ("no-partial-and-unit", .app .w32 (.and 8) [x, Term.C32 255]),
    ("invalid-arity", .app .w32 (.add .w32) [x]),
    ("invalid-width", .app .w32 (.sub .w64) [x, x])]
  for (name, input) in untouched do
    expect name (solve input) input
  let missing : ExternalInterpretation := {
    externalResult := fun _ _ _ _ => none, inputByte := fun _ _ _ => none }
  let explicit : ExternalInterpretation := {
    externalResult := fun w event lane args =>
      if w == .w32 && event == 7 && lane == 2 && args == [5] then some 99 else none
    inputByte := fun resource base address =>
      if resource == 3 && base == 4096 && address == 4108 then some 171 else none }
  let ext : Term := .app .w32 (.externalResult 7 2) [Term.C32 5]
  let byte : Term := .app .w32 (.inputByte 3) [Term.C32 4096, Term.C32 4108]
  expect "explicit external meaning" (interpretTerm (fun _ => 0) explicit ext) (some 99)
  expect "missing external meaning" (interpretTerm (fun _ => 0) missing ext) none
  expect "explicit input meaning" (interpretTerm (fun _ => 0) explicit byte) (some 171)
  expect "missing input meaning" (interpretTerm (fun _ => 0) missing byte) none
  expect "external D remains partial" (eval ext) none
  expect "external solve does not invent result" (solve ext) ext
  expect "Expr explicit theta" (interpretExpr (fun _ => 99) (fun _ => 0) explicit
    ⟨Reg.real32 1, .eq, ext⟩) (some true)
  expect "Expr missing theta" (interpretExpr (fun _ => 99) (fun _ => 0) missing
    ⟨Reg.real32 1, .eq, ext⟩) none
  expect "pure arithmetic ignores external theta"
    (interpretTerm (fun _ => 0) explicit (.app .w32 (.udiv .w32 4294967295) [Term.C32 7, Term.C32 0]))
    (some 4294967295)
  expect "invalid signature remains undefined"
    (interpretTerm (fun _ => 0) explicit (.app .w32 (.add .w64) [Term.C32 1, Term.C32 2])) none
  let canceled : Term := .app .w32 (.sub .w32) [ext, ext]
  expect "partial theta before cancellation" (interpretTerm (fun _ => 0) missing canceled) none
  expect "partial theta after cancellation"
    (interpretTerm (fun _ => 0) missing (solve canceled)) (some 0)
  expect "explicit theta before cancellation" (interpretTerm (fun _ => 0) explicit canceled) (some 0)
  expect "total theta before cancellation" (interpretTerm ν total canceled) (some 0)
  expect "total theta after cancellation" (interpretTerm ν total (solve canceled)) (some 0)
  let observed : Term := .app .w32 (.add .w32) [ext, byte]
  expect "total theta retains external and input values" (interpretTerm ν total observed) (some 270)
  expect "total theta solved external and input values" (interpretTerm ν total (solve observed)) (some 270)

private def operatorChecks : Except String Unit := do
  let total : ExternalInterpretation := {
    externalResult := fun _ _ _ _ => some 99, inputByte := fun _ _ _ => some 171 }
  for (w, bits, max) in [(Width.w32, 32, 4294967295), (.w64, 64, 18446744073709551615)] do
    let rows : List (Op × CrossOp × String × String × String × Nat × Nat × Nat) := [
      (.udiv w 0, .udiv bits 0, s!"udiv{bits}_0", "udiv", s!"[{bits},0]", 7, 0, 0),
      (.udiv w max, .udiv bits max, s!"udiv{bits}_{max}", "udiv", s!"[{bits},{max}]", 7, 0, max),
      (.sdiv w 0, .sdiv bits 0, s!"sdiv{bits}_0", "sdiv", s!"[{bits},0]", 7, 0, 0),
      (.sdiv w max, .sdiv bits max, s!"sdiv{bits}_{max}", "sdiv", s!"[{bits},{max}]", 7, 0, max),
      (.urem w, .urem bits, s!"urem{bits}", "urem", s!"[{bits}]", 17, 3, 2),
      (.srem w, .srem bits, s!"srem{bits}", "srem", s!"[{bits}]", max - 2, 2, max),
      (.mulh w, .mulh bits, s!"mulh{bits}", "mulh", s!"[{bits}]", max - 2, 2, max),
      (.mulhu w, .mulhu bits, s!"mulhu{bits}", "mulhu", s!"[{bits}]", max, 3, 2),
      (.mulhsu w, .mulhsu bits, s!"mulhsu{bits}", "mulhsu", s!"[{bits}]", max - 2, max, max - 2)]
    for (op, crossOp, rawStem, canonicalStem, params, a, b, value) in rows do
      let term : Term := .app w op [.var w 1, .var w 2]
      let rawWire := rawStem ++ s!"(v{bits}:1,v{bits}:2)"
      let some parsed := parseTerm rawWire w | throw s!"raw parse rejected {rawWire}"
      expect ("raw parse " ++ rawStem) parsed term
      let ν : Var → Nat := fun v => if v.name == 1 then a else b
      expect ("parsed numeric meaning " ++ rawStem) (interpretTerm ν total parsed) (some value)
      expect ("rendered raw meaning " ++ rawStem) (parseTerm (renderTerm term) w) (some term)
      let canonical : CrossPred := .ret ⟨.app crossOp [.var 1, .var 2]⟩
      let wire := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"app\",\"op\":\"" ++ canonicalStem ++
        "\",\"params\":" ++ params ++ ",\"args\":[{\"kind\":\"var\",\"name\":1},{\"kind\":\"var\",\"name\":2}]}}"
      expect ("canonical conversion " ++ rawStem) (toCross {} (.ret term)) canonical
      let json ← liftResult "canonical JSON" (Json.parse wire)
      expect ("canonical parse " ++ rawStem) (parseCrossPredJson json) (some canonical)
      let rendered ← liftResult "rendered canonical JSON" (Json.parse (renderCrossPredJson canonical))
      expect ("rendered canonical meaning " ++ rawStem) (parseCrossPredJson rendered) (some canonical)
    let select : Term := .app w (.selectEq w) [.var w 1, .var w 2, .var w 3, .var w 4]
    let rawWire := s!"selectEq{bits}(v{bits}:1,v{bits}:2,v{bits}:3,v{bits}:4)"
    let some parsed := parseTerm rawWire w | throw s!"raw parse rejected {rawWire}"
    expect "selectEq raw parse" parsed select
    expect "selectEq raw rendered meaning" (parseTerm (renderTerm select) w) (some select)
    for (rhs, value) in [(5, 17), (6, 19)] do
      let ν : Var → Nat := fun v =>
        if v.name == 1 then 5 else if v.name == 2 then rhs else if v.name == 3 then 17 else 19
      expect s!"selectEq{bits}/{rhs}" (interpretTerm ν total parsed) (some value)
    let canonical : CrossPred := .ret ⟨.app (.selectEq bits) [.var 1, .var 2, .var 3, .var 4]⟩
    let wire := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"app\",\"op\":\"selectEq\",\"params\":[" ++
      toString bits ++ "],\"args\":[{\"kind\":\"var\",\"name\":1},{\"kind\":\"var\",\"name\":2},{\"kind\":\"var\",\"name\":3},{\"kind\":\"var\",\"name\":4}]}}"
    expect "selectEq canonical conversion" (toCross {} (.ret select)) canonical
    let json ← liftResult "selectEq JSON" (Json.parse wire)
    expect "selectEq canonical parse" (parseCrossPredJson json) (some canonical)
    let rendered ← liftResult "selectEq rendered JSON" (Json.parse (renderCrossPredJson canonical))
    expect "selectEq canonical rendered meaning" (parseCrossPredJson rendered) (some canonical)
  expect "bad new Op arity rejected" (parseTerm "udiv32_0(v32:1)") none
  expect "bad mixed width rejected" (parseTerm "sdiv32_0(v64:1,v32:2)") none

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def strField (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?
private def arrField (j : Json) (key : String) : Except String (Array Json) := do
  (← field j key).getArr?

private def alignmentChecks : Except String Unit := do
  let collision := unifyLists [.ret ⟨.var 0⟩, .ret ⟨.var 1⟩] [.ret ⟨.var 1⟩, .ret ⟨.var 1⟩]
  expect "alignment identity collision"
    (collision.ambiguous, collision.pairs.length, collision.onlyLeft.length, collision.onlyRight.length)
    (true, 1, 1, 1)
  let one : CrossPred := .ret ⟨.c 1⟩
  let two : CrossPred := .ret ⟨.c 2⟩
  let three : CrossPred := .ret ⟨.c 3⟩
  let duplicate := unifyLists [one, one] [one]
  expect "alignment duplicate ambiguity"
    (duplicate.ambiguous, duplicate.pairs.length, duplicate.onlyLeft.length, duplicate.onlyRight.length)
    (true, 1, 1, 0)
  expect "alignment complements" (unifyLists [one, two] [one, three])
    { ambiguous := false, subst := .empty, pairs := [(0, 0)], onlyLeft := [1], onlyRight := [1] }
  expect "alignment swap complements" (unifyLists [one, three] [one, two])
    { ambiguous := false, subst := .empty, pairs := [(0, 0)], onlyLeft := [1], onlyRight := [1] }
  expect "alignment renamed swap" (unifyLists [.ret ⟨.var 9⟩] [.ret ⟨.var 4⟩])
    { ambiguous := false, subst := ⟨[(9, 4)], []⟩, pairs := [(0, 0)], onlyLeft := [], onlyRight := [] }
  expect "alignment rename" (unifyLists [.ret ⟨.var 4⟩] [.ret ⟨.var 9⟩])
    { ambiguous := false, subst := ⟨[(4, 9)], []⟩, pairs := [(0, 0)], onlyLeft := [], onlyRight := [] }
  let crossing := unifyLists [one, two] [two, one]
  expect "alignment increasing crossing ambiguity"
    (crossing.ambiguous, crossing.pairs.length, crossing.onlyLeft.length, crossing.onlyRight.length)
    (true, 1, 1, 1)
  let args := "[{\"kind\":\"c\",\"value\":\"7\"},{\"kind\":\"c\",\"value\":\"0\"}]"
  let left := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"app\",\"op\":\"udiv\",\"params\":[32,0],\"args\":" ++ args ++ "}}"
  let right := "{\"kind\":\"ret\",\"payload\":{\"kind\":\"app\",\"op\":\"udiv\",\"params\":[32,4294967295],\"args\":" ++ args ++ "}}"
  let result ← Json.parse (exportCrossPredUnify ("{\"left\":[" ++ left ++ "],\"right\":[" ++ right ++ "]}"))
  expect "alignment policies response" (← (← field result "ok").getBool?) true
  expect "alignment policies cannot unify" (← (← field result "pass").getBool?) false
  expectJson "alignment policies pairs" (.arr (← arrField result "pairs")) (.arr #[])
  expect "alignment policies unmatched left"
    (← (← arrField result "onlyLeft").toList.mapM Json.getNat?) [0]
  expect "alignment policies unmatched right"
    (← (← arrField result "onlyRight").toList.mapM Json.getNat?) [0]

private def expectStep (name response location : String) (bindings : List (Reg × Term))
    (predicates : List Predicate) : Except String Unit := do
  let result ← Json.parse response
  expect (name ++ "/status") (← strField result "status") "ok"
  expectJson (name ++ "/reason") (← field result "reason") Json.null
  let successors ← arrField result "successors"
  let [successor] := successors.toList | throw s!"{name}: expected one successor, got {successors.size}"
  expect (name ++ "/direction") (← strField successor "dir") "OK"
  expect (name ++ "/location") (← strField successor "loc") location
  let exprs ← field successor "exprs"
  let preds ← field successor "predicates"
  let some state := parseSemStateJson exprs.compress preds.compress
    | throw s!"{name}: invalid successor state"
  expect (name ++ "/binding domain") state.exprs.entries.length bindings.length
  for (reg, term) in bindings do
    expect (name ++ s!"/{reprStr reg}") (state.exprs.lookupEq reg) (some term)
  expect (name ++ "/constraints") state.exprs.constraints []
  expect (name ++ "/observations") state.predicates predicates

private def expectFailure (name response reason : String) : Except String Unit := do
  let result ← Json.parse response
  expect (name ++ "/status") (← strField result "status") "fail"
  expect (name ++ "/reason") (← strField result "reason") reason
  expectJson (name ++ "/atomic rejection") (.arr (← arrField result "successors")) (.arr #[])

private def ffiChecks : Except String Unit := do
  let metadataJson := "{\"entry\":{\"tCtx\":\"v64:1\",\"tSp\":\"v64:0\",\"tData\":\"v32:2\",\"packetBytes\":64,\"alphaCtx\":0,\"packetId\":0,\"stackId\":0}}"
  let call := fun words event j E P =>
    EBPF.exportEbpfExpandStep words metadataJson event j E P
  expectStep "String FFI MOV actual state" (call #[raw 0xb7 0 0 0 7, 0x95] 70 0 "[]" "[]")
    "1" [(Reg.real64 0, Term.C64 7)] []
  expectStep "String FFI LDDW value and raw-slot successor"
    (call #[raw 0x18 0 0 0 0x55667788, raw 0 0 0 0 0x11223344, 0x95] 70 0 "[]" "[]")
    "2" [(Reg.real64 0, Term.C64 0x1122334455667788)] []
  let failures : List (String × Array UInt64 × UInt32 × String × String) := [
    ("illegal opcode", #[0, 0x95], 0, "[]", "LocalReject"),
    ("r10 destination", #[raw 0xb7 10 0 0 7, 0x95], 0, "[]", "LocalReject"),
    ("immediate shift range", #[raw 0x64 0 0 0 32, 0x95], 0, "[]", "LocalReject"),
    ("reserved source field", #[raw 0xb7 0 1 0 7, 0x95], 0, "[]", "LocalReject"),
    ("invalid atomic selector", #[raw 0xc3 10 1 (-4) 2, 0x95], 0, "[]", "LocalReject"),
    ("FETCH r10", #[raw 0xc3 10 10 (-4) 1, 0x95], 0, "[]", "LocalReject"),
    ("missing ALU old", #[raw 0x04 0 0 0 1, 0x95], 0, "[]", "UndefinedSrc"),
    ("missing helper ABI", #[raw 0x85 0 0 0 2, 0x95], 0, "[]", "UndefinedSrc"),
    ("LDDW continuation", #[raw 0x18 0 0 0 7, 0, 0x95], 1, "[]", "LocalReject"),
    ("LDDW missing upper", #[raw 0x18 0 0 0 7], 0, "[]", "LocalReject"),
    ("LDDW malformed upper", #[raw 0x18 0 0 0 7, raw 0 1 0, 0x95], 0, "[]", "LocalReject"),
    ("branch all-or-nothing", #[raw 0x15 0 0 99 7, 0x95], 0,
      "[{\"reg\":\"real64:0\",\"rel\":\"eq\",\"term\":\"v64:8\"}]", "UnboundTarget"),
    ("branch continuation all-or-nothing", #[raw 0x15 0 0 1 7, raw 0x18 1 0 0 0, 0, 0x95], 0,
      "[{\"reg\":\"real64:0\",\"rel\":\"eq\",\"term\":\"v64:8\"}]", "UnboundTarget")]
  for (name, words, j, E, reason) in failures do
    expectFailure ("String FFI reject/" ++ name) (call words 70 j E "[]") reason
  let E := "[{\"reg\":\"real64:0\",\"rel\":\"eq\",\"term\":\"1\"},{\"reg\":\"real64:0\",\"rel\":\"eq\",\"term\":\"2\"}]"
  expectFailure "String FFI malformed state rejected" (call #[raw 0xb7 0 0 0 7, 0x95] 70 0 E "[]")
    "LocalReject"
  let E := "[{\"reg\":\"real64:0\",\"rel\":\"eq\",\"term\":\"7\"}]"
  expectStep "String FFI EXIT frozen return" (call #[0x95] 70 0 E "[]")
    "exit" [(Reg.real64 0, Term.C64 7)] [.ret (Term.C64 7)]
  let rvMeta := "{\"base\":4096,\"helperAddress\":4352,\"returnAddress\":8192}"
  expectStep "RV String FFI actual open M"
    (RV32IMC.exportRv32ExpandStep #[rvWord 5, 0x0001] rvMeta 70 0
      "[{\"reg\":\"real32:8\",\"rel\":\"eq\",\"term\":\"v32:41\"},{\"reg\":\"real32:9\",\"rel\":\"eq\",\"term\":\"v32:42\"}]" "[]")
    "1" [(Reg.real32 8, Term.V32 41), (Reg.real32 9, Term.V32 42),
      (Reg.real32 10, .app .w32 (.udiv .w32 4294967295) [Term.V32 41, Term.V32 42])] []
  expectFailure "RV String FFI illegal all-or-nothing"
    (RV32IMC.exportRv32ExpandStep #[0xffffffff, 0x0001] rvMeta 70 0 "[]" "[]") "LocalReject"

private def rvFixture : Array UInt32 :=
  #[4417, 50694, 50210, 49702, 2048, 16644, 16716, 14976531, 17669, 180744035, 12899843, 26285,
    2290517651, 14026339, 135267987, 14031459, 19170835, 180740195, 17094147, 17737, 40977, 17721,
    26297, 3630597779, 14028131, 18081, 14032739, 38182, 21300755, 12970595, 9782531, 41017, 38182,
    42272275, 113638243, 17665, 49194, 1077413303, 780502419, 17669, 34314, 18049, 18177, 18305,
    13121, 34218, 17669, 51593, 16784, 16852, 1541, 1455891, 38586, 49552, 49620, 17794, 17989,
    46504803, 6591747, 8689027, 10786307, 300675, 2397955, 4495235, 10784803, 11833635, 12882467,
    13931299, 14980131, 16028963, 17677, 16562, 17442, 17554, 321, 32898]

private def snapshotProtocolChecks : Except String Unit := do
  let program := #[raw 0xb7 0 0 0 7, 0x95]
  let metadataJson := "{\"entry\":{\"tCtx\":\"v64:1\",\"tSp\":\"v64:0\",\"tData\":\"v32:2\",\"packetBytes\":64,\"alphaCtx\":0,\"packetId\":0,\"stackId\":0}}"
  let rows : List (UInt32 × String × String × List Predicate × List String) := [
    (1, "running", "1", [], ["1"]),
    (2, "complete", "exit", [.ret (Term.C64 7)], [])]
  for (steps, status, location, observations, pending) in rows do
    let result ← Json.parse (EBPF.exportEbpfBoundWordsSnapshot program metadataJson steps 4)
    expect ("MOV/EXIT snapshot status/" ++ status) (← strField result "status") status
    expectJson ("MOV/EXIT snapshot reason/" ++ status) (← field result "reason") Json.null
    expectJson ("MOV/EXIT snapshot failed/" ++ status) (← field result "failed") Json.null
    let nodes ← arrField result "nodes"
    let work ← arrField result "work"
    let workLocations ← work.toList.mapM fun ref => do
      let id ← ref.getNat?
      let some node ← nodes.toList.findM? (fun n => return (← (← field n "id").getNat?) == id)
        | throw s!"MOV/EXIT snapshot has dangling work reference {id}"
      strField node "loc"
    expect ("MOV/EXIT snapshot work/" ++ status) workLocations pending
    let some node ← nodes.toList.findM? (fun n => return (← strField n "loc") == location)
      | throw s!"MOV/EXIT snapshot missing location {location}"
    let exprs ← field node "exprs"
    let predicates ← field node "predicates"
    let some state := parseSemStateJson exprs.compress predicates.compress
      | throw s!"MOV/EXIT snapshot invalid state at {location}"
    expect ("MOV/EXIT snapshot value/" ++ status)
      (state.exprs.lookupEq (Reg.real64 0)) (some (Term.C64 7))
    expect ("MOV/EXIT snapshot observations/" ++ status) state.predicates observations

private def regressionChecks : Except String Unit := do
  let e ← Json.parse (EBPF.exportEbpfBoundWordsSnapshot EBPF.justTxProgram EBPF.productMetaJson 2000 1024)
  expect "just_tx eBPF status" (← strField e "status") "complete"
  let nodes ← arrField e "nodes"
  let terminalReturns ← nodes.toList.filterMapM fun n => do
    if (← strField n "loc") != "exit" then pure none else do
      let ps ← arrField n "predicates"
      let rs ← ps.toList.filterMapM fun p => do
        if (← strField p "kind") != "ret" then pure none
        else pure (parseTerm (← strField p "term") .w64)
      pure (some rs)
  expect "just_tx eBPF concrete TX return" (terminalReturns.any (·.contains (Term.C64 3))) true
  let r ← Json.parse (RV32IMC.exportRv32BoundWordsSnapshot rvFixture
    "{\"base\":1077412352,\"helperAddress\":1077411840,\"returnAddress\":8192,\"maps\":[{\"mapId\":1077412584,\"keySize\":4,\"valueSize\":8}]}" 60 60)
  expect "just_tx RV frontier status" (← strField r "status") "fail"
  expect "just_tx RV frontier reason" (← strField r "reason") "UnboundTarget"
  let failedRef ← (← field r "failed").getNat?
  let nodes ← arrField r "nodes"
  let failed ← nodes.toList.findM? fun n => do
    pure ((← (← field n "id").getNat?) == failedRef)
  match failed with
  | none => throw s!"just_tx RV frontier: failed reference {failedRef} absent at raw slot 34"
  | some n => expect "just_tx RV frontier slot" (← strField n "loc") "34"

def run : IO UInt32 := do
  let groups : List (String × (Unit → Except String Unit)) := [
    ("eBPF ALU32/64, signed boundaries, MOVSX, END", fun _ => aluChecks),
    ("eBPF all comparisons and JSET", fun _ => jumpChecks),
    ("ST, MEMSX, acquire/release, packet bounds", fun _ => memoryChecks),
    ("atomic old-state RMW, DW carry, rejection domains", fun _ => atomicChecks),
    ("RV32 open/closed M and ISA division policies", fun _ => rvMChecks),
    ("both helper ABIs complete tails and prefix fallback", fun _ => helperChecks),
    ("solve R1-R6, invalid rewrites, explicit/partial theta", fun _ => solverChecks),
    ("raw/canonical operator parameters and numeric results", fun _ => operatorChecks),
    ("alignment collision, ambiguity, complements, swap", fun _ => alignmentChecks),
    ("String FFI semantic states and all-or-nothing rejection", fun _ => ffiChecks),
    ("MOV/EXIT prefix running and complete snapshot protocol", fun _ => snapshotProtocolChecks),
    ("just_tx finite product regressions", fun _ => regressionChecks)]
  for (name, check) in groups do
    match check () with
    | .error detail =>
      IO.eprintln s!"FAIL {name}\n{detail}"
      return 1
    | .ok () => IO.println s!"PASS {name}"
  IO.println "Semantic checks passed. Finite consumer regressions, not general semantic proofs."
  return 0

end SemanticCheck

def main : IO UInt32 := SemanticCheck.run
