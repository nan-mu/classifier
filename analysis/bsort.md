# bsort observation

Observation report for the bsort BPF ELF so a later implementer can compile it. This file does not invent a shared ISA and does not emit a `.alive` module. Conversion result: **NOT CONVERTED**.

## Evidence

- Computed sha256 of `/Volumes/SSD/bs/build/bsort/bpf.o`: `9c477f4bf4cddbf47748c5e7c2154b9f9cd967e57bb09b44d6aaa7e8c63daf18` (`shasum -a 256`). It matches the expected digest.
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -h -S -s -r` and `/opt/homebrew/opt/llvm/bin/llvm-objdump -h -d -r -t`.
- Section bytes of `xdp` re-decoded in this report (file offset `0x40`, size `0x1358`). `.text` is a separate empty section at the same file offset; it is not the program.
- Notes file `/Volumes/SSD/bs/build/bsort/bpf.toml` used only as a side record of the map and the three CO-RE rows. Instruction bytes and CO-RE sites below were checked on the ELF, not copied from the notes as authority.
- Rules actually read are cited by path. Anything not opened is named as unread.

## ELF

- ELF64, little-endian (`EI_DATA` = 1, 2's complement little endian), `ET_REL`, `EM_BPF`, entry `0`, no program headers.
- Executable sections (`SHF_ALLOC|SHF_EXECINSTR`, flags `0x6`):
  - `.text` PROGBITS size **0** (empty). Not the program.
  - `xdp` PROGBITS address 0, file offset `0x40`, size `0x1358` = 4952 bytes, align 8. This is the program.
- Symbol `bsort`: GLOBAL FUNC, section `xdp`, value 0, size 4952. One entry, slot 0.
- `license` PROGBITS size 4, bytes `GPL\0`. Symbol `LICENSE`.
- `.maps` PROGBITS size `0x20`, all zero bytes. Symbol `workload` GLOBAL OBJECT size 32.
- BTF (`.BTF`, magic `0xeb9f`) strings include `xdp_md`, `data`, `data_end`, `workload`, `bsort`, and the source path `bsort.c`. Decoded types:
  - `t17 STRUCT xdp_md`: `data` at bit 0, `data_end` at bit 32, then `data_meta`, `ingress_ifindex`, `rx_queue_index`, `egress_ifindex`, each `__u32`.
  - `t19 FUNC bsort` proto returns `int`, argument `ctx` pointer to `xdp_md`.
  - `t15 VAR workload` linkage 1, type is the anonymous map struct. Field encodings: `type` is a pointer to an array of **1** int (`BPF_MAP_TYPE_HASH` = 1), `max_entries` is a pointer to an array of **2** ints, `key` is a pointer to `__u8`, `value` is a pointer to `struct exec_val` (eight `__u32`, 32 bytes). `t23 DATASEC .maps` places that var at offset 0, size 32.
- No `.rel.xdp`. `llvm-objdump -r -j xdp` prints no relocation records on the program. There is no `R_BPF_64_64` / map-fd patch and no call immediate in the text.

## What is not an instruction operand

Separate these. They are easy to mix up because the object file contains a map and hundreds of relocations.

| Kind | Where | What it is |
| --- | --- | --- |
| Raw object reference | `.rel.debug_addr` | `R_BPF_64_ABS64` against section symbol `xdp` (4), `LICENSE` (1), `workload` (1). Debug address table, not an instruction. |
| Raw object reference | `.rel.BTF` | `R_BPF_64_NODYLD32` at BTF offsets `0x250` (`workload`) and `0x268` (`LICENSE`). Patches BTF variable records, not `xdp`. |
| BTF.ext fixup, not a map index | `.rel.BTF.ext` | 459 × `R_BPF_64_NODYLD32` against section symbol `xdp`. These relocate records inside `.BTF.ext`, not instruction immediates. |
| CO-RE field offset, not XPOST and not a map index | `.BTF.ext` core, printed by `llvm-objdump -d -r` beside three loads | `byte_off` of `struct xdp_md`. See below. The instruction offset field is already the local BTF offset. |
| Map symbol with no use | `.maps` / BTF var `workload` | Hash map, max 2, key 1 byte, value 32 bytes. No `LDDW`, no `PSEUDO_MAP_FD` (src r1), no `PSEUDO_MAP_IDX` (src r5), no helper call. |

CO-RE sites (objdump byte address = slot × 8). All three are `LDX W` from `r1` with immediate 0. Mode is MEM, not a pseudo load:

| Slot | Address | Instruction bytes already say | CO-RE |
| --- | --- | --- | --- |
| 2 | `0x10` | `w3 = *(u32 *)(r1 + 4)` | `xdp_md::data_end` access string `0:1`, type id 17 |
| 3 | `0x18` | `w2 = *(u32 *)(r1 + 0)` | `xdp_md::data` access string `0:0`, type id 17 |
| 13 | `0x68` | `w1 = *(u32 *)(r1 + 4)` | `xdp_md::data_end` access string `0:1`, type id 17 |

Neither `alive2/src/ebpf_decode.cpp` nor `alive2/rocq/upstream/theories/ebpfDecoder.v` applies CO-RE. I found no CO-RE/BTF field walk in those files (the only BTF hits are `CallByBTF` and `PSEUDO_BTF_ID`, neither of which occurs here). For this object the local offsets already match `xdp_md`, so a decoder that ignores the reloc still sees +0 and +4. A different target layout would need a reloc apply step that does not exist in the lifter.

## Entry and shape

- Entry: `bsort` at `xdp` slot 0. No other executable content.
- 619 slots, 619 instructions. No `LDDW` (`opcode 0x18`), so no instruction occupies two slots. `decode_lddw_insn` in `ebpfDecoder.v` is unused for this file.
- No `CALL` (`opcode 0x85` or JMP `src_reg` variant). Helper flag: **no**.
- No backward jump. `jump_target` (`ebpf_decode.cpp` `jump_target`, index+1+off) is in range for every jump, and every offset is positive, so `Lifter::build_blocks` would not set `loop`. Loop flag: **no**.
- Map flag: **present in the ELF, not referenced by any instruction.**
- Last instruction is slot 618 `EXIT` (`0x95`). The slot before it reloads `w0` from the stack.

Opcode counts from the `xdp` bytes:

| Count | Kind | Opcode | C++ `decode_ebpf` | Rocq `decode_insn` |
| ---: | --- | --- | --- | --- |
| 124 | `LDX B MEM` | `0x71` | reject, class not ALU/JMP (`ebpf_decode.cpp` 164–167) | `Pload Byte` (`ebpfDecoder.v` 165–177) |
| 120 | `STX B MEM` | `0x73` | reject, same | `Pstore Byte` from register (181) |
| 93 | `ALU32 LSH K` | `0x64` | `EbAlu::Lsh` W32 (105) | `Palu LSH W32` (69) |
| 93 | `ALU32 OR X` | `0x4c` | `EbAlu::Or` (103) | `Palu OR W32` (67) |
| 76 | `ALU32 MOV X` | `0xbc` | `EbAlu::Mov`, offset 0 (83–85) | `Palu MOV W32` (80–83) |
| 44 | `LDX W MEM` | `0x61` | reject | `Pload Word` |
| 33 | `STX W MEM` | `0x63` | reject | `Pstore Word` |
| 15 | `JMP32 JLE X` | `0xbe` | `EbJmp::Jle` W32 (152) | `Pjmpcmp (LE Unsigned) W32` (154) |
| 4 | `JMP32 JEQ K` | `0x16` | `EbJmp::Jeq` (147) | `Pjmpcmp EQ W32` (146) |
| 4 | `JMP32 JSLT K` | `0xc6` | `EbJmp::Jslt` (155) | `Pjmpcmp (LT Signed) W32` (155) |
| 3 | `JMP32 JLT K` | `0xa6` | `EbJmp::Jlt` (151) | `Pjmpcmp (LT Unsigned) W32` (153) |
| 2 | `ALU32 MOV K` | `0xb4` | `EbAlu::Mov` imm | `Palu MOV W32` imm |
| 2 | `ALU64 MOV X` | `0xbf` | `EbAlu::Mov` W64 | `Palu MOV W64` |
| 2 | `ALU64 ADD K` | `0x07` | `EbAlu::Add` W64 (100) | `Palu ADD W64` (58) |
| 2 | `JMP64 JGT X` | `0x2d` | `EbJmp::Jgt` W64 (149) | `Pjmpcmp (GT Unsigned) W64` (147) |
| 1 | `ALU32 ADD K` | `0x04` | `EbAlu::Add` W32 | `Palu ADD W32` |
| 1 | `JMP64 EXIT` | `0x95` | `EbJmp::Exit` (130–133) | `Pret` (137–138) |

321 of 619 instructions are memory-class. `decode_ebpf` throws `unsupported class` on the first one (slot 1, `0x63`) and never returns a program.

Immediates that matter:

- `ALU32 MOV K`: 0 (slot 0, into `w2`) and 2 (slot 63, into `w1`).
- `ALU32 ADD K`: −7 once (slot 22, `w1 += -7`).
- `ALU64 ADD K`: +8 (slot 5) and +32 (slot 12).
- `ALU32 LSH K`: 8, 16, or 24 only (31 each). All are < 32, so the shift mask does not change them.
- `JMP32` immediates: unsigned `JLT` against −5 (`0xfffffffb`, slot 23), 4 (slot 106), 6 (slot 186); `JEQ` against 2 (slot 66) and 4 (slots 146, 304, 422); signed `JSLT` against 4 (slot 264) and 6 (slots 344, 462, 540).

`llvm-objdump` prints slot 23 as `if w1 < -0x5`. The opcode is unsigned `JLT` (`0xa6` = JMP32 | op `0xa` | src K). The `<` glyph is not signedness. Signed less-than is `0xc6` (`JSLT`), which this file also uses, at the four slots listed above.

## Jump slots

Target = slot + 1 + off16, the same formula as `jump_target` in `alive2/src/ebpf_decode.cpp` (lines 26–31). All 28 land on an instruction. None is a back edge.

| Slot | Kind | off | imm | Target slot |
| ---: | --- | ---: | ---: | ---: |
| 6 | `JMP64_JGT_X` | 610 | 0 | 617 |
| 14 | `JMP64_JGT_X` | 602 | 0 | 617 |
| 23 | `JMP32_JLT_K` | 593 | -5 | 617 |
| 52 | `JMP32_JLE_X` | 10 | 0 | 63 |
| 66 | `JMP32_JEQ_K` | 550 | 2 | 617 |
| 94 | `JMP32_JLE_X` | 10 | 0 | 105 |
| 106 | `JMP32_JLT_K` | 118 | 4 | 225 |
| 134 | `JMP32_JLE_X` | 10 | 0 | 145 |
| 146 | `JMP32_JEQ_K` | 78 | 4 | 225 |
| 174 | `JMP32_JLE_X` | 10 | 0 | 185 |
| 186 | `JMP32_JLT_K` | 38 | 6 | 225 |
| 214 | `JMP32_JLE_X` | 10 | 0 | 225 |
| 252 | `JMP32_JLE_X` | 10 | 0 | 263 |
| 264 | `JMP32_JSLT_K` | 352 | 4 | 617 |
| 292 | `JMP32_JLE_X` | 10 | 0 | 303 |
| 304 | `JMP32_JEQ_K` | 78 | 4 | 383 |
| 332 | `JMP32_JLE_X` | 10 | 0 | 343 |
| 344 | `JMP32_JSLT_K` | 38 | 6 | 383 |
| 372 | `JMP32_JLE_X` | 10 | 0 | 383 |
| 410 | `JMP32_JLE_X` | 10 | 0 | 421 |
| 422 | `JMP32_JEQ_K` | 194 | 4 | 617 |
| 450 | `JMP32_JLE_X` | 10 | 0 | 461 |
| 462 | `JMP32_JSLT_K` | 38 | 6 | 501 |
| 490 | `JMP32_JLE_X` | 10 | 0 | 501 |
| 528 | `JMP32_JLE_X` | 10 | 0 | 539 |
| 540 | `JMP32_JSLT_K` | 76 | 6 | 617 |
| 568 | `JMP32_JLE_X` | 10 | 0 | 579 |
| 606 | `JMP32_JLE_X` | 10 | 0 | 617 |

Fall-through of a conditional is the not-taken edge. Exit targets (617) only execute slot 617 `w0 = *(u32 *)(r10 - 8)` and slot 618 `exit`. There is no jump to 618 itself.

## Memory operands

Bases actually used:

- `r1` (context): three `LDX W`, offsets 0 or 4, the CO-RE loads above. `r1` is then overwritten and never used as a pointer again.
- `r2` (packet cursor): 124 `LDX B` and 120 `STX B`. Displacements are only the integers 4 through 31 inclusive. No halfword, no word, no doubleword on `r2`.
- `r10` (frame pointer): `STX W` / `LDX W` only, displacements −8, −16, −24, −32. No byte stack access. `r10` is never an ALU destination.

Stack roles, from the stores and the reloads that follow them:

- `fp-8`: XDP return word. Slot 1 stores 0. Slot 64 stores 2 after `n` has been accepted. Slot 617 loads it into `w0` on every path that reaches exit, including the early rejects (they jump to 617 and never execute slot 64).
- `fp-16`: the header word `n` (slot 24 stores `w6`). Later gates reload it. Slot 545 also reuses `fp-16` as a byte spill inside the last swap; that is after the last read of `n`.
- `fp-24` and `fp-32`: byte spills during a swap (a zero-extended byte stored as `u32`, reloaded, then stored back as `u8`).

## What the straight-line code is doing

This is an unrolled ascending sort of little-endian `u32` keys, not a loop. The lifter must not invent a loop ISA for it.

1. Store 0 at `fp-8` (default return).
2. Load `data_end` into `w3` and `data` into `w2` (32-bit, so the top half is zero after a zero-extending load).
3. If `(data+8) u> data_end` (slot 6, `JMP64 JGT`), goto 617 and return 0. Otherwise bytes at `data+4..+7` are in range.
4. Those four bytes are assembled with shifts 0/8/16/24 into `w6`. That is an explicit little-endian `u32`, not a `LDXW` of the packet. Then `r3 = data+32`. Reload `data_end` into `w1`. If `(data+32) u> data_end` (slot 14), return 0.
5. `w1 = w6 + (-7)`. If `w1 u< 0xfffffffb` (slot 23), return 0. As unsigned 32-bit arithmetic that accept set is exactly `w6 ∈ {2,3,4,5,6}`. A signed reading of the same immediate (`s< -5`) accepts every `n >= 2` that does not wrap the 32-bit subtract into the signed negatives below −5, including `n = 7` and any larger small `n`. That is the compare that must stay unsigned.
6. Slot 24 saves `n` at `fp-16`. Keys are the six little-endian words at `data+8`, `+12`, `+16`, `+20`, `+24`, `+28` (bytes `+8..+31`). Each compare builds both words the same shift way, then `JMP32 JLE X`: skip the swap when `left u<= right`. The swap writes the eight bytes back individually. So the order is unsigned ascending, and the byte order of each word stays little-endian.
7. Slot 63/64 set the return word to 2. Slot 66: if `n == 2`, goto 617. Further pair compares are skipped by `n u< 4`, `n == 4`, `n u< 6`, and the signed tests `n s< 4` / `n s< 6`. For `n` already in `{2,3,4,5,6}` the signed and unsigned tests against 4 and 6 agree. They do not agree for a high bit set. Keep the opcode (`0xa6` vs `0xc6`).
8. Every path ends at slot 617–618: `w0 = *(u32 *)(fp-8); exit`. Return is 0 if a check failed, else 2, and on the success path the packet bytes `+8..+31` have been reordered in place.

`r0` is a scratch byte register on the swap paths. Only the final load into `w0` is the return value. Early exits must not return whatever `r0` last held.

## Semantic rules read

C++ decoder, `alive2/src/ebpf_decode.cpp` (whole file, 245 lines):

- ALU and ALU64 with op `ADD/OR/LSH/MOV` and offset 0 are accepted. 32-bit vs 64-bit is the class bit (`kAlu` 0x04 vs `kAlu64` 0x07). Immediate source requires the src nibble to be 0 (line 118).
- JMP/JMP32 compares used here (`Jeq`, `Jgt`, `Jlt`, `Jle`, `Jslt`) and `EXIT` are accepted (lines 121–163). `EXIT` must be class JMP (not JMP32), src K, offset 0, dst 0, src reg 0. Slot 618 is `95 00 00 00 00 00 00 00`, which passes.
- Any other class, including every `LDX`/`STX` in this file, hits line 164–167 and throws. There is no load, store, `LDDW`, atomic, or call case in this decoder. Call would also fail: op `0x80` falls into the jump default at line 157.

C++ lifter, `alive2/src/ebpf_lift.cpp`. Read: `eval_op` (27–80), `build_blocks` (214–282), `init_regs` (284–329), `emit` / `emit_alu` / `emit_wide` / `emit_narrow` / `shift` / `emit_cmp` / `arith_op` / `shift_op` / `icmp_cond` (460–694), `concrete` (713–979), `lift_ebpf` (1005–1010). Not a line-by-line reading of the div/mod UB splitting (`emit_divmod`, 593–641); this program has no div or mod.

- `emit_alu` for W32: `trunc` to i32, operate, `zext` to i64 (536–539). W64 `MOV` returns the source value (564–565). W64 `ADD` is `BinOp::Add` on i64 (570, 656–658). `LSH` is `BinOp::Shl` after `And` with 31 or 63 unless `LiftBug::ShiftWithoutMask` (553–558, 669–672). `OR` is `BinOp::Or` (661).
- `emit_cmp`: W32 truncates both sides; an immediate is `c32(uint32_t(imm))`, so −5 becomes `0xfffffffb`, not a sign-extended i64 (643–653). Condition codes: `Jeq→EQ`, `Jgt→UGT`, `Jlt→ULT`, `Jle→ULE`, `Jslt→SLT` (679–686). Taken edge is `succ[0]` (the jump target), not-taken is `succ[1]` (502–503).
- `EXIT` is `Return` of `r0` (496–497).
- `init_regs` for the non-zero mode poisons `r1` and `r10` and marks them `RegOrigin::Pointer` (315–321). `pointer_alu` / `pointer_jmp` only set `EbSite::pointer_use` (347–374, 471, 495). They still emit integer `BinOp` / `ICmp`. There is no memory instruction builder anywhere in `emit`.
- `concrete()`'s `eval_op` implements `Add`, `Sub`, `And`, `UDiv`, `SDiv`, `ICmp EQ`, `ICmp UGT` only (71–78, 879–922). `Or`, `Shl`, `ULE`, `ULT`, and `SLT` take the `stop_unsupported` path. A `MemInstr` would set `MemorySummary::Changed` and then stop unsupported (962–965). This program would not get that far, because decode throws first.

Rocq syntax and decoder, read in full:

- `alive2/rocq/upstream/theories/ebpfSyntax.v`: `Pload` / `Pstore` (233–234), `Palu` (238), `Pjmpcmp` (242), `Pret` (244), `pseudo_ptr_ty` including map fd and map index (214–222). `R10` is the frame pointer (line 21).
- `alive2/rocq/upstream/theories/ebpfDecoder.v`: `decode_insn` ALU cases 57–90, jump cases 115–159, MEM-mode load/store 161–183, `decode_lddw_insn` 235–246 (`R1` = `PSEUDO_MAP_FD`, `R5` = `PSEUDO_MAP_IDX`). `find_instr` only treats opcode `0x18` as two slots (268–276). This program never takes that branch.

Rocq small-step, `alive2/rocq/upstream/theories/ebpfBinSem.v`, the definitions below. I did not read the atomic block (`exec_atomic_store` onward, about line 1121) or the commented-out spilling helpers.

- `eval_alu32` (332–353): `ADD`/`OR`/`LSH`/`MOV` on the low 32 bits, result `Val.longofintu` (zero-extend). `LSH` masks the amount with `eval_shift_mask W32` = `and 31` (236–238, 343).
- `eval_alu64` (355–375): `ADD` is `Val.addl`, `MOV` returns `src`. `eval_val_int` sign-extends a 64-bit immediate (108–116). The two `ALU64 ADD K` immediates are +8 and +32, so sign-extend and zero-extend match.
- `exec_alu` (377–390) writes the destination and steps PC by one. The same-register `SUB`/`XOR` shortcut does not apply to any instruction here.
- `eval_cmp32` / `eval_cmp64` (412–444) and the comment table at 392–410: `JGT`/`JLT`/`JLE` unsigned, `JSLT` signed. `exec_jmpcmp` (484–498) adds `off` to PC when the condition is true, otherwise falls through, then `nextinstr`. `eval_cmp_static` (452–482) does not fold any immediate in this program (the special cases are 0, −1, `min_signed`, `max_signed`).
- `exec_load` (575–589): if the base is `Vlong`, `cast_i2p` of `base + signed(offset)` through `addr_map` (512–522); if the base is `Vptr`, `Val.offset_ptr`. Then `load` of `Mint8unsigned` or `Mint32` (560–567) and `load_value_casting` zero-extends a `Vint` to `Vlong` (569–573). Failure is `Stuck`.
- `exec_store` (642–646): **only** `Val.offset_ptr` on the base register. It does not call `cast_i2p`. `store` of a byte uses `Mint8unsigned` (633–635). A `Vlong` base becomes a non-pointer under `offset_ptr`, `storev_unaligned` returns `None` (554–557), and the outcome is `Stuck`.
- `initial_lst_state` (993–1007): `R1` is `Vptr ctx 0`, `R10` is `Vptr stk (Ptrofs.repr 512)`, other registers `Vundef`. `bpf_stack_size` is 512 (line 720). Stack slots at `512-8`, `512-16`, `512-24`, `512-32` sit inside `[0, 512)`.
- `exec_ret` the live definition (819–839), not the commented one above it: empty call stack sets `PC` to `Vnullptr` and leaves `R0`. `final_lst_state` (1010–1017) requires `R0` to be `Vlong` or `Vptr` and `R10` still the original stack pointer.
- `exec_instr` (888–905): `Pcall` other than `CallInternal` is the catch-all `Stuck` at 904. External calls are a separate `step` clause (979–991) and need a call instruction. This program has none. `Plddw` of a map pseudo goes through `exec_lddw` (648–659); unused here.

`alive2/rocq/upstream/theories/ebpfState.v` was read. It defines `regset`, `outcome` (`Next` / `Stuck`), and `addr_region` (`base_blk`, `size_blk`, `base_addr`). It does not define instruction behavior.

Not read, so not used as rules: `SCLanguage.v`, `GlobalSem.v`, `CMemoryModel.v`, `Nondeterminism.v`, `Extraction.v`, and the CompCert `Val.offset_ptr` / `Mem.storebytes` implementations beyond what `ebpfBinSem.v` states (non-`Vptr` addresses do not store).

## IR mapping against the C++ lifter only

The lifter never sees this program: `decode_ebpf` throws at slot 1. The mapping below is what `emit_alu` / `emit_cmp` / `EXIT` would produce for the ALU and jump opcodes **if** the memory instructions were absent. It is not a conversion.

| Instruction | Alive2 IR the lifter actually builds | Notes for this file |
| --- | --- | --- |
| `ALU32 ADD/OR/MOV/LSH` | `trunc` i32, then `BinOp::Add` / `Or` / the src itself / `Shl`, then `zext` i64 | Shift amount `and 31`. Immediates zero-extended to 64, then truncated. −7 and the `JLT` immediate are not sign-extended before the 32-bit op. |
| `ALU64 MOV X` | copy the i64 value | Slots 4 and 11 (`r4 = r2`, `r3 = r2`). No truncation. |
| `ALU64 ADD K` | `BinOp::Add` i64, sign-extended immediate | +8 and +32. |
| `JMP32 JEQ/JLT/JLE/JSLT` | `trunc` both sides, `ICmp` `EQ`/`ULT`/`ULE`/`SLT`, `Branch` | Immediate is a 32-bit constant of the raw imm bits. |
| `JMP64 JGT X` | `ICmp UGT` on the full i64, `Branch` | Slots 6 and 14. Correct only if both pointers were zero-extended from the `u32` loads. The lifter has no load, so those values do not exist. |
| `EXIT` | `Return` i64 of `r0` | |
| `LDX` / `STX` | no constructor | `emit` rejects a non-jump in the middle of a block only after decode. Decode already failed. |

`lift_ebpf` (`ebpf_lift.cpp` 1005–1010) returns `LiftInfo` with a CFG string and a `loop` flag. It does not build a packet object, a stack object, a map, or a helper. `r1`/`r10` pointer origin is a poison value plus a boolean on the site, not a memory model.

There is no `.alive` text for this program. Do not treat "memory class unsupported" as a successful conversion.

## Requirements for a later compiler

- **Packet.** `r1` starts as `xdp_md*`. Three aligned `u32` loads at +0 and +4, zero-extended. CO-RE `byte_off` for `data` and `data_end`; on this object the bytes already hold those offsets. `r2` is that `data` integer. Byte loads and stores at `data+4..+31` must hit the packet, little-endian assembly is done by the shifts (do not replace them with a host-endian `u32` load unless the target is little-endian and you prove it).
- **Bounds the program itself checks.** Unsigned 64-bit `>` of `data+8` and `data+32` against `data_end`. Nothing else. A model that allows the byte stores without those checks is not this program. A model that `Stuck`s the stores is also not an implementation.
- **Stack.** 512-byte frame, `r10` at the high end, as in `initial_lst_state`. Only the four negative word slots above. `fp-8` is the return word.
- **Helpers.** None.
- **Maps.** Do not emit a map lookup. `workload` is an unused HASH map (type 1, 2 entries, key 1, value 32) described by BTF. No instruction operand is a map fd, a map index, or an `LDDW` pseudo.
- **Loops.** None. 28 forward edges. Do not encode a back-edge or a fixed-point.
- **Calls / `LDDW`.** None. Do not reserve a second slot.
- **Endian.** ELF and instruction encoding are little-endian. The key assembly is explicit LE. The `xdp_md` loads are native `u32`.
- **Rocq store gap to close or avoid.** `exec_load` can turn the `Vlong` from the `data` load into a pointer via `cast_i2p`. `exec_store` cannot. All 120 packet byte stores are `Stuck` in the semantics as written, even after a correct `addr_map` entry for the packet. Stack stores can succeed because `R10` is a `Vptr`. Copying `exec_load`'s `cast_i2p` into `exec_store` is one fix; giving `r2` a `Vptr` before the first store is another. Either way it is not in the code I read.

## Proof coverage

`alive2/rocq/upstream/validator/Validation.v` was read from the trace checker through `compare_trace_at_pc` (about lines 68–147) and the `create_bpf_maps` / stack `addr_map` setup (221–279). `semantics_validation` walks `exec_instr` and compares r0–r9 (and the following register, the conjunction continues past the lines quoted) against a concrete `int64` trace. `Vundef` compares equal. Final success looks at `R0` only (`compare_final_state`). I did not find a theorem, and this file is a checker, not a proof that the sort is sorted. There is no bsort-specific proof in the `.v` files that were listed.

Nothing I read proves: the unsigned accept set `{2,3,4,5,6}`, that the byte swaps sort, that packet stores commute with the stack spills, or that CO-RE offsets match `xdp_md`. The C++ concrete interpreter cannot even evaluate `Or` and `Shl`, which are 186 of the ALU instructions.

## Counterexample

Packet length 32 (`data_end = data+32`), so both bound checks pass. Little-endian `n` at `data+4` is 7. Two keys are enough to observe a write; put `0x00000002` at `data+8` and `0x00000001` at `data+12` (bytes `02 00 00 00 01 00 00 00`).

- Real program: slot 23's unsigned test rejects `n = 7` (`7-7 = 0`, and `0 u< 0xfffffffb`), jumps to 617, returns `r0 = 0`, and does not swap. Keys stay `2, 1`.
- If `0xa6` is lifted as signed `JSLT` against −5: `(7-7) s< -5` is false, the program stores return 2 and swaps. `r0 = 2` and the first key becomes 1. That pair of observations separates the unsigned opcode from the signed one `llvm-objdump`'s `<` glyph suggests.
- If packet stores are dropped or `Stuck` (the Rocq `exec_store` behavior on a `Vlong` `r2`, or a register-only C++ lift): either the run never reaches `exit`, or it returns 2 while `data+8` is still 2. For `n = 3` (which the unsigned test accepts) the sorted image is `1, 2` at `data+8` and `data+12`, with `r0 = 2`. A trace that only checks `r0` (`compare_final_state`) cannot see the missed swap.

A second, smaller check: `data_end = data+8` with any `n`. Slot 6 must return 0. Slot 14 must also return 0 when `data+8 <= data_end < data+32`. Bytes at `data+8` and above must be unchanged. The header loads at `data+4..+7` are legal on the first path and must not be reported as faults.

## Real disassembly

Command: `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r -j xdp /Volumes/SSD/bs/build/bsort/bpf.o`.
Instruction lines in that listing: 619. Slot count from the section bytes: 619. CO-RE notes are indented under slots 2, 3, and 13 and are not instructions.

```
Disassembly of section xdp:

0000000000000000 <bsort>:
       0:	b4 02 00 00 00 00 00 00	w2 = 0x0
       1:	63 2a f8 ff 00 00 00 00	*(u32 *)(r10 - 0x8) = w2
       2:	61 13 04 00 00 00 00 00	w3 = *(u32 *)(r1 + 0x4)
		0000000000000010:  CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)
       3:	61 12 00 00 00 00 00 00	w2 = *(u32 *)(r1 + 0x0)
		0000000000000018:  CO-RE <byte_off> [17] struct xdp_md::data (0:0)
       4:	bf 24 00 00 00 00 00 00	r4 = r2
       5:	07 04 00 00 08 00 00 00	r4 += 0x8
       6:	2d 34 62 02 00 00 00 00	if r4 > r3 goto +0x262 <L14>
       7:	71 24 05 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x5)
       8:	71 20 04 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x4)
       9:	71 25 06 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x6)
      10:	71 26 07 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x7)
      11:	bf 23 00 00 00 00 00 00	r3 = r2
      12:	07 03 00 00 20 00 00 00	r3 += 0x20
      13:	61 11 04 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x4)
		0000000000000068:  CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)
      14:	2d 13 5a 02 00 00 00 00	if r3 > r1 goto +0x25a <L14>
      15:	64 04 00 00 08 00 00 00	w4 <<= 0x8
      16:	4c 04 00 00 00 00 00 00	w4 |= w0
      17:	64 05 00 00 10 00 00 00	w5 <<= 0x10
      18:	64 06 00 00 18 00 00 00	w6 <<= 0x18
      19:	4c 56 00 00 00 00 00 00	w6 |= w5
      20:	4c 46 00 00 00 00 00 00	w6 |= w4
      21:	bc 61 00 00 00 00 00 00	w1 = w6
      22:	04 01 00 00 f9 ff ff ff	w1 += -0x7
      23:	a6 01 51 02 fb ff ff ff	if w1 < -0x5 goto +0x251 <L14>
      24:	63 6a f0 ff 00 00 00 00	*(u32 *)(r10 - 0x10) = w6
      25:	71 21 08 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x8)
      26:	71 26 09 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x9)
      27:	63 6a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w6
      28:	64 06 00 00 08 00 00 00	w6 <<= 0x8
      29:	63 1a f8 ff 00 00 00 00	*(u32 *)(r10 - 0x8) = w1
      30:	4c 16 00 00 00 00 00 00	w6 |= w1
      31:	71 20 0a 00 00 00 00 00	w0 = *(u8 *)(r2 + 0xa)
      32:	bc 03 00 00 00 00 00 00	w3 = w0
      33:	64 03 00 00 10 00 00 00	w3 <<= 0x10
      34:	4c 36 00 00 00 00 00 00	w6 |= w3
      35:	71 25 0c 00 00 00 00 00	w5 = *(u8 *)(r2 + 0xc)
      36:	71 21 0d 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xd)
      37:	bc 17 00 00 00 00 00 00	w7 = w1
      38:	64 07 00 00 08 00 00 00	w7 <<= 0x8
      39:	4c 57 00 00 00 00 00 00	w7 |= w5
      40:	71 28 0e 00 00 00 00 00	w8 = *(u8 *)(r2 + 0xe)
      41:	bc 83 00 00 00 00 00 00	w3 = w8
      42:	64 03 00 00 10 00 00 00	w3 <<= 0x10
      43:	4c 37 00 00 00 00 00 00	w7 |= w3
      44:	71 29 0f 00 00 00 00 00	w9 = *(u8 *)(r2 + 0xf)
      45:	bc 93 00 00 00 00 00 00	w3 = w9
      46:	64 03 00 00 18 00 00 00	w3 <<= 0x18
      47:	4c 37 00 00 00 00 00 00	w7 |= w3
      48:	71 24 0b 00 00 00 00 00	w4 = *(u8 *)(r2 + 0xb)
      49:	bc 43 00 00 00 00 00 00	w3 = w4
      50:	64 03 00 00 18 00 00 00	w3 <<= 0x18
      51:	4c 36 00 00 00 00 00 00	w6 |= w3
      52:	be 76 0a 00 00 00 00 00	if w6 <= w7 goto +0xa <L0>
      53:	73 42 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w4
      54:	73 02 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w0
      55:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
      56:	73 32 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w3
      57:	61 a3 f8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x8)
      58:	73 32 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w3
      59:	73 92 0b 00 00 00 00 00	*(u8 *)(r2 + 0xb) = w9
      60:	73 82 0a 00 00 00 00 00	*(u8 *)(r2 + 0xa) = w8
      61:	73 12 09 00 00 00 00 00	*(u8 *)(r2 + 0x9) = w1
      62:	73 52 08 00 00 00 00 00	*(u8 *)(r2 + 0x8) = w5
<L0>:
      63:	b4 01 00 00 02 00 00 00	w1 = 0x2
      64:	63 1a f8 ff 00 00 00 00	*(u32 *)(r10 - 0x8) = w1
      65:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
      66:	16 01 26 02 02 00 00 00	if w1 == 0x2 goto +0x226 <L14>
      67:	71 21 0c 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xc)
      68:	71 27 0d 00 00 00 00 00	w7 = *(u8 *)(r2 + 0xd)
      69:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
      70:	64 07 00 00 08 00 00 00	w7 <<= 0x8
      71:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
      72:	4c 17 00 00 00 00 00 00	w7 |= w1
      73:	71 26 0e 00 00 00 00 00	w6 = *(u8 *)(r2 + 0xe)
      74:	bc 61 00 00 00 00 00 00	w1 = w6
      75:	64 01 00 00 10 00 00 00	w1 <<= 0x10
      76:	4c 17 00 00 00 00 00 00	w7 |= w1
      77:	71 25 10 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x10)
      78:	71 20 11 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x11)
      79:	bc 08 00 00 00 00 00 00	w8 = w0
      80:	64 08 00 00 08 00 00 00	w8 <<= 0x8
      81:	4c 58 00 00 00 00 00 00	w8 |= w5
      82:	71 29 12 00 00 00 00 00	w9 = *(u8 *)(r2 + 0x12)
      83:	bc 91 00 00 00 00 00 00	w1 = w9
      84:	64 01 00 00 10 00 00 00	w1 <<= 0x10
      85:	4c 18 00 00 00 00 00 00	w8 |= w1
      86:	71 21 13 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x13)
      87:	bc 13 00 00 00 00 00 00	w3 = w1
      88:	64 03 00 00 18 00 00 00	w3 <<= 0x18
      89:	4c 38 00 00 00 00 00 00	w8 |= w3
      90:	71 24 0f 00 00 00 00 00	w4 = *(u8 *)(r2 + 0xf)
      91:	bc 43 00 00 00 00 00 00	w3 = w4
      92:	64 03 00 00 18 00 00 00	w3 <<= 0x18
      93:	4c 37 00 00 00 00 00 00	w7 |= w3
      94:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L1>
      95:	73 42 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w4
      96:	73 62 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w6
      97:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
      98:	73 32 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w3
      99:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     100:	73 32 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w3
     101:	73 12 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w1
     102:	73 92 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w9
     103:	73 02 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w0
     104:	73 52 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w5
<L1>:
     105:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
     106:	a6 01 76 00 04 00 00 00	if w1 < 0x4 goto +0x76 <L4>
     107:	71 21 10 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x10)
     108:	71 27 11 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x11)
     109:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     110:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     111:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     112:	4c 17 00 00 00 00 00 00	w7 |= w1
     113:	71 26 12 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x12)
     114:	bc 63 00 00 00 00 00 00	w3 = w6
     115:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     116:	4c 37 00 00 00 00 00 00	w7 |= w3
     117:	71 25 14 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x14)
     118:	71 21 15 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x15)
     119:	bc 18 00 00 00 00 00 00	w8 = w1
     120:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     121:	4c 58 00 00 00 00 00 00	w8 |= w5
     122:	71 29 16 00 00 00 00 00	w9 = *(u8 *)(r2 + 0x16)
     123:	bc 93 00 00 00 00 00 00	w3 = w9
     124:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     125:	4c 38 00 00 00 00 00 00	w8 |= w3
     126:	71 20 17 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x17)
     127:	bc 03 00 00 00 00 00 00	w3 = w0
     128:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     129:	4c 38 00 00 00 00 00 00	w8 |= w3
     130:	71 24 13 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x13)
     131:	bc 43 00 00 00 00 00 00	w3 = w4
     132:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     133:	4c 37 00 00 00 00 00 00	w7 |= w3
     134:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L2>
     135:	73 42 17 00 00 00 00 00	*(u8 *)(r2 + 0x17) = w4
     136:	73 62 16 00 00 00 00 00	*(u8 *)(r2 + 0x16) = w6
     137:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     138:	73 32 15 00 00 00 00 00	*(u8 *)(r2 + 0x15) = w3
     139:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     140:	73 32 14 00 00 00 00 00	*(u8 *)(r2 + 0x14) = w3
     141:	73 02 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w0
     142:	73 92 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w9
     143:	73 12 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w1
     144:	73 52 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w5
<L2>:
     145:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
     146:	16 01 4e 00 04 00 00 00	if w1 == 0x4 goto +0x4e <L4>
     147:	71 21 14 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x14)
     148:	71 27 15 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x15)
     149:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     150:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     151:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     152:	4c 17 00 00 00 00 00 00	w7 |= w1
     153:	71 26 16 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x16)
     154:	bc 63 00 00 00 00 00 00	w3 = w6
     155:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     156:	4c 37 00 00 00 00 00 00	w7 |= w3
     157:	71 25 18 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x18)
     158:	71 21 19 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x19)
     159:	bc 18 00 00 00 00 00 00	w8 = w1
     160:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     161:	4c 58 00 00 00 00 00 00	w8 |= w5
     162:	71 29 1a 00 00 00 00 00	w9 = *(u8 *)(r2 + 0x1a)
     163:	bc 93 00 00 00 00 00 00	w3 = w9
     164:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     165:	4c 38 00 00 00 00 00 00	w8 |= w3
     166:	71 20 1b 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x1b)
     167:	bc 03 00 00 00 00 00 00	w3 = w0
     168:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     169:	4c 38 00 00 00 00 00 00	w8 |= w3
     170:	71 24 17 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x17)
     171:	bc 43 00 00 00 00 00 00	w3 = w4
     172:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     173:	4c 37 00 00 00 00 00 00	w7 |= w3
     174:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L3>
     175:	73 42 1b 00 00 00 00 00	*(u8 *)(r2 + 0x1b) = w4
     176:	73 62 1a 00 00 00 00 00	*(u8 *)(r2 + 0x1a) = w6
     177:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     178:	73 32 19 00 00 00 00 00	*(u8 *)(r2 + 0x19) = w3
     179:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     180:	73 32 18 00 00 00 00 00	*(u8 *)(r2 + 0x18) = w3
     181:	73 02 17 00 00 00 00 00	*(u8 *)(r2 + 0x17) = w0
     182:	73 92 16 00 00 00 00 00	*(u8 *)(r2 + 0x16) = w9
     183:	73 12 15 00 00 00 00 00	*(u8 *)(r2 + 0x15) = w1
     184:	73 52 14 00 00 00 00 00	*(u8 *)(r2 + 0x14) = w5
<L3>:
     185:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
     186:	a6 01 26 00 06 00 00 00	if w1 < 0x6 goto +0x26 <L4>
     187:	71 21 18 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x18)
     188:	71 27 19 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x19)
     189:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     190:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     191:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     192:	4c 17 00 00 00 00 00 00	w7 |= w1
     193:	71 26 1a 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x1a)
     194:	bc 63 00 00 00 00 00 00	w3 = w6
     195:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     196:	4c 37 00 00 00 00 00 00	w7 |= w3
     197:	71 25 1c 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x1c)
     198:	71 21 1d 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x1d)
     199:	bc 18 00 00 00 00 00 00	w8 = w1
     200:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     201:	4c 58 00 00 00 00 00 00	w8 |= w5
     202:	71 29 1e 00 00 00 00 00	w9 = *(u8 *)(r2 + 0x1e)
     203:	bc 93 00 00 00 00 00 00	w3 = w9
     204:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     205:	4c 38 00 00 00 00 00 00	w8 |= w3
     206:	71 20 1f 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x1f)
     207:	bc 03 00 00 00 00 00 00	w3 = w0
     208:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     209:	4c 38 00 00 00 00 00 00	w8 |= w3
     210:	71 24 1b 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x1b)
     211:	bc 43 00 00 00 00 00 00	w3 = w4
     212:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     213:	4c 37 00 00 00 00 00 00	w7 |= w3
     214:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L4>
     215:	73 42 1f 00 00 00 00 00	*(u8 *)(r2 + 0x1f) = w4
     216:	73 62 1e 00 00 00 00 00	*(u8 *)(r2 + 0x1e) = w6
     217:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     218:	73 32 1d 00 00 00 00 00	*(u8 *)(r2 + 0x1d) = w3
     219:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     220:	73 32 1c 00 00 00 00 00	*(u8 *)(r2 + 0x1c) = w3
     221:	73 02 1b 00 00 00 00 00	*(u8 *)(r2 + 0x1b) = w0
     222:	73 92 1a 00 00 00 00 00	*(u8 *)(r2 + 0x1a) = w9
     223:	73 12 19 00 00 00 00 00	*(u8 *)(r2 + 0x19) = w1
     224:	73 52 18 00 00 00 00 00	*(u8 *)(r2 + 0x18) = w5
<L4>:
     225:	71 21 08 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x8)
     226:	71 27 09 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x9)
     227:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     228:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     229:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     230:	4c 17 00 00 00 00 00 00	w7 |= w1
     231:	71 26 0a 00 00 00 00 00	w6 = *(u8 *)(r2 + 0xa)
     232:	bc 63 00 00 00 00 00 00	w3 = w6
     233:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     234:	4c 37 00 00 00 00 00 00	w7 |= w3
     235:	71 25 0c 00 00 00 00 00	w5 = *(u8 *)(r2 + 0xc)
     236:	71 21 0d 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xd)
     237:	bc 18 00 00 00 00 00 00	w8 = w1
     238:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     239:	4c 58 00 00 00 00 00 00	w8 |= w5
     240:	71 29 0e 00 00 00 00 00	w9 = *(u8 *)(r2 + 0xe)
     241:	bc 93 00 00 00 00 00 00	w3 = w9
     242:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     243:	4c 38 00 00 00 00 00 00	w8 |= w3
     244:	71 20 0f 00 00 00 00 00	w0 = *(u8 *)(r2 + 0xf)
     245:	bc 03 00 00 00 00 00 00	w3 = w0
     246:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     247:	4c 38 00 00 00 00 00 00	w8 |= w3
     248:	71 24 0b 00 00 00 00 00	w4 = *(u8 *)(r2 + 0xb)
     249:	bc 43 00 00 00 00 00 00	w3 = w4
     250:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     251:	4c 37 00 00 00 00 00 00	w7 |= w3
     252:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L5>
     253:	73 42 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w4
     254:	73 62 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w6
     255:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     256:	73 32 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w3
     257:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     258:	73 32 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w3
     259:	73 02 0b 00 00 00 00 00	*(u8 *)(r2 + 0xb) = w0
     260:	73 92 0a 00 00 00 00 00	*(u8 *)(r2 + 0xa) = w9
     261:	73 12 09 00 00 00 00 00	*(u8 *)(r2 + 0x9) = w1
     262:	73 52 08 00 00 00 00 00	*(u8 *)(r2 + 0x8) = w5
<L5>:
     263:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
     264:	c6 01 60 01 04 00 00 00	if w1 s< 0x4 goto +0x160 <L14>
     265:	71 21 0c 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xc)
     266:	71 27 0d 00 00 00 00 00	w7 = *(u8 *)(r2 + 0xd)
     267:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     268:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     269:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     270:	4c 17 00 00 00 00 00 00	w7 |= w1
     271:	71 26 0e 00 00 00 00 00	w6 = *(u8 *)(r2 + 0xe)
     272:	bc 63 00 00 00 00 00 00	w3 = w6
     273:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     274:	4c 37 00 00 00 00 00 00	w7 |= w3
     275:	71 25 10 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x10)
     276:	71 21 11 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x11)
     277:	bc 18 00 00 00 00 00 00	w8 = w1
     278:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     279:	4c 58 00 00 00 00 00 00	w8 |= w5
     280:	71 29 12 00 00 00 00 00	w9 = *(u8 *)(r2 + 0x12)
     281:	bc 93 00 00 00 00 00 00	w3 = w9
     282:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     283:	4c 38 00 00 00 00 00 00	w8 |= w3
     284:	71 20 13 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x13)
     285:	bc 03 00 00 00 00 00 00	w3 = w0
     286:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     287:	4c 38 00 00 00 00 00 00	w8 |= w3
     288:	71 24 0f 00 00 00 00 00	w4 = *(u8 *)(r2 + 0xf)
     289:	bc 43 00 00 00 00 00 00	w3 = w4
     290:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     291:	4c 37 00 00 00 00 00 00	w7 |= w3
     292:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L6>
     293:	73 42 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w4
     294:	73 62 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w6
     295:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     296:	73 32 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w3
     297:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     298:	73 32 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w3
     299:	73 02 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w0
     300:	73 92 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w9
     301:	73 12 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w1
     302:	73 52 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w5
<L6>:
     303:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
     304:	16 01 4e 00 04 00 00 00	if w1 == 0x4 goto +0x4e <L8>
     305:	71 21 10 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x10)
     306:	71 27 11 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x11)
     307:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     308:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     309:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     310:	4c 17 00 00 00 00 00 00	w7 |= w1
     311:	71 26 12 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x12)
     312:	bc 63 00 00 00 00 00 00	w3 = w6
     313:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     314:	4c 37 00 00 00 00 00 00	w7 |= w3
     315:	71 25 14 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x14)
     316:	71 21 15 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x15)
     317:	bc 18 00 00 00 00 00 00	w8 = w1
     318:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     319:	4c 58 00 00 00 00 00 00	w8 |= w5
     320:	71 29 16 00 00 00 00 00	w9 = *(u8 *)(r2 + 0x16)
     321:	bc 93 00 00 00 00 00 00	w3 = w9
     322:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     323:	4c 38 00 00 00 00 00 00	w8 |= w3
     324:	71 20 17 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x17)
     325:	bc 03 00 00 00 00 00 00	w3 = w0
     326:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     327:	4c 38 00 00 00 00 00 00	w8 |= w3
     328:	71 24 13 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x13)
     329:	bc 43 00 00 00 00 00 00	w3 = w4
     330:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     331:	4c 37 00 00 00 00 00 00	w7 |= w3
     332:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L7>
     333:	73 42 17 00 00 00 00 00	*(u8 *)(r2 + 0x17) = w4
     334:	73 62 16 00 00 00 00 00	*(u8 *)(r2 + 0x16) = w6
     335:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     336:	73 32 15 00 00 00 00 00	*(u8 *)(r2 + 0x15) = w3
     337:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     338:	73 32 14 00 00 00 00 00	*(u8 *)(r2 + 0x14) = w3
     339:	73 02 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w0
     340:	73 92 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w9
     341:	73 12 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w1
     342:	73 52 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w5
<L7>:
     343:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
     344:	c6 01 26 00 06 00 00 00	if w1 s< 0x6 goto +0x26 <L8>
     345:	71 21 14 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x14)
     346:	71 27 15 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x15)
     347:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     348:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     349:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     350:	4c 17 00 00 00 00 00 00	w7 |= w1
     351:	71 26 16 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x16)
     352:	bc 63 00 00 00 00 00 00	w3 = w6
     353:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     354:	4c 37 00 00 00 00 00 00	w7 |= w3
     355:	71 25 18 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x18)
     356:	71 21 19 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x19)
     357:	bc 18 00 00 00 00 00 00	w8 = w1
     358:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     359:	4c 58 00 00 00 00 00 00	w8 |= w5
     360:	71 29 1a 00 00 00 00 00	w9 = *(u8 *)(r2 + 0x1a)
     361:	bc 93 00 00 00 00 00 00	w3 = w9
     362:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     363:	4c 38 00 00 00 00 00 00	w8 |= w3
     364:	71 20 1b 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x1b)
     365:	bc 03 00 00 00 00 00 00	w3 = w0
     366:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     367:	4c 38 00 00 00 00 00 00	w8 |= w3
     368:	71 24 17 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x17)
     369:	bc 43 00 00 00 00 00 00	w3 = w4
     370:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     371:	4c 37 00 00 00 00 00 00	w7 |= w3
     372:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L8>
     373:	73 42 1b 00 00 00 00 00	*(u8 *)(r2 + 0x1b) = w4
     374:	73 62 1a 00 00 00 00 00	*(u8 *)(r2 + 0x1a) = w6
     375:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     376:	73 32 19 00 00 00 00 00	*(u8 *)(r2 + 0x19) = w3
     377:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     378:	73 32 18 00 00 00 00 00	*(u8 *)(r2 + 0x18) = w3
     379:	73 02 17 00 00 00 00 00	*(u8 *)(r2 + 0x17) = w0
     380:	73 92 16 00 00 00 00 00	*(u8 *)(r2 + 0x16) = w9
     381:	73 12 15 00 00 00 00 00	*(u8 *)(r2 + 0x15) = w1
     382:	73 52 14 00 00 00 00 00	*(u8 *)(r2 + 0x14) = w5
<L8>:
     383:	71 21 08 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x8)
     384:	71 27 09 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x9)
     385:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     386:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     387:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     388:	4c 17 00 00 00 00 00 00	w7 |= w1
     389:	71 26 0a 00 00 00 00 00	w6 = *(u8 *)(r2 + 0xa)
     390:	bc 63 00 00 00 00 00 00	w3 = w6
     391:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     392:	4c 37 00 00 00 00 00 00	w7 |= w3
     393:	71 25 0c 00 00 00 00 00	w5 = *(u8 *)(r2 + 0xc)
     394:	71 21 0d 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xd)
     395:	bc 18 00 00 00 00 00 00	w8 = w1
     396:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     397:	4c 58 00 00 00 00 00 00	w8 |= w5
     398:	71 29 0e 00 00 00 00 00	w9 = *(u8 *)(r2 + 0xe)
     399:	bc 93 00 00 00 00 00 00	w3 = w9
     400:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     401:	4c 38 00 00 00 00 00 00	w8 |= w3
     402:	71 20 0f 00 00 00 00 00	w0 = *(u8 *)(r2 + 0xf)
     403:	bc 03 00 00 00 00 00 00	w3 = w0
     404:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     405:	4c 38 00 00 00 00 00 00	w8 |= w3
     406:	71 24 0b 00 00 00 00 00	w4 = *(u8 *)(r2 + 0xb)
     407:	bc 43 00 00 00 00 00 00	w3 = w4
     408:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     409:	4c 37 00 00 00 00 00 00	w7 |= w3
     410:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L9>
     411:	73 42 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w4
     412:	73 62 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w6
     413:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     414:	73 32 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w3
     415:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     416:	73 32 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w3
     417:	73 02 0b 00 00 00 00 00	*(u8 *)(r2 + 0xb) = w0
     418:	73 92 0a 00 00 00 00 00	*(u8 *)(r2 + 0xa) = w9
     419:	73 12 09 00 00 00 00 00	*(u8 *)(r2 + 0x9) = w1
     420:	73 52 08 00 00 00 00 00	*(u8 *)(r2 + 0x8) = w5
<L9>:
     421:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
     422:	16 01 c2 00 04 00 00 00	if w1 == 0x4 goto +0xc2 <L14>
     423:	71 21 0c 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xc)
     424:	71 27 0d 00 00 00 00 00	w7 = *(u8 *)(r2 + 0xd)
     425:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     426:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     427:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     428:	4c 17 00 00 00 00 00 00	w7 |= w1
     429:	71 26 0e 00 00 00 00 00	w6 = *(u8 *)(r2 + 0xe)
     430:	bc 63 00 00 00 00 00 00	w3 = w6
     431:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     432:	4c 37 00 00 00 00 00 00	w7 |= w3
     433:	71 25 10 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x10)
     434:	71 21 11 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x11)
     435:	bc 18 00 00 00 00 00 00	w8 = w1
     436:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     437:	4c 58 00 00 00 00 00 00	w8 |= w5
     438:	71 29 12 00 00 00 00 00	w9 = *(u8 *)(r2 + 0x12)
     439:	bc 93 00 00 00 00 00 00	w3 = w9
     440:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     441:	4c 38 00 00 00 00 00 00	w8 |= w3
     442:	71 20 13 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x13)
     443:	bc 03 00 00 00 00 00 00	w3 = w0
     444:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     445:	4c 38 00 00 00 00 00 00	w8 |= w3
     446:	71 24 0f 00 00 00 00 00	w4 = *(u8 *)(r2 + 0xf)
     447:	bc 43 00 00 00 00 00 00	w3 = w4
     448:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     449:	4c 37 00 00 00 00 00 00	w7 |= w3
     450:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L10>
     451:	73 42 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w4
     452:	73 62 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w6
     453:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     454:	73 32 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w3
     455:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     456:	73 32 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w3
     457:	73 02 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w0
     458:	73 92 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w9
     459:	73 12 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w1
     460:	73 52 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w5
<L10>:
     461:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
     462:	c6 01 26 00 06 00 00 00	if w1 s< 0x6 goto +0x26 <L11>
     463:	71 21 10 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x10)
     464:	71 27 11 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x11)
     465:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     466:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     467:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     468:	4c 17 00 00 00 00 00 00	w7 |= w1
     469:	71 26 12 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x12)
     470:	bc 63 00 00 00 00 00 00	w3 = w6
     471:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     472:	4c 37 00 00 00 00 00 00	w7 |= w3
     473:	71 25 14 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x14)
     474:	71 21 15 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x15)
     475:	bc 18 00 00 00 00 00 00	w8 = w1
     476:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     477:	4c 58 00 00 00 00 00 00	w8 |= w5
     478:	71 29 16 00 00 00 00 00	w9 = *(u8 *)(r2 + 0x16)
     479:	bc 93 00 00 00 00 00 00	w3 = w9
     480:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     481:	4c 38 00 00 00 00 00 00	w8 |= w3
     482:	71 20 17 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x17)
     483:	bc 03 00 00 00 00 00 00	w3 = w0
     484:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     485:	4c 38 00 00 00 00 00 00	w8 |= w3
     486:	71 24 13 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x13)
     487:	bc 43 00 00 00 00 00 00	w3 = w4
     488:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     489:	4c 37 00 00 00 00 00 00	w7 |= w3
     490:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L11>
     491:	73 42 17 00 00 00 00 00	*(u8 *)(r2 + 0x17) = w4
     492:	73 62 16 00 00 00 00 00	*(u8 *)(r2 + 0x16) = w6
     493:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     494:	73 32 15 00 00 00 00 00	*(u8 *)(r2 + 0x15) = w3
     495:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     496:	73 32 14 00 00 00 00 00	*(u8 *)(r2 + 0x14) = w3
     497:	73 02 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w0
     498:	73 92 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w9
     499:	73 12 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w1
     500:	73 52 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w5
<L11>:
     501:	71 21 08 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x8)
     502:	71 27 09 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x9)
     503:	63 7a e0 ff 00 00 00 00	*(u32 *)(r10 - 0x20) = w7
     504:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     505:	63 1a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w1
     506:	4c 17 00 00 00 00 00 00	w7 |= w1
     507:	71 26 0a 00 00 00 00 00	w6 = *(u8 *)(r2 + 0xa)
     508:	bc 63 00 00 00 00 00 00	w3 = w6
     509:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     510:	4c 37 00 00 00 00 00 00	w7 |= w3
     511:	71 25 0c 00 00 00 00 00	w5 = *(u8 *)(r2 + 0xc)
     512:	71 21 0d 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xd)
     513:	bc 18 00 00 00 00 00 00	w8 = w1
     514:	64 08 00 00 08 00 00 00	w8 <<= 0x8
     515:	4c 58 00 00 00 00 00 00	w8 |= w5
     516:	71 29 0e 00 00 00 00 00	w9 = *(u8 *)(r2 + 0xe)
     517:	bc 93 00 00 00 00 00 00	w3 = w9
     518:	64 03 00 00 10 00 00 00	w3 <<= 0x10
     519:	4c 38 00 00 00 00 00 00	w8 |= w3
     520:	71 20 0f 00 00 00 00 00	w0 = *(u8 *)(r2 + 0xf)
     521:	bc 03 00 00 00 00 00 00	w3 = w0
     522:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     523:	4c 38 00 00 00 00 00 00	w8 |= w3
     524:	71 24 0b 00 00 00 00 00	w4 = *(u8 *)(r2 + 0xb)
     525:	bc 43 00 00 00 00 00 00	w3 = w4
     526:	64 03 00 00 18 00 00 00	w3 <<= 0x18
     527:	4c 37 00 00 00 00 00 00	w7 |= w3
     528:	be 87 0a 00 00 00 00 00	if w7 <= w8 goto +0xa <L12>
     529:	73 42 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w4
     530:	73 62 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w6
     531:	61 a3 e0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x20)
     532:	73 32 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w3
     533:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     534:	73 32 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w3
     535:	73 02 0b 00 00 00 00 00	*(u8 *)(r2 + 0xb) = w0
     536:	73 92 0a 00 00 00 00 00	*(u8 *)(r2 + 0xa) = w9
     537:	73 12 09 00 00 00 00 00	*(u8 *)(r2 + 0x9) = w1
     538:	73 52 08 00 00 00 00 00	*(u8 *)(r2 + 0x8) = w5
<L12>:
     539:	61 a1 f0 ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x10)
     540:	c6 01 4c 00 06 00 00 00	if w1 s< 0x6 goto +0x4c <L14>
     541:	71 21 0c 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xc)
     542:	71 26 0d 00 00 00 00 00	w6 = *(u8 *)(r2 + 0xd)
     543:	63 6a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w6
     544:	64 06 00 00 08 00 00 00	w6 <<= 0x8
     545:	63 1a f0 ff 00 00 00 00	*(u32 *)(r10 - 0x10) = w1
     546:	4c 16 00 00 00 00 00 00	w6 |= w1
     547:	71 25 0e 00 00 00 00 00	w5 = *(u8 *)(r2 + 0xe)
     548:	bc 54 00 00 00 00 00 00	w4 = w5
     549:	64 04 00 00 10 00 00 00	w4 <<= 0x10
     550:	4c 46 00 00 00 00 00 00	w6 |= w4
     551:	71 24 10 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x10)
     552:	71 21 11 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x11)
     553:	bc 17 00 00 00 00 00 00	w7 = w1
     554:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     555:	4c 47 00 00 00 00 00 00	w7 |= w4
     556:	71 28 12 00 00 00 00 00	w8 = *(u8 *)(r2 + 0x12)
     557:	bc 80 00 00 00 00 00 00	w0 = w8
     558:	64 00 00 00 10 00 00 00	w0 <<= 0x10
     559:	4c 07 00 00 00 00 00 00	w7 |= w0
     560:	71 20 13 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x13)
     561:	bc 09 00 00 00 00 00 00	w9 = w0
     562:	64 09 00 00 18 00 00 00	w9 <<= 0x18
     563:	4c 97 00 00 00 00 00 00	w7 |= w9
     564:	71 23 0f 00 00 00 00 00	w3 = *(u8 *)(r2 + 0xf)
     565:	bc 39 00 00 00 00 00 00	w9 = w3
     566:	64 09 00 00 18 00 00 00	w9 <<= 0x18
     567:	4c 96 00 00 00 00 00 00	w6 |= w9
     568:	be 76 0a 00 00 00 00 00	if w6 <= w7 goto +0xa <L13>
     569:	73 32 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w3
     570:	73 52 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w5
     571:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     572:	73 32 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w3
     573:	61 a3 f0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x10)
     574:	73 32 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w3
     575:	73 02 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w0
     576:	73 82 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w8
     577:	73 12 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w1
     578:	73 42 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w4
<L13>:
     579:	71 21 08 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x8)
     580:	71 26 09 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x9)
     581:	63 6a e8 ff 00 00 00 00	*(u32 *)(r10 - 0x18) = w6
     582:	64 06 00 00 08 00 00 00	w6 <<= 0x8
     583:	63 1a f0 ff 00 00 00 00	*(u32 *)(r10 - 0x10) = w1
     584:	4c 16 00 00 00 00 00 00	w6 |= w1
     585:	71 25 0a 00 00 00 00 00	w5 = *(u8 *)(r2 + 0xa)
     586:	bc 54 00 00 00 00 00 00	w4 = w5
     587:	64 04 00 00 10 00 00 00	w4 <<= 0x10
     588:	4c 46 00 00 00 00 00 00	w6 |= w4
     589:	71 24 0c 00 00 00 00 00	w4 = *(u8 *)(r2 + 0xc)
     590:	71 21 0d 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xd)
     591:	bc 17 00 00 00 00 00 00	w7 = w1
     592:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     593:	4c 47 00 00 00 00 00 00	w7 |= w4
     594:	71 28 0e 00 00 00 00 00	w8 = *(u8 *)(r2 + 0xe)
     595:	bc 80 00 00 00 00 00 00	w0 = w8
     596:	64 00 00 00 10 00 00 00	w0 <<= 0x10
     597:	4c 07 00 00 00 00 00 00	w7 |= w0
     598:	71 29 0f 00 00 00 00 00	w9 = *(u8 *)(r2 + 0xf)
     599:	bc 90 00 00 00 00 00 00	w0 = w9
     600:	64 00 00 00 18 00 00 00	w0 <<= 0x18
     601:	4c 07 00 00 00 00 00 00	w7 |= w0
     602:	71 23 0b 00 00 00 00 00	w3 = *(u8 *)(r2 + 0xb)
     603:	bc 30 00 00 00 00 00 00	w0 = w3
     604:	64 00 00 00 18 00 00 00	w0 <<= 0x18
     605:	4c 06 00 00 00 00 00 00	w6 |= w0
     606:	be 76 0a 00 00 00 00 00	if w6 <= w7 goto +0xa <L14>
     607:	73 32 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w3
     608:	73 52 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w5
     609:	61 a3 e8 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x18)
     610:	73 32 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w3
     611:	61 a3 f0 ff 00 00 00 00	w3 = *(u32 *)(r10 - 0x10)
     612:	73 32 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w3
     613:	73 92 0b 00 00 00 00 00	*(u8 *)(r2 + 0xb) = w9
     614:	73 82 0a 00 00 00 00 00	*(u8 *)(r2 + 0xa) = w8
     615:	73 12 09 00 00 00 00 00	*(u8 *)(r2 + 0x9) = w1
     616:	73 42 08 00 00 00 00 00	*(u8 *)(r2 + 0x8) = w4
<L14>:
     617:	61 a0 f8 ff 00 00 00 00	w0 = *(u32 *)(r10 - 0x8)
     618:	95 00 00 00 00 00 00 00	exit
```

## Classified instruction list

Same bytes, one row per slot. `LDDW` pairs: none. Jump targets are in the table above.

| Slot | Bytes | Opcode | Kind | Operands |
| ---: | --- | --- | --- | --- |
| 0 | `b402000000000000` | `0xb4` | `ALU32_MOV_K` | `r2, 0` |
| 1 | `632af8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65528], r2` |
| 2 | `6113040000000000` | `0x61` | `LDX_W_MEM` | `r3, [r1+4]` |
| 3 | `6112000000000000` | `0x61` | `LDX_W_MEM` | `r2, [r1+0]` |
| 4 | `bf24000000000000` | `0xbf` | `ALU64_MOV_X` | `r4, r2` |
| 5 | `0704000008000000` | `0x07` | `ALU64_ADD_K` | `r4, 8` |
| 6 | `2d34620200000000` | `0x2d` | `JMP64_JGT_X` | `r4, r3, 610` |
| 7 | `7124050000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+5]` |
| 8 | `7120040000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+4]` |
| 9 | `7125060000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+6]` |
| 10 | `7126070000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+7]` |
| 11 | `bf23000000000000` | `0xbf` | `ALU64_MOV_X` | `r3, r2` |
| 12 | `0703000020000000` | `0x07` | `ALU64_ADD_K` | `r3, 32` |
| 13 | `6111040000000000` | `0x61` | `LDX_W_MEM` | `r1, [r1+4]` |
| 14 | `2d135a0200000000` | `0x2d` | `JMP64_JGT_X` | `r3, r1, 602` |
| 15 | `6404000008000000` | `0x64` | `ALU32_LSH_K` | `r4, 8` |
| 16 | `4c04000000000000` | `0x4c` | `ALU32_OR_X` | `r4, r0` |
| 17 | `6405000010000000` | `0x64` | `ALU32_LSH_K` | `r5, 16` |
| 18 | `6406000018000000` | `0x64` | `ALU32_LSH_K` | `r6, 24` |
| 19 | `4c56000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r5` |
| 20 | `4c46000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r4` |
| 21 | `bc61000000000000` | `0xbc` | `ALU32_MOV_X` | `r1, r6` |
| 22 | `04010000f9ffffff` | `0x04` | `ALU32_ADD_K` | `r1, -7` |
| 23 | `a6015102fbffffff` | `0xa6` | `JMP32_JLT_K` | `r1, -5, 593` |
| 24 | `636af0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65520], r6` |
| 25 | `7121080000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+8]` |
| 26 | `7126090000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+9]` |
| 27 | `636ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r6` |
| 28 | `6406000008000000` | `0x64` | `ALU32_LSH_K` | `r6, 8` |
| 29 | `631af8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65528], r1` |
| 30 | `4c16000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r1` |
| 31 | `71200a0000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+10]` |
| 32 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 33 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 34 | `4c36000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r3` |
| 35 | `71250c0000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+12]` |
| 36 | `71210d0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+13]` |
| 37 | `bc17000000000000` | `0xbc` | `ALU32_MOV_X` | `r7, r1` |
| 38 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 39 | `4c57000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r5` |
| 40 | `71280e0000000000` | `0x71` | `LDX_B_MEM` | `r8, [r2+14]` |
| 41 | `bc83000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r8` |
| 42 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 43 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 44 | `71290f0000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+15]` |
| 45 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 46 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 47 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 48 | `71240b0000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+11]` |
| 49 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 50 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 51 | `4c36000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r3` |
| 52 | `be760a0000000000` | `0xbe` | `JMP32_JLE_X` | `r6, r7, 10` |
| 53 | `73420f0000000000` | `0x73` | `STX_B_MEM` | `[r2+15], r4` |
| 54 | `73020e0000000000` | `0x73` | `STX_B_MEM` | `[r2+14], r0` |
| 55 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 56 | `73320d0000000000` | `0x73` | `STX_B_MEM` | `[r2+13], r3` |
| 57 | `61a3f8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65528]` |
| 58 | `73320c0000000000` | `0x73` | `STX_B_MEM` | `[r2+12], r3` |
| 59 | `73920b0000000000` | `0x73` | `STX_B_MEM` | `[r2+11], r9` |
| 60 | `73820a0000000000` | `0x73` | `STX_B_MEM` | `[r2+10], r8` |
| 61 | `7312090000000000` | `0x73` | `STX_B_MEM` | `[r2+9], r1` |
| 62 | `7352080000000000` | `0x73` | `STX_B_MEM` | `[r2+8], r5` |
| 63 | `b401000002000000` | `0xb4` | `ALU32_MOV_K` | `r1, 2` |
| 64 | `631af8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65528], r1` |
| 65 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 66 | `1601260202000000` | `0x16` | `JMP32_JEQ_K` | `r1, 2, 550` |
| 67 | `71210c0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+12]` |
| 68 | `71270d0000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+13]` |
| 69 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 70 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 71 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 72 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 73 | `71260e0000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+14]` |
| 74 | `bc61000000000000` | `0xbc` | `ALU32_MOV_X` | `r1, r6` |
| 75 | `6401000010000000` | `0x64` | `ALU32_LSH_K` | `r1, 16` |
| 76 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 77 | `7125100000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+16]` |
| 78 | `7120110000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+17]` |
| 79 | `bc08000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r0` |
| 80 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 81 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 82 | `7129120000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+18]` |
| 83 | `bc91000000000000` | `0xbc` | `ALU32_MOV_X` | `r1, r9` |
| 84 | `6401000010000000` | `0x64` | `ALU32_LSH_K` | `r1, 16` |
| 85 | `4c18000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r1` |
| 86 | `7121130000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+19]` |
| 87 | `bc13000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r1` |
| 88 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 89 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 90 | `71240f0000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+15]` |
| 91 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 92 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 93 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 94 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 95 | `7342130000000000` | `0x73` | `STX_B_MEM` | `[r2+19], r4` |
| 96 | `7362120000000000` | `0x73` | `STX_B_MEM` | `[r2+18], r6` |
| 97 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 98 | `7332110000000000` | `0x73` | `STX_B_MEM` | `[r2+17], r3` |
| 99 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 100 | `7332100000000000` | `0x73` | `STX_B_MEM` | `[r2+16], r3` |
| 101 | `73120f0000000000` | `0x73` | `STX_B_MEM` | `[r2+15], r1` |
| 102 | `73920e0000000000` | `0x73` | `STX_B_MEM` | `[r2+14], r9` |
| 103 | `73020d0000000000` | `0x73` | `STX_B_MEM` | `[r2+13], r0` |
| 104 | `73520c0000000000` | `0x73` | `STX_B_MEM` | `[r2+12], r5` |
| 105 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 106 | `a601760004000000` | `0xa6` | `JMP32_JLT_K` | `r1, 4, 118` |
| 107 | `7121100000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+16]` |
| 108 | `7127110000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+17]` |
| 109 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 110 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 111 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 112 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 113 | `7126120000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+18]` |
| 114 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 115 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 116 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 117 | `7125140000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+20]` |
| 118 | `7121150000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+21]` |
| 119 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 120 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 121 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 122 | `7129160000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+22]` |
| 123 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 124 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 125 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 126 | `7120170000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+23]` |
| 127 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 128 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 129 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 130 | `7124130000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+19]` |
| 131 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 132 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 133 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 134 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 135 | `7342170000000000` | `0x73` | `STX_B_MEM` | `[r2+23], r4` |
| 136 | `7362160000000000` | `0x73` | `STX_B_MEM` | `[r2+22], r6` |
| 137 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 138 | `7332150000000000` | `0x73` | `STX_B_MEM` | `[r2+21], r3` |
| 139 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 140 | `7332140000000000` | `0x73` | `STX_B_MEM` | `[r2+20], r3` |
| 141 | `7302130000000000` | `0x73` | `STX_B_MEM` | `[r2+19], r0` |
| 142 | `7392120000000000` | `0x73` | `STX_B_MEM` | `[r2+18], r9` |
| 143 | `7312110000000000` | `0x73` | `STX_B_MEM` | `[r2+17], r1` |
| 144 | `7352100000000000` | `0x73` | `STX_B_MEM` | `[r2+16], r5` |
| 145 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 146 | `16014e0004000000` | `0x16` | `JMP32_JEQ_K` | `r1, 4, 78` |
| 147 | `7121140000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+20]` |
| 148 | `7127150000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+21]` |
| 149 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 150 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 151 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 152 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 153 | `7126160000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+22]` |
| 154 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 155 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 156 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 157 | `7125180000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+24]` |
| 158 | `7121190000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+25]` |
| 159 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 160 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 161 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 162 | `71291a0000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+26]` |
| 163 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 164 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 165 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 166 | `71201b0000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+27]` |
| 167 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 168 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 169 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 170 | `7124170000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+23]` |
| 171 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 172 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 173 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 174 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 175 | `73421b0000000000` | `0x73` | `STX_B_MEM` | `[r2+27], r4` |
| 176 | `73621a0000000000` | `0x73` | `STX_B_MEM` | `[r2+26], r6` |
| 177 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 178 | `7332190000000000` | `0x73` | `STX_B_MEM` | `[r2+25], r3` |
| 179 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 180 | `7332180000000000` | `0x73` | `STX_B_MEM` | `[r2+24], r3` |
| 181 | `7302170000000000` | `0x73` | `STX_B_MEM` | `[r2+23], r0` |
| 182 | `7392160000000000` | `0x73` | `STX_B_MEM` | `[r2+22], r9` |
| 183 | `7312150000000000` | `0x73` | `STX_B_MEM` | `[r2+21], r1` |
| 184 | `7352140000000000` | `0x73` | `STX_B_MEM` | `[r2+20], r5` |
| 185 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 186 | `a601260006000000` | `0xa6` | `JMP32_JLT_K` | `r1, 6, 38` |
| 187 | `7121180000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+24]` |
| 188 | `7127190000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+25]` |
| 189 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 190 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 191 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 192 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 193 | `71261a0000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+26]` |
| 194 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 195 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 196 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 197 | `71251c0000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+28]` |
| 198 | `71211d0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+29]` |
| 199 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 200 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 201 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 202 | `71291e0000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+30]` |
| 203 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 204 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 205 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 206 | `71201f0000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+31]` |
| 207 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 208 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 209 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 210 | `71241b0000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+27]` |
| 211 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 212 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 213 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 214 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 215 | `73421f0000000000` | `0x73` | `STX_B_MEM` | `[r2+31], r4` |
| 216 | `73621e0000000000` | `0x73` | `STX_B_MEM` | `[r2+30], r6` |
| 217 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 218 | `73321d0000000000` | `0x73` | `STX_B_MEM` | `[r2+29], r3` |
| 219 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 220 | `73321c0000000000` | `0x73` | `STX_B_MEM` | `[r2+28], r3` |
| 221 | `73021b0000000000` | `0x73` | `STX_B_MEM` | `[r2+27], r0` |
| 222 | `73921a0000000000` | `0x73` | `STX_B_MEM` | `[r2+26], r9` |
| 223 | `7312190000000000` | `0x73` | `STX_B_MEM` | `[r2+25], r1` |
| 224 | `7352180000000000` | `0x73` | `STX_B_MEM` | `[r2+24], r5` |
| 225 | `7121080000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+8]` |
| 226 | `7127090000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+9]` |
| 227 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 228 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 229 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 230 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 231 | `71260a0000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+10]` |
| 232 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 233 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 234 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 235 | `71250c0000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+12]` |
| 236 | `71210d0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+13]` |
| 237 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 238 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 239 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 240 | `71290e0000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+14]` |
| 241 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 242 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 243 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 244 | `71200f0000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+15]` |
| 245 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 246 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 247 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 248 | `71240b0000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+11]` |
| 249 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 250 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 251 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 252 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 253 | `73420f0000000000` | `0x73` | `STX_B_MEM` | `[r2+15], r4` |
| 254 | `73620e0000000000` | `0x73` | `STX_B_MEM` | `[r2+14], r6` |
| 255 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 256 | `73320d0000000000` | `0x73` | `STX_B_MEM` | `[r2+13], r3` |
| 257 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 258 | `73320c0000000000` | `0x73` | `STX_B_MEM` | `[r2+12], r3` |
| 259 | `73020b0000000000` | `0x73` | `STX_B_MEM` | `[r2+11], r0` |
| 260 | `73920a0000000000` | `0x73` | `STX_B_MEM` | `[r2+10], r9` |
| 261 | `7312090000000000` | `0x73` | `STX_B_MEM` | `[r2+9], r1` |
| 262 | `7352080000000000` | `0x73` | `STX_B_MEM` | `[r2+8], r5` |
| 263 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 264 | `c601600104000000` | `0xc6` | `JMP32_JSLT_K` | `r1, 4, 352` |
| 265 | `71210c0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+12]` |
| 266 | `71270d0000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+13]` |
| 267 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 268 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 269 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 270 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 271 | `71260e0000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+14]` |
| 272 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 273 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 274 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 275 | `7125100000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+16]` |
| 276 | `7121110000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+17]` |
| 277 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 278 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 279 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 280 | `7129120000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+18]` |
| 281 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 282 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 283 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 284 | `7120130000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+19]` |
| 285 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 286 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 287 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 288 | `71240f0000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+15]` |
| 289 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 290 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 291 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 292 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 293 | `7342130000000000` | `0x73` | `STX_B_MEM` | `[r2+19], r4` |
| 294 | `7362120000000000` | `0x73` | `STX_B_MEM` | `[r2+18], r6` |
| 295 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 296 | `7332110000000000` | `0x73` | `STX_B_MEM` | `[r2+17], r3` |
| 297 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 298 | `7332100000000000` | `0x73` | `STX_B_MEM` | `[r2+16], r3` |
| 299 | `73020f0000000000` | `0x73` | `STX_B_MEM` | `[r2+15], r0` |
| 300 | `73920e0000000000` | `0x73` | `STX_B_MEM` | `[r2+14], r9` |
| 301 | `73120d0000000000` | `0x73` | `STX_B_MEM` | `[r2+13], r1` |
| 302 | `73520c0000000000` | `0x73` | `STX_B_MEM` | `[r2+12], r5` |
| 303 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 304 | `16014e0004000000` | `0x16` | `JMP32_JEQ_K` | `r1, 4, 78` |
| 305 | `7121100000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+16]` |
| 306 | `7127110000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+17]` |
| 307 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 308 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 309 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 310 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 311 | `7126120000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+18]` |
| 312 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 313 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 314 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 315 | `7125140000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+20]` |
| 316 | `7121150000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+21]` |
| 317 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 318 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 319 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 320 | `7129160000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+22]` |
| 321 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 322 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 323 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 324 | `7120170000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+23]` |
| 325 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 326 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 327 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 328 | `7124130000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+19]` |
| 329 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 330 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 331 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 332 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 333 | `7342170000000000` | `0x73` | `STX_B_MEM` | `[r2+23], r4` |
| 334 | `7362160000000000` | `0x73` | `STX_B_MEM` | `[r2+22], r6` |
| 335 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 336 | `7332150000000000` | `0x73` | `STX_B_MEM` | `[r2+21], r3` |
| 337 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 338 | `7332140000000000` | `0x73` | `STX_B_MEM` | `[r2+20], r3` |
| 339 | `7302130000000000` | `0x73` | `STX_B_MEM` | `[r2+19], r0` |
| 340 | `7392120000000000` | `0x73` | `STX_B_MEM` | `[r2+18], r9` |
| 341 | `7312110000000000` | `0x73` | `STX_B_MEM` | `[r2+17], r1` |
| 342 | `7352100000000000` | `0x73` | `STX_B_MEM` | `[r2+16], r5` |
| 343 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 344 | `c601260006000000` | `0xc6` | `JMP32_JSLT_K` | `r1, 6, 38` |
| 345 | `7121140000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+20]` |
| 346 | `7127150000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+21]` |
| 347 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 348 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 349 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 350 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 351 | `7126160000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+22]` |
| 352 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 353 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 354 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 355 | `7125180000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+24]` |
| 356 | `7121190000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+25]` |
| 357 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 358 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 359 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 360 | `71291a0000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+26]` |
| 361 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 362 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 363 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 364 | `71201b0000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+27]` |
| 365 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 366 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 367 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 368 | `7124170000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+23]` |
| 369 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 370 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 371 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 372 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 373 | `73421b0000000000` | `0x73` | `STX_B_MEM` | `[r2+27], r4` |
| 374 | `73621a0000000000` | `0x73` | `STX_B_MEM` | `[r2+26], r6` |
| 375 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 376 | `7332190000000000` | `0x73` | `STX_B_MEM` | `[r2+25], r3` |
| 377 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 378 | `7332180000000000` | `0x73` | `STX_B_MEM` | `[r2+24], r3` |
| 379 | `7302170000000000` | `0x73` | `STX_B_MEM` | `[r2+23], r0` |
| 380 | `7392160000000000` | `0x73` | `STX_B_MEM` | `[r2+22], r9` |
| 381 | `7312150000000000` | `0x73` | `STX_B_MEM` | `[r2+21], r1` |
| 382 | `7352140000000000` | `0x73` | `STX_B_MEM` | `[r2+20], r5` |
| 383 | `7121080000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+8]` |
| 384 | `7127090000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+9]` |
| 385 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 386 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 387 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 388 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 389 | `71260a0000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+10]` |
| 390 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 391 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 392 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 393 | `71250c0000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+12]` |
| 394 | `71210d0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+13]` |
| 395 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 396 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 397 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 398 | `71290e0000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+14]` |
| 399 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 400 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 401 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 402 | `71200f0000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+15]` |
| 403 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 404 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 405 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 406 | `71240b0000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+11]` |
| 407 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 408 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 409 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 410 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 411 | `73420f0000000000` | `0x73` | `STX_B_MEM` | `[r2+15], r4` |
| 412 | `73620e0000000000` | `0x73` | `STX_B_MEM` | `[r2+14], r6` |
| 413 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 414 | `73320d0000000000` | `0x73` | `STX_B_MEM` | `[r2+13], r3` |
| 415 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 416 | `73320c0000000000` | `0x73` | `STX_B_MEM` | `[r2+12], r3` |
| 417 | `73020b0000000000` | `0x73` | `STX_B_MEM` | `[r2+11], r0` |
| 418 | `73920a0000000000` | `0x73` | `STX_B_MEM` | `[r2+10], r9` |
| 419 | `7312090000000000` | `0x73` | `STX_B_MEM` | `[r2+9], r1` |
| 420 | `7352080000000000` | `0x73` | `STX_B_MEM` | `[r2+8], r5` |
| 421 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 422 | `1601c20004000000` | `0x16` | `JMP32_JEQ_K` | `r1, 4, 194` |
| 423 | `71210c0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+12]` |
| 424 | `71270d0000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+13]` |
| 425 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 426 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 427 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 428 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 429 | `71260e0000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+14]` |
| 430 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 431 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 432 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 433 | `7125100000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+16]` |
| 434 | `7121110000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+17]` |
| 435 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 436 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 437 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 438 | `7129120000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+18]` |
| 439 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 440 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 441 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 442 | `7120130000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+19]` |
| 443 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 444 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 445 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 446 | `71240f0000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+15]` |
| 447 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 448 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 449 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 450 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 451 | `7342130000000000` | `0x73` | `STX_B_MEM` | `[r2+19], r4` |
| 452 | `7362120000000000` | `0x73` | `STX_B_MEM` | `[r2+18], r6` |
| 453 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 454 | `7332110000000000` | `0x73` | `STX_B_MEM` | `[r2+17], r3` |
| 455 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 456 | `7332100000000000` | `0x73` | `STX_B_MEM` | `[r2+16], r3` |
| 457 | `73020f0000000000` | `0x73` | `STX_B_MEM` | `[r2+15], r0` |
| 458 | `73920e0000000000` | `0x73` | `STX_B_MEM` | `[r2+14], r9` |
| 459 | `73120d0000000000` | `0x73` | `STX_B_MEM` | `[r2+13], r1` |
| 460 | `73520c0000000000` | `0x73` | `STX_B_MEM` | `[r2+12], r5` |
| 461 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 462 | `c601260006000000` | `0xc6` | `JMP32_JSLT_K` | `r1, 6, 38` |
| 463 | `7121100000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+16]` |
| 464 | `7127110000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+17]` |
| 465 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 466 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 467 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 468 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 469 | `7126120000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+18]` |
| 470 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 471 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 472 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 473 | `7125140000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+20]` |
| 474 | `7121150000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+21]` |
| 475 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 476 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 477 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 478 | `7129160000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+22]` |
| 479 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 480 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 481 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 482 | `7120170000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+23]` |
| 483 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 484 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 485 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 486 | `7124130000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+19]` |
| 487 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 488 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 489 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 490 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 491 | `7342170000000000` | `0x73` | `STX_B_MEM` | `[r2+23], r4` |
| 492 | `7362160000000000` | `0x73` | `STX_B_MEM` | `[r2+22], r6` |
| 493 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 494 | `7332150000000000` | `0x73` | `STX_B_MEM` | `[r2+21], r3` |
| 495 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 496 | `7332140000000000` | `0x73` | `STX_B_MEM` | `[r2+20], r3` |
| 497 | `7302130000000000` | `0x73` | `STX_B_MEM` | `[r2+19], r0` |
| 498 | `7392120000000000` | `0x73` | `STX_B_MEM` | `[r2+18], r9` |
| 499 | `7312110000000000` | `0x73` | `STX_B_MEM` | `[r2+17], r1` |
| 500 | `7352100000000000` | `0x73` | `STX_B_MEM` | `[r2+16], r5` |
| 501 | `7121080000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+8]` |
| 502 | `7127090000000000` | `0x71` | `LDX_B_MEM` | `r7, [r2+9]` |
| 503 | `637ae0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65504], r7` |
| 504 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 505 | `631ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r1` |
| 506 | `4c17000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r1` |
| 507 | `71260a0000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+10]` |
| 508 | `bc63000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r6` |
| 509 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 510 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 511 | `71250c0000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+12]` |
| 512 | `71210d0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+13]` |
| 513 | `bc18000000000000` | `0xbc` | `ALU32_MOV_X` | `r8, r1` |
| 514 | `6408000008000000` | `0x64` | `ALU32_LSH_K` | `r8, 8` |
| 515 | `4c58000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r5` |
| 516 | `71290e0000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+14]` |
| 517 | `bc93000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r9` |
| 518 | `6403000010000000` | `0x64` | `ALU32_LSH_K` | `r3, 16` |
| 519 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 520 | `71200f0000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+15]` |
| 521 | `bc03000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r0` |
| 522 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 523 | `4c38000000000000` | `0x4c` | `ALU32_OR_X` | `r8, r3` |
| 524 | `71240b0000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+11]` |
| 525 | `bc43000000000000` | `0xbc` | `ALU32_MOV_X` | `r3, r4` |
| 526 | `6403000018000000` | `0x64` | `ALU32_LSH_K` | `r3, 24` |
| 527 | `4c37000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r3` |
| 528 | `be870a0000000000` | `0xbe` | `JMP32_JLE_X` | `r7, r8, 10` |
| 529 | `73420f0000000000` | `0x73` | `STX_B_MEM` | `[r2+15], r4` |
| 530 | `73620e0000000000` | `0x73` | `STX_B_MEM` | `[r2+14], r6` |
| 531 | `61a3e0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65504]` |
| 532 | `73320d0000000000` | `0x73` | `STX_B_MEM` | `[r2+13], r3` |
| 533 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 534 | `73320c0000000000` | `0x73` | `STX_B_MEM` | `[r2+12], r3` |
| 535 | `73020b0000000000` | `0x73` | `STX_B_MEM` | `[r2+11], r0` |
| 536 | `73920a0000000000` | `0x73` | `STX_B_MEM` | `[r2+10], r9` |
| 537 | `7312090000000000` | `0x73` | `STX_B_MEM` | `[r2+9], r1` |
| 538 | `7352080000000000` | `0x73` | `STX_B_MEM` | `[r2+8], r5` |
| 539 | `61a1f0ff00000000` | `0x61` | `LDX_W_MEM` | `r1, [r10+65520]` |
| 540 | `c6014c0006000000` | `0xc6` | `JMP32_JSLT_K` | `r1, 6, 76` |
| 541 | `71210c0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+12]` |
| 542 | `71260d0000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+13]` |
| 543 | `636ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r6` |
| 544 | `6406000008000000` | `0x64` | `ALU32_LSH_K` | `r6, 8` |
| 545 | `631af0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65520], r1` |
| 546 | `4c16000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r1` |
| 547 | `71250e0000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+14]` |
| 548 | `bc54000000000000` | `0xbc` | `ALU32_MOV_X` | `r4, r5` |
| 549 | `6404000010000000` | `0x64` | `ALU32_LSH_K` | `r4, 16` |
| 550 | `4c46000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r4` |
| 551 | `7124100000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+16]` |
| 552 | `7121110000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+17]` |
| 553 | `bc17000000000000` | `0xbc` | `ALU32_MOV_X` | `r7, r1` |
| 554 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 555 | `4c47000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r4` |
| 556 | `7128120000000000` | `0x71` | `LDX_B_MEM` | `r8, [r2+18]` |
| 557 | `bc80000000000000` | `0xbc` | `ALU32_MOV_X` | `r0, r8` |
| 558 | `6400000010000000` | `0x64` | `ALU32_LSH_K` | `r0, 16` |
| 559 | `4c07000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r0` |
| 560 | `7120130000000000` | `0x71` | `LDX_B_MEM` | `r0, [r2+19]` |
| 561 | `bc09000000000000` | `0xbc` | `ALU32_MOV_X` | `r9, r0` |
| 562 | `6409000018000000` | `0x64` | `ALU32_LSH_K` | `r9, 24` |
| 563 | `4c97000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r9` |
| 564 | `71230f0000000000` | `0x71` | `LDX_B_MEM` | `r3, [r2+15]` |
| 565 | `bc39000000000000` | `0xbc` | `ALU32_MOV_X` | `r9, r3` |
| 566 | `6409000018000000` | `0x64` | `ALU32_LSH_K` | `r9, 24` |
| 567 | `4c96000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r9` |
| 568 | `be760a0000000000` | `0xbe` | `JMP32_JLE_X` | `r6, r7, 10` |
| 569 | `7332130000000000` | `0x73` | `STX_B_MEM` | `[r2+19], r3` |
| 570 | `7352120000000000` | `0x73` | `STX_B_MEM` | `[r2+18], r5` |
| 571 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 572 | `7332110000000000` | `0x73` | `STX_B_MEM` | `[r2+17], r3` |
| 573 | `61a3f0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65520]` |
| 574 | `7332100000000000` | `0x73` | `STX_B_MEM` | `[r2+16], r3` |
| 575 | `73020f0000000000` | `0x73` | `STX_B_MEM` | `[r2+15], r0` |
| 576 | `73820e0000000000` | `0x73` | `STX_B_MEM` | `[r2+14], r8` |
| 577 | `73120d0000000000` | `0x73` | `STX_B_MEM` | `[r2+13], r1` |
| 578 | `73420c0000000000` | `0x73` | `STX_B_MEM` | `[r2+12], r4` |
| 579 | `7121080000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+8]` |
| 580 | `7126090000000000` | `0x71` | `LDX_B_MEM` | `r6, [r2+9]` |
| 581 | `636ae8ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65512], r6` |
| 582 | `6406000008000000` | `0x64` | `ALU32_LSH_K` | `r6, 8` |
| 583 | `631af0ff00000000` | `0x63` | `STX_W_MEM` | `[r10+65520], r1` |
| 584 | `4c16000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r1` |
| 585 | `71250a0000000000` | `0x71` | `LDX_B_MEM` | `r5, [r2+10]` |
| 586 | `bc54000000000000` | `0xbc` | `ALU32_MOV_X` | `r4, r5` |
| 587 | `6404000010000000` | `0x64` | `ALU32_LSH_K` | `r4, 16` |
| 588 | `4c46000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r4` |
| 589 | `71240c0000000000` | `0x71` | `LDX_B_MEM` | `r4, [r2+12]` |
| 590 | `71210d0000000000` | `0x71` | `LDX_B_MEM` | `r1, [r2+13]` |
| 591 | `bc17000000000000` | `0xbc` | `ALU32_MOV_X` | `r7, r1` |
| 592 | `6407000008000000` | `0x64` | `ALU32_LSH_K` | `r7, 8` |
| 593 | `4c47000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r4` |
| 594 | `71280e0000000000` | `0x71` | `LDX_B_MEM` | `r8, [r2+14]` |
| 595 | `bc80000000000000` | `0xbc` | `ALU32_MOV_X` | `r0, r8` |
| 596 | `6400000010000000` | `0x64` | `ALU32_LSH_K` | `r0, 16` |
| 597 | `4c07000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r0` |
| 598 | `71290f0000000000` | `0x71` | `LDX_B_MEM` | `r9, [r2+15]` |
| 599 | `bc90000000000000` | `0xbc` | `ALU32_MOV_X` | `r0, r9` |
| 600 | `6400000018000000` | `0x64` | `ALU32_LSH_K` | `r0, 24` |
| 601 | `4c07000000000000` | `0x4c` | `ALU32_OR_X` | `r7, r0` |
| 602 | `71230b0000000000` | `0x71` | `LDX_B_MEM` | `r3, [r2+11]` |
| 603 | `bc30000000000000` | `0xbc` | `ALU32_MOV_X` | `r0, r3` |
| 604 | `6400000018000000` | `0x64` | `ALU32_LSH_K` | `r0, 24` |
| 605 | `4c06000000000000` | `0x4c` | `ALU32_OR_X` | `r6, r0` |
| 606 | `be760a0000000000` | `0xbe` | `JMP32_JLE_X` | `r6, r7, 10` |
| 607 | `73320f0000000000` | `0x73` | `STX_B_MEM` | `[r2+15], r3` |
| 608 | `73520e0000000000` | `0x73` | `STX_B_MEM` | `[r2+14], r5` |
| 609 | `61a3e8ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65512]` |
| 610 | `73320d0000000000` | `0x73` | `STX_B_MEM` | `[r2+13], r3` |
| 611 | `61a3f0ff00000000` | `0x61` | `LDX_W_MEM` | `r3, [r10+65520]` |
| 612 | `73320c0000000000` | `0x73` | `STX_B_MEM` | `[r2+12], r3` |
| 613 | `73920b0000000000` | `0x73` | `STX_B_MEM` | `[r2+11], r9` |
| 614 | `73820a0000000000` | `0x73` | `STX_B_MEM` | `[r2+10], r8` |
| 615 | `7312090000000000` | `0x73` | `STX_B_MEM` | `[r2+9], r1` |
| 616 | `7342080000000000` | `0x73` | `STX_B_MEM` | `[r2+8], r4` |
| 617 | `61a0f8ff00000000` | `0x61` | `LDX_W_MEM` | `r0, [r10+65528]` |
| 618 | `9500000000000000` | `0x95` | `JMP64_EXIT` | `` |

## Conversion result

**NOT CONVERTED.** No `.alive` file. The C++ decoder rejects the program at the first store. The Rocq semantics can decode every opcode in this file and can step the ALU and the jumps, but `exec_store` cannot perform the packet byte stores that are the point of the program. Calling the missing memory model "unsupported" is not success.

ISSUES
