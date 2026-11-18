# helper_loop observation

Observation report for a later compiler. This is not a shared ISA and not a conversion. The object was not rewritten. No `.alive` file was emitted. `decode_ebpf` / `lift_ebpf` were not executed; each opcode below is classified by reading the cited sources against the bytes.

## Identity

- File: `/Volumes/SSD/bs/build/helper_loop/bpf.o`
- sha256 computed with `shasum -a 256`: `973a78d63dba1f7ab4b1d2246855f0c92b17d1f0d5d4372dc52308622872dcb9` (matches the requested digest and `alive2/corpus/snapshot.toml`)
- Size: 7184 bytes. Notes file `/Volumes/SSD/bs/build/helper_loop/bpf.toml` sha256 `6776aad8120f94617c4b9bc369604ad0bac8cccd183703800bacd980f7c888c0` (matches the snapshot). Source read only as a name check: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/helper_loop.c`
- ELF64, `ELFDATA2LSB`, `ET_REL`, `EM_BPF`, `e_entry = 0`, no program headers. Instruction bytes are little-endian. `alive2/rocq/upstream/validator/Extraction.v` extracts `Archi.ptr64` as true and `Archi.big_endian` as false. CompCert `decode_val` itself was not read, so packet byte order is not re-derived here beyond that flag and the ELF encoding.
- Tools: `/opt/homebrew/opt/llvm/bin/llvm-readelf -a`, `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r -s --section-headers --syms`. A Python `-I` walk re-decoded every slot and the BTF section.

## Executable sections

| section | file off | size | flags | role |
| --- | --- | --- | --- | --- |
| `.text` | `0x40` | 0 | `AX` (`SHF_ALLOC\|SHF_EXECINSTR`) | empty. Not the program. Shares the file offset with `xdp` only because its size is 0. |
| `xdp` | `0x40` | `0xe0` (224) | `AX` | the only nonzero executable section |

No other section has `SHF_EXECINSTR`. `.maps` and `license` are `WA`, not executable.

## Entry

Relocatable object, so the ELF entry point is unused. The only function symbol is `helper_loop`: `STB_GLOBAL`, `STT_FUNC`, section `xdp`, value 0, size 224. Execution starts at slot 0 of `xdp`. There is no second entry and no code in `.text`.

## Slots

224 bytes = 28 eight-byte slots (indices 0..27). One `LDDW` occupies slots 20 and 21, so there are 27 instructions. Jump offsets are in slots, counted from the next slot, and the second `LDDW` slot is not an instruction. Renumbering after collapsing `LDDW` would move every later target.

`llvm-objdump -d` of section `xdp` (the empty `.text` dump is omitted because objdump prints no instructions for it):

```
0000000000000000 <helper_loop>:
       0:	b4 06 00 00 00 00 00 00	w6 = 0x0
       1:	61 12 04 00 00 00 00 00	w2 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [13] struct xdp_md::data_end (0:1)
       2:	61 11 00 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [13] struct xdp_md::data (0:0)
       3:	bf 13 00 00 00 00 00 00	r3 = r1
       4:	07 03 00 00 04 00 00 00	r3 += 0x4
       5:	2d 23 09 00 00 00 00 00	if r3 > r2 goto +0x9 <L2>
       6:	61 17 00 00 00 00 00 00	w7 = *(u32 *)(r1 + 0x0)
       7:	a6 07 01 00 08 00 00 00	if w7 < 0x8 goto +0x1 <L0>
       8:	b4 07 00 00 08 00 00 00	w7 = 0x8
<L0>:
       9:	b4 06 00 00 02 00 00 00	w6 = 0x2
      10:	16 07 04 00 00 00 00 00	if w7 == 0x0 goto +0x4 <L2>
      11:	b4 08 00 00 00 00 00 00	w8 = 0x0
      12:	05 00 04 00 00 00 00 00	goto +0x4 <L3>
<L1>:
      13:	04 08 00 00 01 00 00 00	w8 += 0x1
      14:	ae 78 02 00 00 00 00 00	if w8 < w7 goto +0x2 <L3>
<L2>:
      15:	bc 60 00 00 00 00 00 00	w0 = w6
      16:	95 00 00 00 00 00 00 00	exit
<L3>:
      17:	63 8a fc ff 00 00 00 00	*(u32 *)(r10 - 0x4) = w8
      18:	bf a2 00 00 00 00 00 00	r2 = r10
      19:	07 02 00 00 fc ff ff ff	r2 += -0x4
      20:	18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00	r1 = 0x0 ll
		00000000000000a0:  R_BPF_64_64	counters
      22:	85 00 00 00 01 00 00 00	call 0x1
      23:	15 00 f5 ff 00 00 00 00	if r0 == 0x0 goto -0xb <L1>
      24:	61 01 00 00 00 00 00 00	w1 = *(u32 *)(r0 + 0x0)
      25:	04 01 00 00 01 00 00 00	w1 += 0x1
      26:	63 10 00 00 00 00 00 00	*(u32 *)(r0 + 0x0) = w1
      27:	05 00 f1 ff 00 00 00 00	goto -0xf <L1>
```

### Instruction list

`class` is `opcode & 7`. Targets use `slot + 1 + off` (`alive2/src/ebpf.h` `jump_target`, and the same formula in `alive2/src/ebpf_decode.cpp`).

| slot | raw | op | decoded | jump |
| --- | --- | --- | --- | --- |
| 0 | `b406000000000000` | ALU32 MOV K | `w6 = 0` | fall 1 |
| 1 | `6112040000000000` | LDX W | `w2 = *(u32 *)(r1 + 4)` | fall 2 |
| 2 | `6111000000000000` | LDX W | `w1 = *(u32 *)(r1 + 0)` | fall 3 |
| 3 | `bf13000000000000` | ALU64 MOV X | `r3 = r1` | fall 4 |
| 4 | `0703000004000000` | ALU64 ADD K | `r3 += 4` | fall 5 |
| 5 | `2d23090000000000` | JMP64 JGT X | `if r3 > r2` unsigned | +9 → 15, else 6 |
| 6 | `6117000000000000` | LDX W | `w7 = *(u32 *)(r1 + 0)` | fall 7 |
| 7 | `a607010008000000` | JMP32 JLT K | `if w7 < 8` unsigned | +1 → 9, else 8 |
| 8 | `b407000008000000` | ALU32 MOV K | `w7 = 8` | fall 9 |
| 9 | `b406000002000000` | ALU32 MOV K | `w6 = 2` | fall 10 |
| 10 | `1607040000000000` | JMP32 JEQ K | `if w7 == 0` | +4 → 15, else 11 |
| 11 | `b408000000000000` | ALU32 MOV K | `w8 = 0` | fall 12 |
| 12 | `0500040000000000` | JMP64 JA | `goto +4` | → 17 |
| 13 | `0408000001000000` | ALU32 ADD K | `w8 += 1` | fall 14 |
| 14 | `ae78020000000000` | JMP32 JLT X | `if w8 < w7` unsigned | +2 → 17, else 15 |
| 15 | `bc60000000000000` | ALU32 MOV X | `w0 = w6` | fall 16 |
| 16 | `9500000000000000` | JMP EXIT | `exit` | return `r0` |
| 17 | `638afcff00000000` | STX W | `*(u32 *)(r10 - 4) = w8` | fall 18 |
| 18 | `bfa2000000000000` | ALU64 MOV X | `r2 = r10` | fall 19 |
| 19 | `07020000fcffffff` | ALU64 ADD K | `r2 += -4` | fall 20 |
| 20–21 | `1801000000000000` `0000000000000000` | LD DW IMM | `r1 = 0` with `src_reg = 0`; second slot reserved 0 | fall 22. See relocation below. |
| 22 | `8500000001000000` | JMP CALL K | `call 1`, `src_reg = 0`, `off = 0` | fall 23 |
| 23 | `1500f5ff00000000` | JMP64 JEQ K | `if r0 == 0` | −11 → 13, else 24 |
| 24 | `6101000000000000` | LDX W | `w1 = *(u32 *)(r0 + 0)` | fall 25 |
| 25 | `0401000001000000` | ALU32 ADD K | `w1 += 1` | fall 26 |
| 26 | `6310000000000000` | STX W | `*(u32 *)(r0 + 0) = w1` | fall 27 |
| 27 | `0500f1ff00000000` | JMP64 JA | `goto -15` | → 13 |

Back edges are slot 23 → 13 and slot 27 → 13. Both land on or before the jump, which is the lifter's loop test (`alive2/src/ebpf_lift.cpp` `build_blocks`, `tgt <= i`).

### What the bytes do

`r1` enters as the context pointer (`initial_lst_state` in `ebpfBinSem.v` sets `R1` to a `Vptr`). Slot 2 then overwrites `r1` with a zero-extended `u32` load. After that, `r1` is the packet `data` pointer, not `ctx`. Slot 6 loads `n` from `*(u32 *)data`, not from the context.

- `w6` is the return word: 0 until the bounds check passes, then 2. The C source names those `XDP_ABORTED` and `XDP_PASS`. The object itself only has immediates 0 and 2. Exit copies `w6` into `w0` with an ALU32 move, so the high half is zero.
- Bounds check: `data_end` is the zero-extended `u32` at `ctx+4`; `data` is the zero-extended `u32` at `ctx+0`; compare unsigned 64-bit `(data + 4) > data_end`. Failure jumps to the exit with `w6` still 0. This is not a 32-bit wrapping compare and not a sign-extending `(long)` cast, even though the C source writes `(void *)(long)`.
- `w7 = min(n, 8)` with the clamp in a register (slot 8 is skipped when `w7 < 8`). `w7 == 0` skips the loop and returns 2.
- Loop index `w8` starts at 0 by jumping over the increment (slot 12 → 17). The body runs while `w8 < w7` after each increment at slot 13. Iteration count is `w7`, at most 8.
- Each iteration stores `w8` at `fp-4`, calls helper 1 with `r1 = <map>` and `r2 = fp-4`, and on a non-zero `r0` does a 32-bit load/add/store at `r0+0`. A zero `r0` skips the store. Either way control returns to slot 13. `r6`, `r7`, `r8`, `r10` are live across the call; `r1`–`r5` are not.

## Relocations, map, CO-RE, endianness

Code relocation, section `.relxdp`, one `Elf64_Rel`:

- offset `0xa0` (slot 20), type `1` = `R_BPF_64_64`, symbol index 12 = `counters`
- symbol: `GLOBAL OBJECT`, section `.maps` (index 5), value 0, size 32

That is not three different references. Keep them apart:

1. Raw object encoding. The `LDDW` has `src_reg = 0`, `imm = 0`, `next_imm = 0`, and the second slot's low 32 bits are 0. `decode_lddw_insn` in `alive2/rocq/upstream/theories/ebpfDecoder.v` maps source `R0` to `Plddw PSEUDO_Constant`. `exec_lddw` then writes `Vlong (Int64.ofwords hi lo)`, which is the integer 0, and does not consult `addr_map`. Ignoring the relocation and lifting `r1 = 0` is the wrong program.
2. Not an XPOST relocation. Compact XPOST, as read in `tooling/vendor/xpost-elf/src/lib.rs` and `encode.rs`, is a different container: `.xpost.meta`, `.xpost.image`, optional `.xpost.mem` (`XPM1`), and `MapDescriptorV0.map_vma`. This file has none of those sections. `bpf.toml`'s `aot_addr = 0x40380270` is a note, not an ELF relocation and not an instruction immediate.
3. Not a map-index reference. `ebpfSyntax.v` lists `src_reg 0x5` as `map_by_idx` (`PSEUDO_MAP_IDX` / `R5` in `decode_lddw_insn`). This `src_reg` is 0, not 5, and not 1 (`PSEUDO_MAP_FD`). The object does not already contain a map fd or a map index. The only thing that names the map is `R_BPF_64_64` against the symbol `counters`.

Other relocations are not instruction operands:

- `.rel.BTF`: `R_BPF_64_NODYLD32` at `0x1bc` (`counters`) and `0x1d4` (`LICENSE`). These patch BTF datasec variable offsets.
- `.rel.BTF.ext`: twenty `R_BPF_64_NODYLD32` against section symbol `xdp`. They locate line and CO-RE records in `xdp`.
- `.rel.debug_*`: DWARF, not code.

`.maps` is 32 zero bytes. That is the size of the BTF map descriptor struct, not a filled array image. It happens to equal `max_entries * value_size`; those are different quantities.

BTF (parsed; header `0xeb9f`, version 1, type bytes end on the section boundary):

- `t10` anonymous struct, size 32. `type` is a pointer to an array of 2 `int`s (the usual `__uint` encoding of map type 2, `BPF_MAP_TYPE_ARRAY`). `max_entries` is a pointer to an array of 8 `int`s. `key` and `value` are both pointers to typedef `__u32` (`unsigned int`, 4 bytes, encoding unsigned).
- `t11` VAR `counters`, linkage 1, type `t10`. DATASEC `.maps` places it at offset 0, size 32.
- `t13` STRUCT `xdp_md`, size 24: `data` at bit 0, `data_end` at bit 32, then `data_meta`, `ingress_ifindex`, `rx_queue_index`, `egress_ifindex`, each `__u32`.
- `t18` VAR `LICENSE`, array of 4 `char`. Section `license` bytes are `47 50 4c 00` (`GPL\0`).

`.BTF.ext` core relocations (record size 16, section name `xdp`, count 2), same as `bpf.toml` `[CORE]` and the objdump CO-RE notes:

- insn byte `0x8` (slot 1), type id 13 `xdp_md`, access `0:1`, kind 0 (field byte offset) → `data_end`. The instruction immediate is already 4, which matches this BTF layout.
- insn byte `0x10` (slot 2), type id 13, access `0:0`, kind 0 → `data`. The immediate is already 0.

A loader that retargets `xdp_md` could still patch those two immediates. In this file they are already the local offsets. No other instruction has a CO-RE record. The packet load at slot 6 is a plain `u32` load through the data pointer, not a CO-RE field.

## Semantic rules actually read

Cited because the text was read. Rules not in this list were not used.

C++ decoder and IR lifter:

- `alive2/src/ebpf.h`: `EbAlu` / `EbJmp` only. No load, store, `LDDW`, or call variant.
- `alive2/src/ebpf_decode.cpp`: ALU and JMP/JMP32 only. Class other than ALU/ALU64/JMP/JMP32 raises `unsupported class`. JMP code `0x80` (`CALL`) falls through to `unsupported jump opcode`. `EXIT` requires class JMP, no register source, `dst = src = off = 0`. `JA` on JMP requires `imm = 0` and uses the 16-bit offset. ALU32 immediate sources are zero-extended later by the lifter, not here. `jump_target` is `index + 1 + disp`.
- `alive2/src/ebpf_lift.cpp`: `emit_alu` / `emit_cmp` / `emit`. ALU32 is trunc to `i32`, operate, `zext` to `i64`. ALU64 `MOV` returns the source value unchanged. ALU64 `ADD` is `BinOp::Add` on `i64`. ALU64 immediates are sign-extended (`imm64` with `sign_imm`); ALU32 immediates are zero-extended then truncated. `JGT` → `ICmp::UGT`, `JLT` → `ICmp::ULT`, `JEQ` → `ICmp::EQ`. `JA` is an unconditional `Branch`. `EXIT` is `Return` of `r0` as `i64`. A back edge sets `LiftInfo.loop`. `concrete()` marks `MemInstr` as `MemorySummary::Changed` and then `StepStatus::Unsupported`; the symbolic lifter never builds a `MemInstr` because the decoder rejects the memory classes. There is no helper, map, or stack memory opcode.
- `alive2/src/ebpf_gate.cpp`: rejects any decoded `r10` read or write (`r10 read`). Does not itself reject loops. `r0`–`r9` are the definedness bits. This program reads `r10` at slots 17 and 18; slot 18 is an ALU64 move the gate would reject if decoding ever reached it.
- `alive2/src/ebpf_project.cpp` `build_blocks` / the check around lines 873–889: a back edge sets `program.loop`, pushes a pc whose reason is `back edge`, and returns without unrolling and without projecting. `alive2/src/ebpf_exhibit.cpp` states that supported-scope-equivalent does not cover loops, memory, maps, or helpers, and that a back edge is reported `UNSUPPORTED` and not unrolled. That exhibit status is an exclusion, not a successful conversion.

Rocq:

- `alive2/rocq/upstream/theories/ebpfSyntax.v`: instruction forms `Pload`, `Pstore`, `Plddw` (including `PSEUDO_Constant`, `PSEUDO_MAP_FD`, `PSEUDO_MAP_IDX`), `Palu`, `Pjmp64`, `Pjmpcmp`, `Pcall` (`CallByStaticID` / `CallInternal` / `CallByBTF`), `Pret`. Register `R10` is the frame pointer. Caller-saved list is `R1`–`R5`. The `src_reg` table for `LDDW` was read there.
- `alive2/rocq/upstream/theories/ebpfDecoder.v` `decode_insn`, `decode_lddw_insn`, `find_instr`: full file. ALU32/ALU64 codes `0x0` ADD and `0xb` MOV. JMP64/JMP32 codes `0x0` JA, `0x1` EQ, `0x2` unsigned GT, `0xa` unsigned LT, `0x8` CALL when class is JMP64 and source is immediate (`R0` → `CallByStaticID`), `0x9` EXIT. Memory mode `(opcode >> 5) == 3` with size word is `Pload` / `Pstore` of `Word`. `LDDW` (`opcode == 0x18`) consumes `pc+1` and requires the second slot's low 32 bits to be 0, which they are. `src_reg = R0` selects `PSEUDO_Constant`.
- `alive2/rocq/upstream/theories/ebpfBinSem.v`, the definitions named below, not the whole 1292 lines: `eval_alu32` (`MOV` is `Val.longofintu` of the low word; `ADD` is `Val.longofintu (Val.add ...)`), `eval_alu64` (`ADD` is `Val.addl`; `MOV` is the source), `exec_alu`, `eval_cmp32`, `eval_cmp64` (unsigned `GT`/`LT` use `Val.cmpu_bool` / `Val.cmplu_bool`), `eval_cmp_static` (not triggered here: no compare of a register with itself, and the unsigned-immediate shortcuts are `imm == 0` or `imm == -1`, while slot 7's immediate is 8), `exec_jmpcmp`, `exec_jmp64`, `exec_load` (a `Vlong` address is `cast_i2p` against `addr_map`; a `Vptr` is `Val.offset_ptr`; failure is `Stuck`; a 32-bit load is zero-extended by `load_value_casting`), `exec_store` (`Val.offset_ptr` on the destination register, then `store` of `Word`; `None` is `Stuck`; it does not `cast_i2p`), `exec_lddw`, `exec_ret` (empty call stack sets `PC` to `Vnullptr` and keeps `R0`), `exec_instr` (only `Pcall CallInternal` is in the match; `CallByStaticID` and `Patomic` hit `_ => Stuck`), `exec_step_external` (static-id and BTF calls go through the parameter `ebpf_call_function`, which is an uninterpreted `Variable` at line 60, then `undef_caller_save_regs` and `R0 <- res`), `initial_lst_state` (`R10` is `Vptr stk (Ptrofs.repr 512)`, `R1` is the context pointer), `bpf_stack_size = 512`. `exec_instr_event` records `eBPF_vload` / `eBPF_vstore` only for `Pload` / `Pstore`. The external step records `eBPF_ext_call`. Neither event is a map or helper specification.
- `alive2/rocq/upstream/validator/Extraction.v`: endianness and `ptr64` only. `Validation.v` was not read; its proofs are not cited. `CMemoryModel.v`, `GlobalSem.v`, `Nondeterminism.v`, `SCLanguage.v`, and `ebpfState.v` were not read beyond the `regset` / `outcome` names visible from `ebpfBinSem.v`'s imports.

Observation notes, for what a later compiler must preserve, not for what this lifter does:

- `doc/观察.md`: observations are helper, branch, return, map write, packet write. A stack store is not a map write or a packet write. A map write keeps the key bytes recorded at the lookup, not the key-buffer address. `EXIT` is the return. Proposition 2 is stated there as not fully proved.
- `doc/寄存器.md`: map memory is a slice of the value for a key, and the address has to trace to a lookup return that already recorded the map id and the key bytes. Packet bytes are relative to context `data`. Context includes map key/value sizes.
- `doc/证明义务.md`: the link from a helper call to the comparison term is not established, including the assumption that the high 32 bits of a 64-bit helper return are 0. A single back-edge truncation is not acceptance.
- `src/Observation/Insn.lean`: helper id 1 is `HelperKind.lookup`, arity 2. Id 2 would be `update`. This object never calls id 2.
- `src/Observation/Helper.lean`: `freezeHelperArgs` for `.lookup` replaces the key pointer with `keySize` bytes. That function was read; it is not wired to this ELF.
- `src/Node/Drive.lean`: `loopLimit` is 128. That budget is not the clamp of 8 in this object, and it was not applied to these bytes.

Not read, so not used as a rule: CompCert `Val.addl` / `decode_val` / `Mem.loadbytes` bodies, the Linux verifier, and any loader that rewrites `R_BPF_64_64` into `src_reg = 1` plus a map fd. The C source was read to confirm the helper name and the clamp. Where the C text and the object differ (the `(long)` cast versus a zero-extending `LDXW`), the object wins.

## IR mapping against the existing C++ lifter only

`decode_ebpf` has no memory or call constructor. The first slot it cannot accept is slot 1, opcode `0x61`, class `LDX`: `unsupported class in opcode 0x61`. Slots after that are classified against the same code, not as instructions the function returns. Nothing below was lifted.

| slots | if the variant existed | what `emit_alu` / `emit_cmp` / `emit` actually do for that variant |
| --- | --- | --- |
| 0, 8, 9, 11 | `EbAlu` ALU32 `Mov` immediate | trunc immediate to `i32` (the immediate was zero-extended to `i64` first; 0, 8, 2, 0 are unchanged), then `zext` to `i64` |
| 3 | ALU64 `Mov` register | the source `Value*` is reused; no new arithmetic instruction |
| 4 | ALU64 `Add` immediate 4 | `i64` `BinOp::Add` of `r3` and sign-extended `4` |
| 13, 25 | ALU32 `Add` immediate 1 | `i32` add, then `zext` to `i64`. High half becomes 0 |
| 15 | ALU32 `Mov` register | trunc `r6` to `i32`, `zext` to `i64` into `r0` |
| 18 | ALU64 `Mov` of `r10` | same value as `r10`. Under `LiftInit::Rocq`, `r10` starts as `PoisonValue` tagged `RegOrigin::Pointer`. `pointer_alu` would set `pointer_use`. The gate rejects the `r10` read before a proof |
| 19 | ALU64 `Add` immediate −4 | `i64` `BinOp::Add` of sign-extended `−4`. Not a stack address. `pointer_alu` is true if `r2` is still the `r10` value. The produced sum is not entered in `origins` |
| 5 | JMP64 `Jgt` register | `ICmp::UGT` on the full `i64` values; true edge is the jump target, false edge is the fall-through |
| 7 | JMP32 `Jlt` immediate 8 | trunc both sides to `i32`, `ICmp::ULT` against `c32(8)` |
| 10 | JMP32 `Jeq` immediate 0 | trunc, `ICmp::EQ` against `c32(0)` |
| 14 | JMP32 `Jlt` register | trunc `w8` and `w7`, `ICmp::ULT` |
| 12, 27 | JMP64 `Ja` | unconditional `Branch`. Offsets +4 and −15. No condition |
| 16 | `Exit` | `Return` of the `i64` in `r0` |
| 23 | JMP64 `Jeq` immediate 0 | would be `ICmp::EQ` on `i64` `r0` against sign-extended `0`, if decoding reached it. It does not, because slot 1 already fails |
| 1, 2, 6, 24 | LDX W | no `EbInsn` case. No load in the lifter |
| 17, 26 | STX W | no `EbInsn` case. No store in the lifter |
| 20–21 | LDDW | class `LD`, rejected. The lifter has no 16-byte instruction and no relocation operand |
| 22 | CALL 1 | class JMP but code `0x80` is `unsupported jump opcode`. No helper symbol, no clobber of `r1`–`r5`, no `r0` result |

`eval_op` in the same file can concretely step `Add`, `Sub`, `And`, `UDiv`, `SDiv`, `ICmp::EQ`, and `ICmp::UGT` only. `ICmp::ULT` (slots 7 and 14) is not in that interpreter. That gap is inside the concrete tracer; it is not why this object fails.

## Memory, helper, map, and loop requirements

Memory.

- Three context/packet loads are zero-extending `u32`: `ctx+4` (`data_end`), `ctx+0` (`data`), then `*(u32 *)data` after `r1` has been replaced by `data`. The third is a packet read at packet offset 0, width 32, little-endian encoding of the file. It is not a `PacketWrite`. `doc/观察.md` has no packet-read observation.
- One stack store: `u32` at `r10-4`. `initial_lst_state` puts `R10` at offset 512 of a 512-byte frame, so −4 lands at 508, inside the frame, only while `r10` remains that pointer. The store is the lookup key, not a map write and not a packet write.
- One value load and one value store at `r0+0`, width 32, only on the non-zero side of slot 23. `r0` is the helper return, not a packet address and not the frame pointer. `exec_load` / `exec_store` `Stuck` unless that return is a `Vptr` (or, for the load only, a `Vlong` that `cast_i2p` resolves). The C++ lifter cannot represent either access.
- ALU64 `r3 += 4` and `r2 += -4` are pointer arithmetic on zero-extended addresses and on the frame pointer. The lifter folds both into `i64` `Add`.

Helper.

- One call, static id 1 (`src_reg = 0`, `imm = 1`, `off = 0`). `Insn.lean` names id 1 `lookup`. The C source calls `bpf_map_lookup_elem`. Arguments at the call: `r1` is the relocated map, `r2` is `r10-4`. `r3`–`r5` are not meaningful arguments (arity 2).
- Rocq does not define this helper. `exec_instr` returns `Stuck` for `CallByStaticID`. `exec_step_external` applies only when `ebpf_call_function` returns `Some (res, mem)`. That function is an unbound parameter. There is no equation for a null miss, for array bounds, or for which pointer is returned.
- Across the call the object needs `r6`, `r7`, `r8`, and `r10` preserved, and `r0` set to the pointer or 0. `undef_caller_save_regs` drops `R1`–`R5`, which matches the next use (`r1` is overwritten by the value load). It does not say what `r0` is.
- The return word is not a helper result. It is `w6` (0 or 2), copied to `w0` at the exit.

Map.

- One map, symbol `counters`, `BPF_MAP_TYPE_ARRAY`, `max_entries = 8`, key 4 bytes, value 4 bytes, from BTF `t10`/`t11`, agreeing with `bpf.toml`.
- The key is the 4 little-endian bytes of `w8` at the call, not the address in `r2`. `w8` is the iteration index `0 .. w7-1`.
- The update is the STX at slot 26, not helper id 2. For the observation in `doc/寄存器.md` it is a `MapWrite` of map `counters`, the key bytes frozen at this lookup, value offset 0, width 32, source = previous `u32` plus 1 in 32-bit arithmetic. A null return produces no write.
- Array lookup of a key `>= 8` is not in this object, because `w7` is clamped to 8 and the index walks `0 .. w7-1`. A model that drops the clamp and still calls the helper with key 8 is a different program. Nothing read here specifies that out-of-range lookup.

Loop.

- CFG back edges into slot 13, as listed above. The header is bottom-tested: the first body execution is the jump at slot 12, and the trip test is slot 14 after the increment.
- The C++ check records the back edge and stops. It does not unroll the 8-trip bound. `Drive.lean`'s `loopLimit` of 128 was not applied and is not this bound.
- `r7` is invariant in the loop. `r8` increases by 1 each trip. `w6` is already 2 before the loop and is not stored inside it.

## Conversion result

NOT CONVERTED.

The C++ decoder rejects slot 1. No IR, no CFG from `lift_ebpf`, and no `.alive` artifact was produced. Calling the missing helper or the back edge `UNSUPPORTED` would describe the exhibit's exclusion path; it is not a successful conversion of this object.

## Proof coverage

None for this object. No SMT query was run. The ALU and compare rules that were read would apply to slots 0, 3–5, 7–16, 18–19, 23, 25, and 27 only after the surrounding loads, stores, `LDDW`, and call had been decoded, which they cannot. Even then `ebpf_project.cpp` would stop on the back edge and emit no per-pc proof.

The Rocq step relation does not close:

- `Plddw PSEUDO_Constant` yields integer 0, not `counters`.
- `Pcall CallByStaticID` is `Stuck` in `exec_instr` unless an external interpretation is supplied, and none is defined for id 1.
- The value load/store `Stuck` without a `Vptr` (or a resolved `Vlong` on the load).
- `doc/证明义务.md` says the helper-call correspondence, including the high-32-bits assumption, is not proved. `doc/观察.md` says proposition 2 is not fully proved.

`profile.toml` expects `weak` for `helper_loop`, and `doc/匹配.md` records that name in a weak-match list under budget 1024. That measurement is the observation matcher, not an Alive2 conversion, and it was not re-run.

## Counterexample idea

Do not treat these as SMT results. They are inputs that separate this object from the models the current lifter and decoder implement.

1. Sign-extended or 32-bit-wrapping bounds check. Let `ctx.data = 0xfffffffd` and `ctx.data_end = 0xffffffff`, and let the four bytes at that address be anything. The object zero-extends, computes `0x100000001 > 0xffffffff`, takes slot 5, and returns 0 without a lookup. A model that sign-extends through `(long)` gets `data = -3`, `data+4 = 1`, `data_end = -1`, and the unsigned 64-bit compare `1 > 2^64-1` is false, so it would fall into the load. A model that adds and compares in 32 bits wraps `0xfffffffd+4` to 1, and `1 > 0xffffffff` is false, so it would also fall through. Either model returns 2 and may call the helper; the object returns 0 and does not.

2. Dropping the relocation. Packet `u32` at offset 0 is 1, length at least 4, `counters[0]` starts at 0. The object calls lookup on `counters` with key bytes `00 00 00 00` and, if that returns a value pointer, stores 1 and returns 2. `decode_lddw_insn` on the raw slots yields the constant 0. A program that calls helper 1 with map pointer 0 is not this program, even if it also returns 2.

3. Dropping the back edge the way `ebpf_project.cpp` does. Same packet, `n = 1`. The object executes the body once. A conversion that keeps the straight-line prefix and deletes edges 23→13 and 27→13 never stores the key and never calls helper 1, but can still return 2. The return matches and the map does not.

4. Null lookup is not a store. `n = 1`, lookup returns 0. Slot 23 jumps to 13, then slot 14 falls into the exit. Return is 2 and `counters` is unchanged. Treating `r0 == 0` as a pointer and executing slots 24–26 faults or writes address 0.

5. Clamp. `n = 9` (bytes `09 00 00 00`), packet length at least 4. The object sets `w7 = 8` and looks up keys 0..7 only. A model that compares `i < n` inside the loop, which the C comment says the compiler avoided, issues a ninth lookup with key 8. That key is outside `max_entries`.

## Status

ISSUES
