# fletcher32 observation

Observation report for `fletcher32` so a later implementer can compile this object. This file does not invent a shared ISA and it is not a conversion. Conversion result: **NOT CONVERTED**. No `.alive` file is emitted.

## Identity

- ELF: `/Volumes/SSD/bs/build/fletcher32/bpf.o`
- sha256 (computed, matches the expected digest): `80ee54d740ac5df55b3ef80d7ee3ac095f92fb95294861dfd2bec920081d9b26`
- Command: `shasum -a 256 /Volumes/SSD/bs/build/fletcher32/bpf.o`
- Notes: `/Volumes/SSD/bs/build/fletcher32/bpf.toml` (`source = "/Volumes/SSD/bs/libbpf-mcu/tests/xdp/fletcher32.c"`, `[xdp] size = 3216`)
- Producer C file read only as corroboration of the note path: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/fletcher32.c`
- Tools: Homebrew LLVM 23.1.1 `/opt/homebrew/opt/llvm/bin/llvm-readelf` and `/opt/homebrew/opt/llvm/bin/llvm-objdump`
- `decode_ebpf` was not executed. ACCEPT/REJECT below is a reading of `alive2/src/ebpf_decode.cpp`, checked by walking the same conditions over the 402 slots. The Rocq decoder was not executed either; the Rocq column names the constructor `decode_insn` returns for that opcode shape.

## File, endian, executable sections

`llvm-readelf -h`: ELF64, little endian (`ELFDATA2LSB`, magic `7f 45 4c 46 02 01 01`), type `REL`, machine `EM_BPF`, entry point `0`, no program headers, 27 section headers, flags 0. Instruction words are little-endian 8-byte slots (`code, regs, int16 off, int32 imm`). No `BPF_END` / byte-swap opcode (`0xd4` / `0xdc`) is present. Multi-byte packet values are assembled and split with explicit `lsh`/`or`/`rsh` of bytes, little-endian byte order in the packet.

Executable sections (`llvm-readelf -S`, flags include `X`):

| Index | Name | Type | File offset | Size | Flags | Role |
|---|---|---|---|---|---|---|
| 2 | `.text` | PROGBITS | `0x40` | **0** | AX | empty. Not the program. Shares the file offset with `xdp` only because its size is 0. |
| 3 | `xdp` | PROGBITS | `0x40` | `0xc90` = 3216 | AX | the program. 3216/8 = **402 slots**. |

No other section has the execute flag. `.text` must not be decoded as the program.

## Entries

- ELF `e_entry` is 0 because the file is relocatable. That is not a BPF entry.
- Symbol table (`.symtab`, 15 symbols): `fletcher32` is `FUNC GLOBAL`, value 0, size 3216, section index 3 (`xdp`). That is the only function entry. It starts at slot 0.
- `LICENSE` is `OBJECT GLOBAL`, size 4, section `license`. Bytes `47 50 4c 00` (`GPL`).
- `workload` is `OBJECT GLOBAL`, size 32, section `.maps`. The section contents are 32 zero bytes (`llvm-objdump -s -j .maps`). It is not an instruction operand.
- Source file symbol: `fletcher32.c`.

## Slots, LDDW, jumps

402 slots, each one instruction. **LDDW count is 0.** No opcode `0x18`. No second slot is consumed by a wide immediate. There is nothing to split into a pair.

Opcode census (first byte of each slot):

| Opcode | Count | Shape | C++ `decode_ebpf` | Rocq `decode_insn` |
|---|---:|---|---|---|
| `0x73` | 80 | STX, MEM, byte | REJECT class | `Pstore Byte` (register source) |
| `0x0c` | 61 | ALU32 ADD X | ACCEPT `EbAlu::Add` W32 | `Palu ADD W32` |
| `0xbc` | 60 | ALU32 MOV X | ACCEPT `EbAlu::Mov` W32 (offset 0) | `Palu MOV W32` |
| `0x71` | 34 | LDX, MEM, byte | REJECT class | `Pload Byte` |
| `0x56` | 29 | JMP32 JNE K | ACCEPT `EbJmp::Jne` W32 | `Pjmpcmp NE W32` |
| `0x05` | 28 | JMP JA | ACCEPT `EbJmp::Ja` (imm 0, off is the displacement) | `Pjmp64` |
| `0x74` | 26 | ALU32 RSH K | ACCEPT `EbAlu::Rsh` W32 | `Palu RSH W32` |
| `0x54` | 24 | ALU32 AND K | ACCEPT `EbAlu::And` W32 | `Palu AND W32` |
| `0x4c` | 14 | ALU32 OR X | ACCEPT `EbAlu::Or` W32 | `Palu OR W32` |
| `0x64` | 13 | ALU32 LSH K | ACCEPT `EbAlu::Lsh` W32 | `Palu LSH W32` |
| `0xa6` | 12 | JMP32 JLT K | ACCEPT `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` |
| `0xb4` | 5 | ALU32 MOV K | ACCEPT `EbAlu::Mov` W32 | `Palu MOV W32` |
| `0x61` | 3 | LDX, MEM, word | REJECT class | `Pload Word` |
| `0x04` | 3 | ALU32 ADD K | ACCEPT `EbAlu::Add` W32 | `Palu ADD W32` |
| `0xbf` | 2 | ALU64 MOV X | ACCEPT `EbAlu::Mov` W64 | `Palu MOV W64` |
| `0x07` | 2 | ALU64 ADD K | ACCEPT `EbAlu::Add` W64 | `Palu ADD W64` |
| `0x2d` | 2 | JMP JGT X | ACCEPT `EbJmp::Jgt` W64 | `Pjmpcmp (GT Unsigned) W64` |
| `0x1c` | 1 | ALU32 SUB X | ACCEPT `EbAlu::Sub` W32 | `Palu SUB W32` |
| `0x24` | 1 | ALU32 MUL K | ACCEPT `EbAlu::Mul` W32 | `Palu MUL W32` |
| `0x16` | 1 | JMP32 JEQ K | ACCEPT `EbJmp::Jeq` W32 | `Pjmpcmp EQ W32` |
| `0x95` | 1 | JMP EXIT | ACCEPT `EbJmp::Exit` | `Pret` |

Sum of counts is 402. Every ALU immediate form has source-register nibble 0 and offset 0. Every ALU register form has offset 0. EXIT at slot 395 has dst, src, offset, and imm all zero. JA immediates are 0. No CALL (`0x85`), no atomic mode (`opcode >> 5 == 6`), no halfword, no dword load/store, no signed load (`0x80` mode).

Registers named by an operand: r0–r8. r9 is unused. r10 is unused. There is no stack spill.

### Jump slots

Displacement is the 16-bit `off`. Target slot = index + 1 + off, which is `jump_target` in `alive2/src/ebpf_decode.cpp` for non-EXIT jumps (`ja_uses_imm` is false for JMP JA). All 72 targets are inside `0 .. 401`. The only non-positive displacement is slot 401.

| Slot | Kind | Target | Note |
|---:|---|---:|---|
| 5 | jmp jgt r5, r8, +389 | 395 | bounds, exit |
| 12 | jmp32 jlt r8, 24, +382 | 395 | bounds, exit |
| 15 | jmp jgt r8, r1, +379 | 395 | bounds, exit |
| 24 | jmp32 jlt r1, -20, +370 | 395 | unsigned; see counterexample |
| 27 | jmp32 jlt r3, 2, +89 | 117 | unrolled length |
| 35 | jmp32 jlt r3, 4, +81 | 117 | |
| 45 | jmp32 jlt r3, 6, +71 | 117 | |
| 53 | jmp32 jlt r3, 8, +63 | 117 | |
| 63 | jmp32 jlt r3, 10, +53 | 117 | |
| 71 | jmp32 jlt r3, 12, +45 | 117 | |
| 81 | jmp32 jlt r3, 14, +35 | 117 | |
| 89 | jmp32 jlt r3, 16, +27 | 117 | |
| 99 | jmp32 jlt r3, 18, +17 | 117 | |
| 107 | jmp32 jlt r3, 20, +9 | 117 | |
| 126 | jmp32 jeq r6, 0, +143 | 270 | even length skips the odd-byte tail |
| 127 | jmp32 jne r3, 1, +13 | 141 | |
| 140 | jmp ja +13 | 154 | |
| 141 | jmp32 jne r3, 3, +15 | 157 | |
| 156 | jmp ja +113 | 270 | |
| 157 | jmp32 jne r3, 5, +13 | 171 | |
| 170 | jmp ja +97 | 268 | |
| 171 | jmp32 jne r3, 7, +13 | 185 | |
| 184 | jmp ja +83 | 268 | |
| 185 | jmp32 jne r3, 9, +13 | 199 | |
| 198 | jmp ja +69 | 268 | |
| 199 | jmp32 jne r3, 11, +13 | 213 | |
| 212 | jmp ja +55 | 268 | |
| 213 | jmp32 jne r3, 13, +13 | 227 | |
| 226 | jmp ja +41 | 268 | |
| 227 | jmp32 jne r3, 15, +13 | 241 | |
| 240 | jmp ja +27 | 268 | |
| 241 | jmp32 jne r3, 17, +13 | 255 | |
| 254 | jmp ja +13 | 268 | |
| 255 | jmp32 jne r3, 19, +14 | 270 | |
| 281 | jmp32 jne r3, 1, +5 | 287 | store select |
| 286 | jmp ja +107 | 394 | |
| 287 | jmp32 jne r3, 2, +5 | 293 | |
| 292 | jmp ja +101 | 394 | |
| 293 | jmp32 jne r3, 3, +5 | 299 | |
| 298 | jmp ja +95 | 394 | |
| 299 | jmp32 jne r3, 4, +5 | 305 | |
| 304 | jmp ja +89 | 394 | |
| 305 | jmp32 jne r3, 5, +5 | 311 | |
| 310 | jmp ja +83 | 394 | |
| 311 | jmp32 jne r3, 6, +5 | 317 | |
| 316 | jmp ja +77 | 394 | |
| 317 | jmp32 jne r3, 7, +5 | 323 | |
| 322 | jmp ja +71 | 394 | |
| 323 | jmp32 jne r3, 8, +5 | 329 | |
| 328 | jmp ja +65 | 394 | |
| 329 | jmp32 jne r3, 9, +5 | 335 | |
| 334 | jmp ja +59 | 394 | |
| 335 | jmp32 jne r3, 10, +5 | 341 | |
| 340 | jmp ja +53 | 394 | |
| 341 | jmp32 jne r3, 11, +5 | 347 | |
| 346 | jmp ja +47 | 394 | |
| 347 | jmp32 jne r3, 12, +5 | 353 | |
| 352 | jmp ja +41 | 394 | |
| 353 | jmp32 jne r3, 13, +5 | 359 | |
| 358 | jmp ja +35 | 394 | |
| 359 | jmp32 jne r3, 14, +5 | 365 | |
| 364 | jmp ja +29 | 394 | |
| 365 | jmp32 jne r3, 15, +5 | 371 | |
| 370 | jmp ja +23 | 394 | |
| 371 | jmp32 jne r3, 16, +5 | 377 | |
| 376 | jmp ja +17 | 394 | |
| 377 | jmp32 jne r3, 17, +5 | 383 | |
| 382 | jmp ja +11 | 394 | |
| 383 | jmp32 jne r3, 18, +5 | 389 | |
| 388 | jmp ja +5 | 394 | |
| 389 | jmp32 jne r3, 19, +6 | 396 | |
| 395 | jmp exit | exit | r0 is the return |
| 401 | jmp ja -7 | 395 | backward edge onto exit, not a body loop |

## What the 402 slots do

Slot 0 sets `w0 = 0` (`XDP_ABORTED` if a later path does not overwrite it). Slots 1, 2, and 11 are the only word loads: `w8 = *(u32*)(r1+4)`, `w2 = *(u32*)(r1+0)`, `w1 = *(u32*)(r1+4)`. Those offsets are `xdp_md.data_end` and `xdp_md.data` (BTF type 17, and the three CO-RE records below). The other 34 loads and all 80 stores are unsigned byte operations on r2, which is the packet `data` pointer. Store offsets run through the bytes after the 8-byte header; each store arm writes four consecutive bytes. Success paths write `w0 = 2` at slot 394 or slot 400 (`XDP_PASS` in the C file) and reach slot 395. Reject paths jump to slot 395 with r0 still 0.

The C file's `#pragma unroll` loops (ten words, then an odd byte, then a store selected by `param`) are fully unrolled into the compare cascade above. There is no pc that returns to an earlier arithmetic slot.

The single backward edge is slot 401 `ja -7` to slot 395 `exit`. Reaching 401 stores four bytes, sets `w0 = 2`, then jumps to exit. Exit does not fall through. The edge does not re-execute the checksum.

## Relocations: raw object, CO-RE, map index

There is **no** relocation section for `xdp` or `.text`. `llvm-readelf -r` section names are only:

- `.rel.debug_info` (6) `R_BPF_64_ABS32` to debug sections
- `.rel.debug_str_offsets` (62) `R_BPF_64_ABS32` to `.debug_str`
- `.rel.debug_addr` (5) `R_BPF_64_ABS64` to `xdp` (three), `LICENSE`, `workload`
- `.rel.BTF` (2) `R_BPF_64_NODYLD32` to `workload` at offset `0x250` and `LICENSE` at offset `0x268`
- `.rel.BTF.ext` (318) `R_BPF_64_NODYLD32` to `xdp`
- `.rel.debug_frame` (2), `.rel.debug_line` (6)

Those are debug and BTF fixups. They are not instruction immediates.

Separate the three reference kinds:

- **Raw object reference.** Symbols `fletcher32` (section `xdp`), `LICENSE` (section `license`), `workload` (section `.maps`). `.rel.debug_addr` points at those symbols with `R_BPF_64_ABS64`. That is a DWARF address, not a packet or map access.
- **CO-RE / BTF.ext field offset, not an ELF `R_*` on the insn.** `.BTF.ext` header: magic `0xeb9f`, version 1, `hdr_len` 32. Core-relo subsection at header-relative off `0x13c0`, length `0x3c`: record size 16, section-name string off `0xe0` (`xdp`), count 3. Each record is `(insn_off, type_id, access_str_off, kind)`:

  | insn byte | slot | type_id | kind | access string | encoded `off` already in the slot |
  |---:|---:|---:|---:|---|---|
  | `0x8` | 1 | 17 | 0 | `0:1` | 4 |
  | `0x10` | 2 | 17 | 0 | `0:0` | 0 |
  | `0x58` | 11 | 17 | 0 | `0:1` | 4 |

  `llvm-objdump -d -r` prints these as `CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)` and `struct xdp_md::data (0:0)`. Kind 0 matches that `byte_off` label. Type 17 is BTF `struct xdp_md` with `data` at bit 0 and `data_end` at bit 32, so the bytes already in the insn match this object's own BTF. A loader may still patch the 16-bit offset if the target layout differs. This is not an `R_BPF_64_64` text relocation.
- **Map-index / map-fd reference.** None in the instruction stream. No LDDW, so no `src_reg` pseudo-type (`PSEUDO_MAP_FD` = 1, `PSEUDO_MAP_IDX` = 5, and the other `pseudo_ptr_ty` values in `ebpfSyntax.v`). No `R_BPF_64_64`. The `workload` symbol is not loaded by any slot.

## Map and helper facts that are not instruction references

BTF (section `.BTF` at file `0x22a4`, size `0x6d5`, parsed, not guessed):

- `[11] STRUCT exec_val` size 32: `w0`..`w7` as `__u32` at bit offsets 0, 32, …, 224.
- `[14] STRUCT` anonymous size 32: `type` → ptr to int array nelems **1**; `max_entries` → ptr to int array nelems **2**; `key` → ptr to `__u8`; `value` → ptr to `exec_val`.
- `[15] VAR workload` type 14, linkage 1. `[23] DATASEC .maps` places that var at offset 0, size 32.
- `[17] STRUCT xdp_md` size 24, fields as used by the CO-RE records.
- `[19] FUNC fletcher32` proto `(ctx: ptr xdp_md) -> int`.

The nelems-1 / nelems-2 encoding is the libbpf `__uint` pattern. The C file states `BPF_MAP_TYPE_HASH` and `max_entries` 2. The `.maps` bytes themselves are zeros; the integers are not stored as an insn immediate. The comment in the C file says the test app copies the map into the context and back. **This program never calls a helper and never touches the map.**

Helper flag: **no**. Map flag for the instruction stream: **no**. Map object present in the ELF: **yes, unused by these 402 slots**.

## Semantic rules actually read

Read and used:

- `alive2/src/ebpf_decode.cpp` entire file (245 lines). Class mask `0x07`. ALU/ALU64 and JMP/JMP32 only. The `else` at lines 164–167 throws `unsupported class in opcode`. ALU ops accepted by the `switch` at lines 99–108 plus MOV at lines 83–95: Add, Sub, Mul, Or, And, Lsh, Rsh, Xor, Arsh, Mov. JMP ops at lines 130–156: Exit, Ja, Jeq, Jne, Jgt, Jge, Jlt, Jle, Jsgt, Jsge, Jslt, Jsle. `jump_target` at lines 26–31 is `index + 1 + off` unless EXIT.
- `alive2/src/ebpf.h` entire file. `EbInsn::op` is `variant<EbAlu, EbJmp>` only. There is no load, store, or call alternative.
- `alive2/src/ebpf_lift.cpp` lines 102–119 (`run` copies `loop` into `LiftInfo`), 138–145 (`bare_mov`), 182–282 (`imm64` sign-extends only ALU64 immediates; `build_blocks` sets `loop = true` when a jump target is `<=` the jump slot), 347–362 (`pointer_alu` / `pointer_jmp`), 396–439 (`schedule`), 460–539 (`emit` / `emit_alu`: W32 is trunc to i32, operate, `zext64`), 553–558 (shift amount masked with 31 or 63 unless `ShiftWithoutMask`), 561–694 (`emit_wide`, `emit_narrow`, `arith_op`, `shift_op`, `icmp_cond`), 713–966 (`concrete`: `MemorySummary::Empty` unless a `MemInstr` appears; a `MemInstr` sets `Changed` and then `stop_unsupported`. `BinOp` concrete cases are only Add, Sub, And, UDiv, SDiv. `ICmp` concrete cases are only EQ and UGT).
- `alive2/rocq/upstream/theories/ebpfSyntax.v` lines 99–245. `sizeOp` Byte/HalfWord/Word/DBWord. `aluOp` including ADD, SUB, MUL, OR, AND, LSH, RSH, MOV. `cmpOp` EQ/NE/GT/LT with `signedness`. `instruction` includes `Pload`, `Pstore`, `Palu`, `Pjmp64`, `Pjmpcmp`, `Pret`, `Plddw`, `Pcall`. `pseudo_ptr_ty` lists map fd and map index. The NEG comment at line 158 says `dst = ~dst`; `eval_alu32` uses `Val.neg` (negation). This object has no NEG, so that comment was not used to classify a slot.
- `alive2/rocq/upstream/theories/ebpfDecoder.v` lines 13–246. `decode_insn` accepts ALU32/ALU64 codes `0x0`–`0xc` (with DIV/MOD/MOV/END side conditions), JMP JA/EXIT/conditional codes including `0x2` JGT, `0x5` JNE, `0xa` JLT, `0x1` JEQ, and MEM-mode (`opcode >> 5 == 3`) LDX as `Pload` and STX as `Pstore`. Size bits `(opcode >> 3) & 3`: 0 Word, 2 Byte. `decode_lddw_insn` maps src r0..r6 onto pseudo pointer kinds. Not used: this object has no `0x18`.
- `alive2/rocq/upstream/theories/ebpfBinSem.v` lines 331–498 and 500–659 and 881–905. `eval_alu32` takes `Val.loword` of both operands and `Val.longofintu` of the result (32-bit op, zero-extend). `eval_alu64` is the 64-bit `Val.*l` family. Shifts go through `eval_shift_mask`. `eval_cmp32` / `eval_cmp64` use unsigned `cmpu`/`cmplu` for GT/LT/EQ/NE. `exec_jmpcmp` can return `Stuck` if the comparison option is `None`. `exec_load` turns a `Vlong` address into a pointer only via `cast_i2p` over `addr_map`, then `loadv_unaligned` (`Mint8unsigned` or `Mint32`) and `load_value_casting` (zero-extend a `Vint`). `exec_store` uses `storev_unaligned` `Mint8unsigned` for Byte. `exec_instr` dispatches `Pload` to `exec_load` and `Pstore` to `exec_store`. `Pcall` other than `CallInternal`, and every other unmatched instruction, is `Stuck`.

Not read, so not used as a rule: `alive2/rocq/upstream/theories/ebpfState.v`, `SCLanguage.v`, `GlobalSem.v`, `CMemoryModel.v`, `Nondeterminism.v`, `alive2/rocq/upstream/validator/Validation.v`, `Extraction.v`. No proof was run. No theorem in the files above is applied to this ELF.

## IR mapping against the existing C++ lifter only

The lifter never sees this object. `decode_ebpf` throws at slot 1 (`61 18 04 00 …`, class LDX). Mapping below is what the current emitter would do for the slots it knows, and what it cannot name for the rest. It is not a successful lift.

| Object form | Slots | Existing IR if the decoder accepted the insn |
|---|---:|---|
| alu32 mov/add/sub/mul/or/and/lsh/rsh | 207 ALU32 | `emit_alu`: `Trunc` to i32, then `BinOp` Add/Sub/Mul/Or/And or `Shl`/`LShr` with amount `& 31`, then `ZExt` to i64. MOV is the truncated source, then `ZExt`. Immediates are zero-extended to i64 before the trunc (`imm64` sign-extends only W64). |
| alu64 mov r5,r2 and r8,r2 | 3, 13 | `emit_wide` MOV returns the source value unchanged (64-bit copy). |
| alu64 add imm 8 and imm 0x20 | 4, 14 | `BinOp` i64 Add. Both immediates are non-negative, so sign-extension does not change them. `pointer_alu` is true only when an origin is already `RegOrigin::Pointer`. A zero `LiftInit` does not mark r1 as a pointer; the `Poison` pointer origin is only for `LiftInit` that is not `Zero`, and only on r1 and r10 (`ebpf_lift.cpp` lines 315–321). These adds would not become pointer arithmetic unless the caller seeded that origin. |
| jmp32 jlt/jne/jeq, jmp jgt | 44 conditional | `emit_cmp`: W32 compares `Trunc` both sides and uses `ICmp` ULT, NE, or EQ. W64 `jgt` is `ICmp` UGT on the full i64. Branch to the target block or fall-through. |
| jmp ja, including slot 401 | 28 | Unconditional `Branch` to the target block. Slot 401's target 395 is `<= 401`, so `build_blocks` sets `loop = true` even though the target is exit. |
| jmp exit | 395 | Exit edge, no ALU IR. Concrete trace records `StepStatus::Exit` and r0. |
| ldx.w / ldx.b / stx.b | 3 + 34 + 80 | No constructor. `EbInsn` cannot hold them. `emit` has no load/store case. `concrete` only notices `MemInstr` to mark memory changed and then stops unsupported. There is no packet memory, no context pointer, and no CO-RE offset in the IR. |

Concrete-trace gap even for the ALU/JMP subset, read at `ebpf_lift.cpp` lines 873–934: `Or`, `Mul`, `Shl`, and `LShr` hit `known = false` and `stop_unsupported`. `ICmp::ULT` and `ICmp::NE` are not handled (only EQ and UGT). This program's dominant ALU ops are or/shift and its dominant branches are jlt/jne. A concrete trace of the ALU skeleton would stop on the first such op. That is independent of the memory rejection, and it is not a conversion.

Shift constants in this object are 8, 16, and 24. The W32 mask `& 31` does not change them. The Rocq `eval_shift_mask` and the C++ mask agree on those constants. Not a reason to mark the object converted.

## Memory, helper, map, loop requirements for a later compiler

- **Context memory.** Three unsigned 32-bit loads from r1 at offset 0 (`data`) and offset 4 (`data_end`), subject to the three CO-RE `byte_off` records. BTF says both fields are `__u32`. The 32-bit load must zero the high half before the later 64-bit `mov`/`add`/`jgt`.
- **Packet memory.** 34 unsigned byte loads and 80 unsigned byte stores through r2 + a constant offset. Stores are the observable result (four little-endian bytes of the checksum at a `param`-selected offset). Bounds checks are the explicit `jgt`/`jlt` slots 5, 12, 15, and 24, not a separate verifier pass inside the object.
- **No stack.** r10 unused.
- **No helper.** Do not invent `bpf_map_lookup_elem` or a checksum helper. None is called.
- **No map op.** The hash map exists for the harness. Compiling the 402 slots must not emit a map lookup. Dropping the symbol would lose the harness contract; treating it as an insn input would invent a reference that is not in the text.
- **Loop.** Do not model an iterating loop. The C loops are unrolled. The only back edge is slot 401 → 395 (exit). A detector that sets `loop` on `target <= pc` (`ebpf_lift.cpp:228`) will flag this object. That flag must not be read as "needs a loop invariant over the checksum."
- **Endian.** ELF and insn encoding are little endian. Packet words are built from bytes. Do not insert `BPF_END`.
- **Return.** r0 is 0 on the reject edges into slot 395, and 2 on the two success stores (slots 394 and 400). No other exit.

## Conversion result

**NOT CONVERTED.**

`decode_ebpf` rejects slot 1, opcode `0x61`, class LDX, before any IR block is built. 117 of 402 slots are in that rejected class (34 `ldx.b`, 3 `ldx.w`, 80 `stx.b`). The other 285 slots are ALU or JMP forms the same function accepts, but they are not a program without the loads and the stores. Calling the memory model "unsupported" is the decoder's own error string; it is not a successful classification of the object as converted.

No `.alive` file is written.

## Proof coverage

- Rocq `decode_insn` has a constructor for every opcode byte in this object, including the 117 memory slots (`Pload` / `Pstore`) and the ALU/JMP slots. That is a decoder match, not a proof about this ELF.
- Rocq `exec_load` / `exec_store` define byte and word memory. `exec_load` turns a `Vlong` into a pointer only through `cast_i2p` over `addr_map`, and `None` from that cast or from `load` is `Stuck` (`ebpfBinSem.v` lines 575–588). Nothing read here supplies an `addr_map` for the packet or for `xdp_md`. `exec_jmpcmp` is `Stuck` when the comparison is `None` (lines 484–497). `eval_cmp64` calls `Val.cmplu_bool`; CompCert's definition of that function was not read, so this report does not claim what a `Vptr`/`Vlong` mix returns.
- The C++ lifter has no memory IR, so there is no Alive2 trace to compare with `exec_instr`.
- `Validation.v` was not read. No equivalence to the Fletcher-32 in the C file (RFC 3720 / Wikipedia, per the comment in `fletcher32.c`) was checked.
- CO-RE patching is not a rule in the files that were read.

## Counterexample

Do not treat "r0 becomes 2" as the whole spec. The stores are the result.

Input that separates a signed mis-read of slot 24 from the encoding: `data_end - data >= 32` (slots 5, 12, and 15 fall through; slot 12's `avail` is that difference minus 8) and the word at `data+4` is `param = 21`. Slot 23 is `w1 += -21`, so w1 becomes 0. Slot 24 is opcode `0xa6` (`JLT` unsigned, not `0xc6` `JSLT`) with immediate `-20` (`0xffffffec`). Unsigned `0 < 0xffffffec` is true, so the slot jumps to 395 and returns 0 with no store. Signed `0 < -20` is false. The fall-through then misses every `jne` arm for 1, 3, …, 19 (slot 255 targets 270) and every store arm for 1..19 (slot 389 targets 396), writes four bytes at slots 396–399, sets `w0 = 2` at slot 400, and jumps to exit. The correct object aborts; the signed reading stores and returns 2.

A second, independent failure: delete or skip the 80 `stx.b` slots and still return 2 on a legal `param` in 1..20. r0 matches `XDP_PASS` and the four checksum bytes in the packet do not. Any conversion that only preserves r0 is wrong.

## Instruction list

Classified from the bytes at file offset `0x40`, length `0xc90`. `C++ decode ACCEPT` means the `ebpf_decode.cpp` conditions read above. `REJECT` means the class `else` at line 164.

  0  b400000000000000  alu32 mov r0, 0    C++ decode ACCEPT (alu32 mov); Rocq Palu
  1  6118040000000000  ldx.w dst r8 src r1 off 4    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Word
  2  6112000000000000  ldx.w dst r2 src r1 off 0    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Word
  3  bf25000000000000  alu64 mov r5, r2    C++ decode ACCEPT (alu64 mov); Rocq Palu
  4  0705000008000000  alu64 add r5, 8    C++ decode ACCEPT (alu64 add); Rocq Palu
  5  2d85850100000000  jmp jgt r5, r8, 389 -> slot 395    C++ decode ACCEPT; Rocq Pjmpcmp
  6  7127060000000000  ldx.b dst r7 src r2 off 6    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
  7  7123050000000000  ldx.b dst r3 src r2 off 5    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
  8  7124070000000000  ldx.b dst r4 src r2 off 7    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
  9  1c58000000000000  alu32 sub r8, r5    C++ decode ACCEPT (alu32 sub); Rocq Palu
 10  7126040000000000  ldx.b dst r6 src r2 off 4    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 11  6111040000000000  ldx.w dst r1 src r1 off 4    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Word
 12  a6087e0118000000  jmp32 jlt r8, 24, 382 -> slot 395    C++ decode ACCEPT; Rocq Pjmpcmp
 13  bf28000000000000  alu64 mov r8, r2    C++ decode ACCEPT (alu64 mov); Rocq Palu
 14  0708000020000000  alu64 add r8, 32    C++ decode ACCEPT (alu64 add); Rocq Palu
 15  2d187b0100000000  jmp jgt r8, r1, 379 -> slot 395    C++ decode ACCEPT; Rocq Pjmpcmp
 16  6407000010000000  alu32 lsh r7, 16    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 17  6403000008000000  alu32 lsh r3, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 18  4c73000000000000  alu32 or r3, r7    C++ decode ACCEPT (alu32 or); Rocq Palu
 19  6404000018000000  alu32 lsh r4, 24    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 20  4c43000000000000  alu32 or r3, r4    C++ decode ACCEPT (alu32 or); Rocq Palu
 21  4c63000000000000  alu32 or r3, r6    C++ decode ACCEPT (alu32 or); Rocq Palu
 22  bc31000000000000  alu32 mov r1, r3    C++ decode ACCEPT (alu32 mov); Rocq Palu
 23  04010000ebffffff  alu32 add r1, -21    C++ decode ACCEPT (alu32 add); Rocq Palu
 24  a6017201ecffffff  jmp32 jlt r1, -20, 370 -> slot 395    C++ decode ACCEPT; Rocq Pjmpcmp
 25  b4040000ffff0000  alu32 mov r4, 65535    C++ decode ACCEPT (alu32 mov); Rocq Palu
 26  b4010000ffff0000  alu32 mov r1, 65535    C++ decode ACCEPT (alu32 mov); Rocq Palu
 27  a603590002000000  jmp32 jlt r3, 2, 89 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
 28  7124080000000000  ldx.b dst r4 src r2 off 8    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 29  7121090000000000  ldx.b dst r1 src r2 off 9    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 30  6401000008000000  alu32 lsh r1, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 31  4c41000000000000  alu32 or r1, r4    C++ decode ACCEPT (alu32 or); Rocq Palu
 32  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
 33  04040000feff0100  alu32 add r4, 131070    C++ decode ACCEPT (alu32 add); Rocq Palu
 34  04010000ffff0000  alu32 add r1, 65535    C++ decode ACCEPT (alu32 add); Rocq Palu
 35  a603510004000000  jmp32 jlt r3, 4, 81 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
 36  71270a0000000000  ldx.b dst r7 src r2 off 10    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 37  71200b0000000000  ldx.b dst r0 src r2 off 11    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 38  6400000008000000  alu32 lsh r0, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 39  4c70000000000000  alu32 or r0, r7    C++ decode ACCEPT (alu32 or); Rocq Palu
 40  0c10000000000000  alu32 add r0, r1    C++ decode ACCEPT (alu32 add); Rocq Palu
 41  bc07000000000000  alu32 mov r7, r0    C++ decode ACCEPT (alu32 mov); Rocq Palu
 42  0c47000000000000  alu32 add r7, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
 43  bc74000000000000  alu32 mov r4, r7    C++ decode ACCEPT (alu32 mov); Rocq Palu
 44  bc01000000000000  alu32 mov r1, r0    C++ decode ACCEPT (alu32 mov); Rocq Palu
 45  a603470006000000  jmp32 jlt r3, 6, 71 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
 46  71240c0000000000  ldx.b dst r4 src r2 off 12    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 47  71210d0000000000  ldx.b dst r1 src r2 off 13    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 48  6401000008000000  alu32 lsh r1, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 49  4c41000000000000  alu32 or r1, r4    C++ decode ACCEPT (alu32 or); Rocq Palu
 50  0c01000000000000  alu32 add r1, r0    C++ decode ACCEPT (alu32 add); Rocq Palu
 51  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
 52  0c74000000000000  alu32 add r4, r7    C++ decode ACCEPT (alu32 add); Rocq Palu
 53  a6033f0008000000  jmp32 jlt r3, 8, 63 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
 54  71270e0000000000  ldx.b dst r7 src r2 off 14    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 55  71200f0000000000  ldx.b dst r0 src r2 off 15    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 56  6400000008000000  alu32 lsh r0, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 57  4c70000000000000  alu32 or r0, r7    C++ decode ACCEPT (alu32 or); Rocq Palu
 58  0c10000000000000  alu32 add r0, r1    C++ decode ACCEPT (alu32 add); Rocq Palu
 59  bc07000000000000  alu32 mov r7, r0    C++ decode ACCEPT (alu32 mov); Rocq Palu
 60  0c47000000000000  alu32 add r7, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
 61  bc74000000000000  alu32 mov r4, r7    C++ decode ACCEPT (alu32 mov); Rocq Palu
 62  bc01000000000000  alu32 mov r1, r0    C++ decode ACCEPT (alu32 mov); Rocq Palu
 63  a60335000a000000  jmp32 jlt r3, 10, 53 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
 64  7124100000000000  ldx.b dst r4 src r2 off 16    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 65  7121110000000000  ldx.b dst r1 src r2 off 17    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 66  6401000008000000  alu32 lsh r1, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 67  4c41000000000000  alu32 or r1, r4    C++ decode ACCEPT (alu32 or); Rocq Palu
 68  0c01000000000000  alu32 add r1, r0    C++ decode ACCEPT (alu32 add); Rocq Palu
 69  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
 70  0c74000000000000  alu32 add r4, r7    C++ decode ACCEPT (alu32 add); Rocq Palu
 71  a6032d000c000000  jmp32 jlt r3, 12, 45 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
 72  7127120000000000  ldx.b dst r7 src r2 off 18    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 73  7120130000000000  ldx.b dst r0 src r2 off 19    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 74  6400000008000000  alu32 lsh r0, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 75  4c70000000000000  alu32 or r0, r7    C++ decode ACCEPT (alu32 or); Rocq Palu
 76  0c10000000000000  alu32 add r0, r1    C++ decode ACCEPT (alu32 add); Rocq Palu
 77  bc07000000000000  alu32 mov r7, r0    C++ decode ACCEPT (alu32 mov); Rocq Palu
 78  0c47000000000000  alu32 add r7, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
 79  bc74000000000000  alu32 mov r4, r7    C++ decode ACCEPT (alu32 mov); Rocq Palu
 80  bc01000000000000  alu32 mov r1, r0    C++ decode ACCEPT (alu32 mov); Rocq Palu
 81  a60323000e000000  jmp32 jlt r3, 14, 35 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
 82  7124140000000000  ldx.b dst r4 src r2 off 20    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 83  7121150000000000  ldx.b dst r1 src r2 off 21    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 84  6401000008000000  alu32 lsh r1, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 85  4c41000000000000  alu32 or r1, r4    C++ decode ACCEPT (alu32 or); Rocq Palu
 86  0c01000000000000  alu32 add r1, r0    C++ decode ACCEPT (alu32 add); Rocq Palu
 87  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
 88  0c74000000000000  alu32 add r4, r7    C++ decode ACCEPT (alu32 add); Rocq Palu
 89  a6031b0010000000  jmp32 jlt r3, 16, 27 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
 90  7127160000000000  ldx.b dst r7 src r2 off 22    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 91  7120170000000000  ldx.b dst r0 src r2 off 23    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
 92  6400000008000000  alu32 lsh r0, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
 93  4c70000000000000  alu32 or r0, r7    C++ decode ACCEPT (alu32 or); Rocq Palu
 94  0c10000000000000  alu32 add r0, r1    C++ decode ACCEPT (alu32 add); Rocq Palu
 95  bc07000000000000  alu32 mov r7, r0    C++ decode ACCEPT (alu32 mov); Rocq Palu
 96  0c47000000000000  alu32 add r7, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
 97  bc74000000000000  alu32 mov r4, r7    C++ decode ACCEPT (alu32 mov); Rocq Palu
 98  bc01000000000000  alu32 mov r1, r0    C++ decode ACCEPT (alu32 mov); Rocq Palu
 99  a603110012000000  jmp32 jlt r3, 18, 17 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
100  7124180000000000  ldx.b dst r4 src r2 off 24    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
101  7121190000000000  ldx.b dst r1 src r2 off 25    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
102  6401000008000000  alu32 lsh r1, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
103  4c41000000000000  alu32 or r1, r4    C++ decode ACCEPT (alu32 or); Rocq Palu
104  0c01000000000000  alu32 add r1, r0    C++ decode ACCEPT (alu32 add); Rocq Palu
105  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
106  0c74000000000000  alu32 add r4, r7    C++ decode ACCEPT (alu32 add); Rocq Palu
107  a603090014000000  jmp32 jlt r3, 20, 9 -> slot 117    C++ decode ACCEPT; Rocq Pjmpcmp
108  71201a0000000000  ldx.b dst r0 src r2 off 26    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
109  71271b0000000000  ldx.b dst r7 src r2 off 27    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
110  6407000008000000  alu32 lsh r7, 8    C++ decode ACCEPT (alu32 lsh); Rocq Palu
111  4c07000000000000  alu32 or r7, r0    C++ decode ACCEPT (alu32 or); Rocq Palu
112  0c17000000000000  alu32 add r7, r1    C++ decode ACCEPT (alu32 add); Rocq Palu
113  bc71000000000000  alu32 mov r1, r7    C++ decode ACCEPT (alu32 mov); Rocq Palu
114  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
115  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
116  bc71000000000000  alu32 mov r1, r7    C++ decode ACCEPT (alu32 mov); Rocq Palu
117  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
118  7400000010000000  alu32 rsh r0, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
119  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
120  0c01000000000000  alu32 add r1, r0    C++ decode ACCEPT (alu32 add); Rocq Palu
121  bc40000000000000  alu32 mov r0, r4    C++ decode ACCEPT (alu32 mov); Rocq Palu
122  7400000010000000  alu32 rsh r0, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
123  54040000ffff0000  alu32 and r4, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
124  0c04000000000000  alu32 add r4, r0    C++ decode ACCEPT (alu32 add); Rocq Palu
125  5406000001000000  alu32 and r6, 1    C++ decode ACCEPT (alu32 and); Rocq Palu
126  16068f0000000000  jmp32 jeq r6, 0, 143 -> slot 270    C++ decode ACCEPT; Rocq Pjmpcmp
127  56030d0001000000  jmp32 jne r3, 1, 13 -> slot 141    C++ decode ACCEPT; Rocq Pjmpcmp
128  7155000000000000  ldx.b dst r5 src r5 off 0    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
129  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
130  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
131  7400000010000000  alu32 rsh r0, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
132  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
133  54050000ffff0000  alu32 and r5, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
134  0c05000000000000  alu32 add r5, r0    C++ decode ACCEPT (alu32 add); Rocq Palu
135  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
136  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
137  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
138  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
139  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
140  05000d0000000000  jmp ja 13 -> slot 154    C++ decode ACCEPT (JA); Rocq Pjmp64
141  56030f0003000000  jmp32 jne r3, 3, 15 -> slot 157    C++ decode ACCEPT; Rocq Pjmpcmp
142  71250a0000000000  ldx.b dst r5 src r2 off 10    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
143  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
144  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
145  7400000010000000  alu32 rsh r0, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
146  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
147  54050000ffff0000  alu32 and r5, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
148  0c05000000000000  alu32 add r5, r0    C++ decode ACCEPT (alu32 add); Rocq Palu
149  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
150  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
151  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
152  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
153  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
154  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
155  bc51000000000000  alu32 mov r1, r5    C++ decode ACCEPT (alu32 mov); Rocq Palu
156  0500710000000000  jmp ja 113 -> slot 270    C++ decode ACCEPT (JA); Rocq Pjmp64
157  56030d0005000000  jmp32 jne r3, 5, 13 -> slot 171    C++ decode ACCEPT; Rocq Pjmpcmp
158  71250c0000000000  ldx.b dst r5 src r2 off 12    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
159  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
160  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
161  7405000010000000  alu32 rsh r5, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
162  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
163  54000000ffff0000  alu32 and r0, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
164  0c50000000000000  alu32 add r0, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
165  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
166  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
167  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
168  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
169  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
170  0500610000000000  jmp ja 97 -> slot 268    C++ decode ACCEPT (JA); Rocq Pjmp64
171  56030d0007000000  jmp32 jne r3, 7, 13 -> slot 185    C++ decode ACCEPT; Rocq Pjmpcmp
172  71250e0000000000  ldx.b dst r5 src r2 off 14    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
173  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
174  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
175  7405000010000000  alu32 rsh r5, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
176  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
177  54000000ffff0000  alu32 and r0, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
178  0c50000000000000  alu32 add r0, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
179  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
180  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
181  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
182  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
183  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
184  0500530000000000  jmp ja 83 -> slot 268    C++ decode ACCEPT (JA); Rocq Pjmp64
185  56030d0009000000  jmp32 jne r3, 9, 13 -> slot 199    C++ decode ACCEPT; Rocq Pjmpcmp
186  7125100000000000  ldx.b dst r5 src r2 off 16    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
187  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
188  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
189  7405000010000000  alu32 rsh r5, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
190  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
191  54000000ffff0000  alu32 and r0, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
192  0c50000000000000  alu32 add r0, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
193  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
194  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
195  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
196  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
197  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
198  0500450000000000  jmp ja 69 -> slot 268    C++ decode ACCEPT (JA); Rocq Pjmp64
199  56030d000b000000  jmp32 jne r3, 11, 13 -> slot 213    C++ decode ACCEPT; Rocq Pjmpcmp
200  7125120000000000  ldx.b dst r5 src r2 off 18    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
201  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
202  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
203  7405000010000000  alu32 rsh r5, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
204  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
205  54000000ffff0000  alu32 and r0, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
206  0c50000000000000  alu32 add r0, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
207  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
208  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
209  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
210  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
211  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
212  0500370000000000  jmp ja 55 -> slot 268    C++ decode ACCEPT (JA); Rocq Pjmp64
213  56030d000d000000  jmp32 jne r3, 13, 13 -> slot 227    C++ decode ACCEPT; Rocq Pjmpcmp
214  7125140000000000  ldx.b dst r5 src r2 off 20    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
215  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
216  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
217  7405000010000000  alu32 rsh r5, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
218  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
219  54000000ffff0000  alu32 and r0, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
220  0c50000000000000  alu32 add r0, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
221  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
222  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
223  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
224  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
225  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
226  0500290000000000  jmp ja 41 -> slot 268    C++ decode ACCEPT (JA); Rocq Pjmp64
227  56030d000f000000  jmp32 jne r3, 15, 13 -> slot 241    C++ decode ACCEPT; Rocq Pjmpcmp
228  7125160000000000  ldx.b dst r5 src r2 off 22    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
229  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
230  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
231  7405000010000000  alu32 rsh r5, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
232  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
233  54000000ffff0000  alu32 and r0, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
234  0c50000000000000  alu32 add r0, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
235  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
236  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
237  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
238  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
239  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
240  05001b0000000000  jmp ja 27 -> slot 268    C++ decode ACCEPT (JA); Rocq Pjmp64
241  56030d0011000000  jmp32 jne r3, 17, 13 -> slot 255    C++ decode ACCEPT; Rocq Pjmpcmp
242  7125180000000000  ldx.b dst r5 src r2 off 24    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
243  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
244  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
245  7405000010000000  alu32 rsh r5, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
246  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
247  54000000ffff0000  alu32 and r0, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
248  0c50000000000000  alu32 add r0, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
249  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
250  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
251  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
252  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
253  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
254  05000d0000000000  jmp ja 13 -> slot 268    C++ decode ACCEPT (JA); Rocq Pjmp64
255  56030e0013000000  jmp32 jne r3, 19, 14 -> slot 270    C++ decode ACCEPT; Rocq Pjmpcmp
256  71251a0000000000  ldx.b dst r5 src r2 off 26    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pload Byte
257  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
258  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
259  7405000010000000  alu32 rsh r5, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
260  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
261  54000000ffff0000  alu32 and r0, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
262  0c50000000000000  alu32 add r0, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
263  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
264  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
265  7404000010000000  alu32 rsh r4, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
266  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
267  0c41000000000000  alu32 add r1, r4    C++ decode ACCEPT (alu32 add); Rocq Palu
268  bc14000000000000  alu32 mov r4, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
269  bc01000000000000  alu32 mov r1, r0    C++ decode ACCEPT (alu32 mov); Rocq Palu
270  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
271  7405000010000000  alu32 rsh r5, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
272  54010000ffff0000  alu32 and r1, 65535    C++ decode ACCEPT (alu32 and); Rocq Palu
273  0c51000000000000  alu32 add r1, r5    C++ decode ACCEPT (alu32 add); Rocq Palu
274  2404000001000100  alu32 mul r4, 65537    C++ decode ACCEPT (alu32 mul); Rocq Palu
275  bc10000000000000  alu32 mov r0, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
276  4c40000000000000  alu32 or r0, r4    C++ decode ACCEPT (alu32 or); Rocq Palu
277  7404000018000000  alu32 rsh r4, 24    C++ decode ACCEPT (alu32 rsh); Rocq Palu
278  bc15000000000000  alu32 mov r5, r1    C++ decode ACCEPT (alu32 mov); Rocq Palu
279  7405000008000000  alu32 rsh r5, 8    C++ decode ACCEPT (alu32 rsh); Rocq Palu
280  7400000010000000  alu32 rsh r0, 16    C++ decode ACCEPT (alu32 rsh); Rocq Palu
281  5603050001000000  jmp32 jne r3, 1, 5 -> slot 287    C++ decode ACCEPT; Rocq Pjmpcmp
282  73420c0000000000  stx.b dst r2 src r4 off 12    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
283  73020b0000000000  stx.b dst r2 src r0 off 11    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
284  73520a0000000000  stx.b dst r2 src r5 off 10    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
285  7312090000000000  stx.b dst r2 src r1 off 9    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
286  05006b0000000000  jmp ja 107 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
287  5603050002000000  jmp32 jne r3, 2, 5 -> slot 293    C++ decode ACCEPT; Rocq Pjmpcmp
288  73420d0000000000  stx.b dst r2 src r4 off 13    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
289  73020c0000000000  stx.b dst r2 src r0 off 12    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
290  73520b0000000000  stx.b dst r2 src r5 off 11    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
291  73120a0000000000  stx.b dst r2 src r1 off 10    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
292  0500650000000000  jmp ja 101 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
293  5603050003000000  jmp32 jne r3, 3, 5 -> slot 299    C++ decode ACCEPT; Rocq Pjmpcmp
294  73420e0000000000  stx.b dst r2 src r4 off 14    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
295  73020d0000000000  stx.b dst r2 src r0 off 13    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
296  73520c0000000000  stx.b dst r2 src r5 off 12    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
297  73120b0000000000  stx.b dst r2 src r1 off 11    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
298  05005f0000000000  jmp ja 95 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
299  5603050004000000  jmp32 jne r3, 4, 5 -> slot 305    C++ decode ACCEPT; Rocq Pjmpcmp
300  73420f0000000000  stx.b dst r2 src r4 off 15    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
301  73020e0000000000  stx.b dst r2 src r0 off 14    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
302  73520d0000000000  stx.b dst r2 src r5 off 13    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
303  73120c0000000000  stx.b dst r2 src r1 off 12    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
304  0500590000000000  jmp ja 89 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
305  5603050005000000  jmp32 jne r3, 5, 5 -> slot 311    C++ decode ACCEPT; Rocq Pjmpcmp
306  7342100000000000  stx.b dst r2 src r4 off 16    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
307  73020f0000000000  stx.b dst r2 src r0 off 15    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
308  73520e0000000000  stx.b dst r2 src r5 off 14    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
309  73120d0000000000  stx.b dst r2 src r1 off 13    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
310  0500530000000000  jmp ja 83 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
311  5603050006000000  jmp32 jne r3, 6, 5 -> slot 317    C++ decode ACCEPT; Rocq Pjmpcmp
312  7342110000000000  stx.b dst r2 src r4 off 17    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
313  7302100000000000  stx.b dst r2 src r0 off 16    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
314  73520f0000000000  stx.b dst r2 src r5 off 15    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
315  73120e0000000000  stx.b dst r2 src r1 off 14    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
316  05004d0000000000  jmp ja 77 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
317  5603050007000000  jmp32 jne r3, 7, 5 -> slot 323    C++ decode ACCEPT; Rocq Pjmpcmp
318  7342120000000000  stx.b dst r2 src r4 off 18    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
319  7302110000000000  stx.b dst r2 src r0 off 17    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
320  7352100000000000  stx.b dst r2 src r5 off 16    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
321  73120f0000000000  stx.b dst r2 src r1 off 15    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
322  0500470000000000  jmp ja 71 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
323  5603050008000000  jmp32 jne r3, 8, 5 -> slot 329    C++ decode ACCEPT; Rocq Pjmpcmp
324  7342130000000000  stx.b dst r2 src r4 off 19    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
325  7302120000000000  stx.b dst r2 src r0 off 18    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
326  7352110000000000  stx.b dst r2 src r5 off 17    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
327  7312100000000000  stx.b dst r2 src r1 off 16    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
328  0500410000000000  jmp ja 65 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
329  5603050009000000  jmp32 jne r3, 9, 5 -> slot 335    C++ decode ACCEPT; Rocq Pjmpcmp
330  7342140000000000  stx.b dst r2 src r4 off 20    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
331  7302130000000000  stx.b dst r2 src r0 off 19    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
332  7352120000000000  stx.b dst r2 src r5 off 18    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
333  7312110000000000  stx.b dst r2 src r1 off 17    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
334  05003b0000000000  jmp ja 59 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
335  560305000a000000  jmp32 jne r3, 10, 5 -> slot 341    C++ decode ACCEPT; Rocq Pjmpcmp
336  7342150000000000  stx.b dst r2 src r4 off 21    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
337  7302140000000000  stx.b dst r2 src r0 off 20    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
338  7352130000000000  stx.b dst r2 src r5 off 19    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
339  7312120000000000  stx.b dst r2 src r1 off 18    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
340  0500350000000000  jmp ja 53 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
341  560305000b000000  jmp32 jne r3, 11, 5 -> slot 347    C++ decode ACCEPT; Rocq Pjmpcmp
342  7342160000000000  stx.b dst r2 src r4 off 22    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
343  7302150000000000  stx.b dst r2 src r0 off 21    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
344  7352140000000000  stx.b dst r2 src r5 off 20    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
345  7312130000000000  stx.b dst r2 src r1 off 19    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
346  05002f0000000000  jmp ja 47 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
347  560305000c000000  jmp32 jne r3, 12, 5 -> slot 353    C++ decode ACCEPT; Rocq Pjmpcmp
348  7342170000000000  stx.b dst r2 src r4 off 23    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
349  7302160000000000  stx.b dst r2 src r0 off 22    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
350  7352150000000000  stx.b dst r2 src r5 off 21    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
351  7312140000000000  stx.b dst r2 src r1 off 20    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
352  0500290000000000  jmp ja 41 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
353  560305000d000000  jmp32 jne r3, 13, 5 -> slot 359    C++ decode ACCEPT; Rocq Pjmpcmp
354  7342180000000000  stx.b dst r2 src r4 off 24    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
355  7302170000000000  stx.b dst r2 src r0 off 23    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
356  7352160000000000  stx.b dst r2 src r5 off 22    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
357  7312150000000000  stx.b dst r2 src r1 off 21    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
358  0500230000000000  jmp ja 35 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
359  560305000e000000  jmp32 jne r3, 14, 5 -> slot 365    C++ decode ACCEPT; Rocq Pjmpcmp
360  7342190000000000  stx.b dst r2 src r4 off 25    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
361  7302180000000000  stx.b dst r2 src r0 off 24    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
362  7352170000000000  stx.b dst r2 src r5 off 23    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
363  7312160000000000  stx.b dst r2 src r1 off 22    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
364  05001d0000000000  jmp ja 29 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
365  560305000f000000  jmp32 jne r3, 15, 5 -> slot 371    C++ decode ACCEPT; Rocq Pjmpcmp
366  73421a0000000000  stx.b dst r2 src r4 off 26    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
367  7302190000000000  stx.b dst r2 src r0 off 25    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
368  7352180000000000  stx.b dst r2 src r5 off 24    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
369  7312170000000000  stx.b dst r2 src r1 off 23    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
370  0500170000000000  jmp ja 23 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
371  5603050010000000  jmp32 jne r3, 16, 5 -> slot 377    C++ decode ACCEPT; Rocq Pjmpcmp
372  73421b0000000000  stx.b dst r2 src r4 off 27    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
373  73021a0000000000  stx.b dst r2 src r0 off 26    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
374  7352190000000000  stx.b dst r2 src r5 off 25    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
375  7312180000000000  stx.b dst r2 src r1 off 24    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
376  0500110000000000  jmp ja 17 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
377  5603050011000000  jmp32 jne r3, 17, 5 -> slot 383    C++ decode ACCEPT; Rocq Pjmpcmp
378  73421c0000000000  stx.b dst r2 src r4 off 28    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
379  73021b0000000000  stx.b dst r2 src r0 off 27    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
380  73521a0000000000  stx.b dst r2 src r5 off 26    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
381  7312190000000000  stx.b dst r2 src r1 off 25    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
382  05000b0000000000  jmp ja 11 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
383  5603050012000000  jmp32 jne r3, 18, 5 -> slot 389    C++ decode ACCEPT; Rocq Pjmpcmp
384  73421d0000000000  stx.b dst r2 src r4 off 29    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
385  73021c0000000000  stx.b dst r2 src r0 off 28    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
386  73521b0000000000  stx.b dst r2 src r5 off 27    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
387  73121a0000000000  stx.b dst r2 src r1 off 26    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
388  0500050000000000  jmp ja 5 -> slot 394    C++ decode ACCEPT (JA); Rocq Pjmp64
389  5603060013000000  jmp32 jne r3, 19, 6 -> slot 396    C++ decode ACCEPT; Rocq Pjmpcmp
390  73421e0000000000  stx.b dst r2 src r4 off 30    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
391  73021d0000000000  stx.b dst r2 src r0 off 29    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
392  73521c0000000000  stx.b dst r2 src r5 off 28    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
393  73121b0000000000  stx.b dst r2 src r1 off 27    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
394  b400000002000000  alu32 mov r0, 2    C++ decode ACCEPT (alu32 mov); Rocq Palu
395  9500000000000000  jmp exit    C++ decode ACCEPT (EXIT); Rocq Pret
396  73421f0000000000  stx.b dst r2 src r4 off 31    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
397  73021e0000000000  stx.b dst r2 src r0 off 30    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
398  73521d0000000000  stx.b dst r2 src r5 off 29    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
399  73121c0000000000  stx.b dst r2 src r1 off 28    C++ decode REJECT (class not ALU/JMP, ebpf_decode.cpp:164); Rocq Pstore Byte
400  b400000002000000  alu32 mov r0, 2    C++ decode ACCEPT (alu32 mov); Rocq Palu
401  0500f9ff00000000  jmp ja -7 -> slot 395    C++ decode ACCEPT (JA); Rocq Pjmp64

## Real disassembly

Command: `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r --section=xdp /Volumes/SSD/bs/build/fletcher32/bpf.o` (LLVM 23.1.1). Raw 8 bytes precede each mnemonic. The three `CO-RE <byte_off>` lines are objdump's reading of `.BTF.ext`, not an ELF relocation section.

```

/Volumes/SSD/bs/build/fletcher32/bpf.o:	file format elf64-bpf

Disassembly of section xdp:

0000000000000000 <fletcher32>:
       0:	b4 00 00 00 00 00 00 00	w0 = 0x0
       1:	61 18 04 00 00 00 00 00	w8 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)
       2:	61 12 00 00 00 00 00 00	w2 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [17] struct xdp_md::data (0:0)
       3:	bf 25 00 00 00 00 00 00	r5 = r2
       4:	07 05 00 00 08 00 00 00	r5 += 0x8
       5:	2d 85 85 01 00 00 00 00	if r5 > r8 goto +0x185 <L32>
       6:	71 27 06 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x6)
       7:	71 23 05 00 00 00 00 00	w3 = *(u8 *)(r2 + 0x5)
       8:	71 24 07 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x7)
       9:	1c 58 00 00 00 00 00 00	w8 -= w5
      10:	71 26 04 00 00 00 00 00	w6 = *(u8 *)(r2 + 0x4)
      11:	61 11 04 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x4)
		0000000000000058:  CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)
      12:	a6 08 7e 01 18 00 00 00	if w8 < 0x18 goto +0x17e <L32>
      13:	bf 28 00 00 00 00 00 00	r8 = r2
      14:	07 08 00 00 20 00 00 00	r8 += 0x20
      15:	2d 18 7b 01 00 00 00 00	if r8 > r1 goto +0x17b <L32>
      16:	64 07 00 00 10 00 00 00	w7 <<= 0x10
      17:	64 03 00 00 08 00 00 00	w3 <<= 0x8
      18:	4c 73 00 00 00 00 00 00	w3 |= w7
      19:	64 04 00 00 18 00 00 00	w4 <<= 0x18
      20:	4c 43 00 00 00 00 00 00	w3 |= w4
      21:	4c 63 00 00 00 00 00 00	w3 |= w6
      22:	bc 31 00 00 00 00 00 00	w1 = w3
      23:	04 01 00 00 eb ff ff ff	w1 += -0x15
      24:	a6 01 72 01 ec ff ff ff	if w1 < -0x14 goto +0x172 <L32>
      25:	b4 04 00 00 ff ff 00 00	w4 = 0xffff
      26:	b4 01 00 00 ff ff 00 00	w1 = 0xffff
      27:	a6 03 59 00 02 00 00 00	if w3 < 0x2 goto +0x59 <L0>
      28:	71 24 08 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x8)
      29:	71 21 09 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x9)
      30:	64 01 00 00 08 00 00 00	w1 <<= 0x8
      31:	4c 41 00 00 00 00 00 00	w1 |= w4
      32:	bc 14 00 00 00 00 00 00	w4 = w1
      33:	04 04 00 00 fe ff 01 00	w4 += 0x1fffe
      34:	04 01 00 00 ff ff 00 00	w1 += 0xffff
      35:	a6 03 51 00 04 00 00 00	if w3 < 0x4 goto +0x51 <L0>
      36:	71 27 0a 00 00 00 00 00	w7 = *(u8 *)(r2 + 0xa)
      37:	71 20 0b 00 00 00 00 00	w0 = *(u8 *)(r2 + 0xb)
      38:	64 00 00 00 08 00 00 00	w0 <<= 0x8
      39:	4c 70 00 00 00 00 00 00	w0 |= w7
      40:	0c 10 00 00 00 00 00 00	w0 += w1
      41:	bc 07 00 00 00 00 00 00	w7 = w0
      42:	0c 47 00 00 00 00 00 00	w7 += w4
      43:	bc 74 00 00 00 00 00 00	w4 = w7
      44:	bc 01 00 00 00 00 00 00	w1 = w0
      45:	a6 03 47 00 06 00 00 00	if w3 < 0x6 goto +0x47 <L0>
      46:	71 24 0c 00 00 00 00 00	w4 = *(u8 *)(r2 + 0xc)
      47:	71 21 0d 00 00 00 00 00	w1 = *(u8 *)(r2 + 0xd)
      48:	64 01 00 00 08 00 00 00	w1 <<= 0x8
      49:	4c 41 00 00 00 00 00 00	w1 |= w4
      50:	0c 01 00 00 00 00 00 00	w1 += w0
      51:	bc 14 00 00 00 00 00 00	w4 = w1
      52:	0c 74 00 00 00 00 00 00	w4 += w7
      53:	a6 03 3f 00 08 00 00 00	if w3 < 0x8 goto +0x3f <L0>
      54:	71 27 0e 00 00 00 00 00	w7 = *(u8 *)(r2 + 0xe)
      55:	71 20 0f 00 00 00 00 00	w0 = *(u8 *)(r2 + 0xf)
      56:	64 00 00 00 08 00 00 00	w0 <<= 0x8
      57:	4c 70 00 00 00 00 00 00	w0 |= w7
      58:	0c 10 00 00 00 00 00 00	w0 += w1
      59:	bc 07 00 00 00 00 00 00	w7 = w0
      60:	0c 47 00 00 00 00 00 00	w7 += w4
      61:	bc 74 00 00 00 00 00 00	w4 = w7
      62:	bc 01 00 00 00 00 00 00	w1 = w0
      63:	a6 03 35 00 0a 00 00 00	if w3 < 0xa goto +0x35 <L0>
      64:	71 24 10 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x10)
      65:	71 21 11 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x11)
      66:	64 01 00 00 08 00 00 00	w1 <<= 0x8
      67:	4c 41 00 00 00 00 00 00	w1 |= w4
      68:	0c 01 00 00 00 00 00 00	w1 += w0
      69:	bc 14 00 00 00 00 00 00	w4 = w1
      70:	0c 74 00 00 00 00 00 00	w4 += w7
      71:	a6 03 2d 00 0c 00 00 00	if w3 < 0xc goto +0x2d <L0>
      72:	71 27 12 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x12)
      73:	71 20 13 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x13)
      74:	64 00 00 00 08 00 00 00	w0 <<= 0x8
      75:	4c 70 00 00 00 00 00 00	w0 |= w7
      76:	0c 10 00 00 00 00 00 00	w0 += w1
      77:	bc 07 00 00 00 00 00 00	w7 = w0
      78:	0c 47 00 00 00 00 00 00	w7 += w4
      79:	bc 74 00 00 00 00 00 00	w4 = w7
      80:	bc 01 00 00 00 00 00 00	w1 = w0
      81:	a6 03 23 00 0e 00 00 00	if w3 < 0xe goto +0x23 <L0>
      82:	71 24 14 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x14)
      83:	71 21 15 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x15)
      84:	64 01 00 00 08 00 00 00	w1 <<= 0x8
      85:	4c 41 00 00 00 00 00 00	w1 |= w4
      86:	0c 01 00 00 00 00 00 00	w1 += w0
      87:	bc 14 00 00 00 00 00 00	w4 = w1
      88:	0c 74 00 00 00 00 00 00	w4 += w7
      89:	a6 03 1b 00 10 00 00 00	if w3 < 0x10 goto +0x1b <L0>
      90:	71 27 16 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x16)
      91:	71 20 17 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x17)
      92:	64 00 00 00 08 00 00 00	w0 <<= 0x8
      93:	4c 70 00 00 00 00 00 00	w0 |= w7
      94:	0c 10 00 00 00 00 00 00	w0 += w1
      95:	bc 07 00 00 00 00 00 00	w7 = w0
      96:	0c 47 00 00 00 00 00 00	w7 += w4
      97:	bc 74 00 00 00 00 00 00	w4 = w7
      98:	bc 01 00 00 00 00 00 00	w1 = w0
      99:	a6 03 11 00 12 00 00 00	if w3 < 0x12 goto +0x11 <L0>
     100:	71 24 18 00 00 00 00 00	w4 = *(u8 *)(r2 + 0x18)
     101:	71 21 19 00 00 00 00 00	w1 = *(u8 *)(r2 + 0x19)
     102:	64 01 00 00 08 00 00 00	w1 <<= 0x8
     103:	4c 41 00 00 00 00 00 00	w1 |= w4
     104:	0c 01 00 00 00 00 00 00	w1 += w0
     105:	bc 14 00 00 00 00 00 00	w4 = w1
     106:	0c 74 00 00 00 00 00 00	w4 += w7
     107:	a6 03 09 00 14 00 00 00	if w3 < 0x14 goto +0x9 <L0>
     108:	71 20 1a 00 00 00 00 00	w0 = *(u8 *)(r2 + 0x1a)
     109:	71 27 1b 00 00 00 00 00	w7 = *(u8 *)(r2 + 0x1b)
     110:	64 07 00 00 08 00 00 00	w7 <<= 0x8
     111:	4c 07 00 00 00 00 00 00	w7 |= w0
     112:	0c 17 00 00 00 00 00 00	w7 += w1
     113:	bc 71 00 00 00 00 00 00	w1 = w7
     114:	0c 41 00 00 00 00 00 00	w1 += w4
     115:	bc 14 00 00 00 00 00 00	w4 = w1
     116:	bc 71 00 00 00 00 00 00	w1 = w7
<L0>:
     117:	bc 10 00 00 00 00 00 00	w0 = w1
     118:	74 00 00 00 10 00 00 00	w0 >>= 0x10
     119:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     120:	0c 01 00 00 00 00 00 00	w1 += w0
     121:	bc 40 00 00 00 00 00 00	w0 = w4
     122:	74 00 00 00 10 00 00 00	w0 >>= 0x10
     123:	54 04 00 00 ff ff 00 00	w4 &= 0xffff
     124:	0c 04 00 00 00 00 00 00	w4 += w0
     125:	54 06 00 00 01 00 00 00	w6 &= 0x1
     126:	16 06 8f 00 00 00 00 00	if w6 == 0x0 goto +0x8f <L12>
     127:	56 03 0d 00 01 00 00 00	if w3 != 0x1 goto +0xd <L1>
     128:	71 55 00 00 00 00 00 00	w5 = *(u8 *)(r5 + 0x0)
     129:	0c 51 00 00 00 00 00 00	w1 += w5
     130:	bc 10 00 00 00 00 00 00	w0 = w1
     131:	74 00 00 00 10 00 00 00	w0 >>= 0x10
     132:	bc 15 00 00 00 00 00 00	w5 = w1
     133:	54 05 00 00 ff ff 00 00	w5 &= 0xffff
     134:	0c 05 00 00 00 00 00 00	w5 += w0
     135:	0c 41 00 00 00 00 00 00	w1 += w4
     136:	bc 14 00 00 00 00 00 00	w4 = w1
     137:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     138:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     139:	0c 41 00 00 00 00 00 00	w1 += w4
     140:	05 00 0d 00 00 00 00 00	goto +0xd <L2>
<L1>:
     141:	56 03 0f 00 03 00 00 00	if w3 != 0x3 goto +0xf <L3>
     142:	71 25 0a 00 00 00 00 00	w5 = *(u8 *)(r2 + 0xa)
     143:	0c 51 00 00 00 00 00 00	w1 += w5
     144:	bc 10 00 00 00 00 00 00	w0 = w1
     145:	74 00 00 00 10 00 00 00	w0 >>= 0x10
     146:	bc 15 00 00 00 00 00 00	w5 = w1
     147:	54 05 00 00 ff ff 00 00	w5 &= 0xffff
     148:	0c 05 00 00 00 00 00 00	w5 += w0
     149:	0c 41 00 00 00 00 00 00	w1 += w4
     150:	bc 14 00 00 00 00 00 00	w4 = w1
     151:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     152:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     153:	0c 41 00 00 00 00 00 00	w1 += w4
<L2>:
     154:	bc 14 00 00 00 00 00 00	w4 = w1
     155:	bc 51 00 00 00 00 00 00	w1 = w5
     156:	05 00 71 00 00 00 00 00	goto +0x71 <L12>
<L3>:
     157:	56 03 0d 00 05 00 00 00	if w3 != 0x5 goto +0xd <L4>
     158:	71 25 0c 00 00 00 00 00	w5 = *(u8 *)(r2 + 0xc)
     159:	0c 51 00 00 00 00 00 00	w1 += w5
     160:	bc 15 00 00 00 00 00 00	w5 = w1
     161:	74 05 00 00 10 00 00 00	w5 >>= 0x10
     162:	bc 10 00 00 00 00 00 00	w0 = w1
     163:	54 00 00 00 ff ff 00 00	w0 &= 0xffff
     164:	0c 50 00 00 00 00 00 00	w0 += w5
     165:	0c 41 00 00 00 00 00 00	w1 += w4
     166:	bc 14 00 00 00 00 00 00	w4 = w1
     167:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     168:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     169:	0c 41 00 00 00 00 00 00	w1 += w4
     170:	05 00 61 00 00 00 00 00	goto +0x61 <L11>
<L4>:
     171:	56 03 0d 00 07 00 00 00	if w3 != 0x7 goto +0xd <L5>
     172:	71 25 0e 00 00 00 00 00	w5 = *(u8 *)(r2 + 0xe)
     173:	0c 51 00 00 00 00 00 00	w1 += w5
     174:	bc 15 00 00 00 00 00 00	w5 = w1
     175:	74 05 00 00 10 00 00 00	w5 >>= 0x10
     176:	bc 10 00 00 00 00 00 00	w0 = w1
     177:	54 00 00 00 ff ff 00 00	w0 &= 0xffff
     178:	0c 50 00 00 00 00 00 00	w0 += w5
     179:	0c 41 00 00 00 00 00 00	w1 += w4
     180:	bc 14 00 00 00 00 00 00	w4 = w1
     181:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     182:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     183:	0c 41 00 00 00 00 00 00	w1 += w4
     184:	05 00 53 00 00 00 00 00	goto +0x53 <L11>
<L5>:
     185:	56 03 0d 00 09 00 00 00	if w3 != 0x9 goto +0xd <L6>
     186:	71 25 10 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x10)
     187:	0c 51 00 00 00 00 00 00	w1 += w5
     188:	bc 15 00 00 00 00 00 00	w5 = w1
     189:	74 05 00 00 10 00 00 00	w5 >>= 0x10
     190:	bc 10 00 00 00 00 00 00	w0 = w1
     191:	54 00 00 00 ff ff 00 00	w0 &= 0xffff
     192:	0c 50 00 00 00 00 00 00	w0 += w5
     193:	0c 41 00 00 00 00 00 00	w1 += w4
     194:	bc 14 00 00 00 00 00 00	w4 = w1
     195:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     196:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     197:	0c 41 00 00 00 00 00 00	w1 += w4
     198:	05 00 45 00 00 00 00 00	goto +0x45 <L11>
<L6>:
     199:	56 03 0d 00 0b 00 00 00	if w3 != 0xb goto +0xd <L7>
     200:	71 25 12 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x12)
     201:	0c 51 00 00 00 00 00 00	w1 += w5
     202:	bc 15 00 00 00 00 00 00	w5 = w1
     203:	74 05 00 00 10 00 00 00	w5 >>= 0x10
     204:	bc 10 00 00 00 00 00 00	w0 = w1
     205:	54 00 00 00 ff ff 00 00	w0 &= 0xffff
     206:	0c 50 00 00 00 00 00 00	w0 += w5
     207:	0c 41 00 00 00 00 00 00	w1 += w4
     208:	bc 14 00 00 00 00 00 00	w4 = w1
     209:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     210:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     211:	0c 41 00 00 00 00 00 00	w1 += w4
     212:	05 00 37 00 00 00 00 00	goto +0x37 <L11>
<L7>:
     213:	56 03 0d 00 0d 00 00 00	if w3 != 0xd goto +0xd <L8>
     214:	71 25 14 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x14)
     215:	0c 51 00 00 00 00 00 00	w1 += w5
     216:	bc 15 00 00 00 00 00 00	w5 = w1
     217:	74 05 00 00 10 00 00 00	w5 >>= 0x10
     218:	bc 10 00 00 00 00 00 00	w0 = w1
     219:	54 00 00 00 ff ff 00 00	w0 &= 0xffff
     220:	0c 50 00 00 00 00 00 00	w0 += w5
     221:	0c 41 00 00 00 00 00 00	w1 += w4
     222:	bc 14 00 00 00 00 00 00	w4 = w1
     223:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     224:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     225:	0c 41 00 00 00 00 00 00	w1 += w4
     226:	05 00 29 00 00 00 00 00	goto +0x29 <L11>
<L8>:
     227:	56 03 0d 00 0f 00 00 00	if w3 != 0xf goto +0xd <L9>
     228:	71 25 16 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x16)
     229:	0c 51 00 00 00 00 00 00	w1 += w5
     230:	bc 15 00 00 00 00 00 00	w5 = w1
     231:	74 05 00 00 10 00 00 00	w5 >>= 0x10
     232:	bc 10 00 00 00 00 00 00	w0 = w1
     233:	54 00 00 00 ff ff 00 00	w0 &= 0xffff
     234:	0c 50 00 00 00 00 00 00	w0 += w5
     235:	0c 41 00 00 00 00 00 00	w1 += w4
     236:	bc 14 00 00 00 00 00 00	w4 = w1
     237:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     238:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     239:	0c 41 00 00 00 00 00 00	w1 += w4
     240:	05 00 1b 00 00 00 00 00	goto +0x1b <L11>
<L9>:
     241:	56 03 0d 00 11 00 00 00	if w3 != 0x11 goto +0xd <L10>
     242:	71 25 18 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x18)
     243:	0c 51 00 00 00 00 00 00	w1 += w5
     244:	bc 15 00 00 00 00 00 00	w5 = w1
     245:	74 05 00 00 10 00 00 00	w5 >>= 0x10
     246:	bc 10 00 00 00 00 00 00	w0 = w1
     247:	54 00 00 00 ff ff 00 00	w0 &= 0xffff
     248:	0c 50 00 00 00 00 00 00	w0 += w5
     249:	0c 41 00 00 00 00 00 00	w1 += w4
     250:	bc 14 00 00 00 00 00 00	w4 = w1
     251:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     252:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     253:	0c 41 00 00 00 00 00 00	w1 += w4
     254:	05 00 0d 00 00 00 00 00	goto +0xd <L11>
<L10>:
     255:	56 03 0e 00 13 00 00 00	if w3 != 0x13 goto +0xe <L12>
     256:	71 25 1a 00 00 00 00 00	w5 = *(u8 *)(r2 + 0x1a)
     257:	0c 51 00 00 00 00 00 00	w1 += w5
     258:	bc 15 00 00 00 00 00 00	w5 = w1
     259:	74 05 00 00 10 00 00 00	w5 >>= 0x10
     260:	bc 10 00 00 00 00 00 00	w0 = w1
     261:	54 00 00 00 ff ff 00 00	w0 &= 0xffff
     262:	0c 50 00 00 00 00 00 00	w0 += w5
     263:	0c 41 00 00 00 00 00 00	w1 += w4
     264:	bc 14 00 00 00 00 00 00	w4 = w1
     265:	74 04 00 00 10 00 00 00	w4 >>= 0x10
     266:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     267:	0c 41 00 00 00 00 00 00	w1 += w4
<L11>:
     268:	bc 14 00 00 00 00 00 00	w4 = w1
     269:	bc 01 00 00 00 00 00 00	w1 = w0
<L12>:
     270:	bc 15 00 00 00 00 00 00	w5 = w1
     271:	74 05 00 00 10 00 00 00	w5 >>= 0x10
     272:	54 01 00 00 ff ff 00 00	w1 &= 0xffff
     273:	0c 51 00 00 00 00 00 00	w1 += w5
     274:	24 04 00 00 01 00 01 00	w4 *= 0x10001
     275:	bc 10 00 00 00 00 00 00	w0 = w1
     276:	4c 40 00 00 00 00 00 00	w0 |= w4
     277:	74 04 00 00 18 00 00 00	w4 >>= 0x18
     278:	bc 15 00 00 00 00 00 00	w5 = w1
     279:	74 05 00 00 08 00 00 00	w5 >>= 0x8
     280:	74 00 00 00 10 00 00 00	w0 >>= 0x10
     281:	56 03 05 00 01 00 00 00	if w3 != 0x1 goto +0x5 <L13>
     282:	73 42 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w4
     283:	73 02 0b 00 00 00 00 00	*(u8 *)(r2 + 0xb) = w0
     284:	73 52 0a 00 00 00 00 00	*(u8 *)(r2 + 0xa) = w5
     285:	73 12 09 00 00 00 00 00	*(u8 *)(r2 + 0x9) = w1
     286:	05 00 6b 00 00 00 00 00	goto +0x6b <L31>
<L13>:
     287:	56 03 05 00 02 00 00 00	if w3 != 0x2 goto +0x5 <L14>
     288:	73 42 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w4
     289:	73 02 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w0
     290:	73 52 0b 00 00 00 00 00	*(u8 *)(r2 + 0xb) = w5
     291:	73 12 0a 00 00 00 00 00	*(u8 *)(r2 + 0xa) = w1
     292:	05 00 65 00 00 00 00 00	goto +0x65 <L31>
<L14>:
     293:	56 03 05 00 03 00 00 00	if w3 != 0x3 goto +0x5 <L15>
     294:	73 42 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w4
     295:	73 02 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w0
     296:	73 52 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w5
     297:	73 12 0b 00 00 00 00 00	*(u8 *)(r2 + 0xb) = w1
     298:	05 00 5f 00 00 00 00 00	goto +0x5f <L31>
<L15>:
     299:	56 03 05 00 04 00 00 00	if w3 != 0x4 goto +0x5 <L16>
     300:	73 42 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w4
     301:	73 02 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w0
     302:	73 52 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w5
     303:	73 12 0c 00 00 00 00 00	*(u8 *)(r2 + 0xc) = w1
     304:	05 00 59 00 00 00 00 00	goto +0x59 <L31>
<L16>:
     305:	56 03 05 00 05 00 00 00	if w3 != 0x5 goto +0x5 <L17>
     306:	73 42 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w4
     307:	73 02 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w0
     308:	73 52 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w5
     309:	73 12 0d 00 00 00 00 00	*(u8 *)(r2 + 0xd) = w1
     310:	05 00 53 00 00 00 00 00	goto +0x53 <L31>
<L17>:
     311:	56 03 05 00 06 00 00 00	if w3 != 0x6 goto +0x5 <L18>
     312:	73 42 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w4
     313:	73 02 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w0
     314:	73 52 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w5
     315:	73 12 0e 00 00 00 00 00	*(u8 *)(r2 + 0xe) = w1
     316:	05 00 4d 00 00 00 00 00	goto +0x4d <L31>
<L18>:
     317:	56 03 05 00 07 00 00 00	if w3 != 0x7 goto +0x5 <L19>
     318:	73 42 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w4
     319:	73 02 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w0
     320:	73 52 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w5
     321:	73 12 0f 00 00 00 00 00	*(u8 *)(r2 + 0xf) = w1
     322:	05 00 47 00 00 00 00 00	goto +0x47 <L31>
<L19>:
     323:	56 03 05 00 08 00 00 00	if w3 != 0x8 goto +0x5 <L20>
     324:	73 42 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w4
     325:	73 02 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w0
     326:	73 52 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w5
     327:	73 12 10 00 00 00 00 00	*(u8 *)(r2 + 0x10) = w1
     328:	05 00 41 00 00 00 00 00	goto +0x41 <L31>
<L20>:
     329:	56 03 05 00 09 00 00 00	if w3 != 0x9 goto +0x5 <L21>
     330:	73 42 14 00 00 00 00 00	*(u8 *)(r2 + 0x14) = w4
     331:	73 02 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w0
     332:	73 52 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w5
     333:	73 12 11 00 00 00 00 00	*(u8 *)(r2 + 0x11) = w1
     334:	05 00 3b 00 00 00 00 00	goto +0x3b <L31>
<L21>:
     335:	56 03 05 00 0a 00 00 00	if w3 != 0xa goto +0x5 <L22>
     336:	73 42 15 00 00 00 00 00	*(u8 *)(r2 + 0x15) = w4
     337:	73 02 14 00 00 00 00 00	*(u8 *)(r2 + 0x14) = w0
     338:	73 52 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w5
     339:	73 12 12 00 00 00 00 00	*(u8 *)(r2 + 0x12) = w1
     340:	05 00 35 00 00 00 00 00	goto +0x35 <L31>
<L22>:
     341:	56 03 05 00 0b 00 00 00	if w3 != 0xb goto +0x5 <L23>
     342:	73 42 16 00 00 00 00 00	*(u8 *)(r2 + 0x16) = w4
     343:	73 02 15 00 00 00 00 00	*(u8 *)(r2 + 0x15) = w0
     344:	73 52 14 00 00 00 00 00	*(u8 *)(r2 + 0x14) = w5
     345:	73 12 13 00 00 00 00 00	*(u8 *)(r2 + 0x13) = w1
     346:	05 00 2f 00 00 00 00 00	goto +0x2f <L31>
<L23>:
     347:	56 03 05 00 0c 00 00 00	if w3 != 0xc goto +0x5 <L24>
     348:	73 42 17 00 00 00 00 00	*(u8 *)(r2 + 0x17) = w4
     349:	73 02 16 00 00 00 00 00	*(u8 *)(r2 + 0x16) = w0
     350:	73 52 15 00 00 00 00 00	*(u8 *)(r2 + 0x15) = w5
     351:	73 12 14 00 00 00 00 00	*(u8 *)(r2 + 0x14) = w1
     352:	05 00 29 00 00 00 00 00	goto +0x29 <L31>
<L24>:
     353:	56 03 05 00 0d 00 00 00	if w3 != 0xd goto +0x5 <L25>
     354:	73 42 18 00 00 00 00 00	*(u8 *)(r2 + 0x18) = w4
     355:	73 02 17 00 00 00 00 00	*(u8 *)(r2 + 0x17) = w0
     356:	73 52 16 00 00 00 00 00	*(u8 *)(r2 + 0x16) = w5
     357:	73 12 15 00 00 00 00 00	*(u8 *)(r2 + 0x15) = w1
     358:	05 00 23 00 00 00 00 00	goto +0x23 <L31>
<L25>:
     359:	56 03 05 00 0e 00 00 00	if w3 != 0xe goto +0x5 <L26>
     360:	73 42 19 00 00 00 00 00	*(u8 *)(r2 + 0x19) = w4
     361:	73 02 18 00 00 00 00 00	*(u8 *)(r2 + 0x18) = w0
     362:	73 52 17 00 00 00 00 00	*(u8 *)(r2 + 0x17) = w5
     363:	73 12 16 00 00 00 00 00	*(u8 *)(r2 + 0x16) = w1
     364:	05 00 1d 00 00 00 00 00	goto +0x1d <L31>
<L26>:
     365:	56 03 05 00 0f 00 00 00	if w3 != 0xf goto +0x5 <L27>
     366:	73 42 1a 00 00 00 00 00	*(u8 *)(r2 + 0x1a) = w4
     367:	73 02 19 00 00 00 00 00	*(u8 *)(r2 + 0x19) = w0
     368:	73 52 18 00 00 00 00 00	*(u8 *)(r2 + 0x18) = w5
     369:	73 12 17 00 00 00 00 00	*(u8 *)(r2 + 0x17) = w1
     370:	05 00 17 00 00 00 00 00	goto +0x17 <L31>
<L27>:
     371:	56 03 05 00 10 00 00 00	if w3 != 0x10 goto +0x5 <L28>
     372:	73 42 1b 00 00 00 00 00	*(u8 *)(r2 + 0x1b) = w4
     373:	73 02 1a 00 00 00 00 00	*(u8 *)(r2 + 0x1a) = w0
     374:	73 52 19 00 00 00 00 00	*(u8 *)(r2 + 0x19) = w5
     375:	73 12 18 00 00 00 00 00	*(u8 *)(r2 + 0x18) = w1
     376:	05 00 11 00 00 00 00 00	goto +0x11 <L31>
<L28>:
     377:	56 03 05 00 11 00 00 00	if w3 != 0x11 goto +0x5 <L29>
     378:	73 42 1c 00 00 00 00 00	*(u8 *)(r2 + 0x1c) = w4
     379:	73 02 1b 00 00 00 00 00	*(u8 *)(r2 + 0x1b) = w0
     380:	73 52 1a 00 00 00 00 00	*(u8 *)(r2 + 0x1a) = w5
     381:	73 12 19 00 00 00 00 00	*(u8 *)(r2 + 0x19) = w1
     382:	05 00 0b 00 00 00 00 00	goto +0xb <L31>
<L29>:
     383:	56 03 05 00 12 00 00 00	if w3 != 0x12 goto +0x5 <L30>
     384:	73 42 1d 00 00 00 00 00	*(u8 *)(r2 + 0x1d) = w4
     385:	73 02 1c 00 00 00 00 00	*(u8 *)(r2 + 0x1c) = w0
     386:	73 52 1b 00 00 00 00 00	*(u8 *)(r2 + 0x1b) = w5
     387:	73 12 1a 00 00 00 00 00	*(u8 *)(r2 + 0x1a) = w1
     388:	05 00 05 00 00 00 00 00	goto +0x5 <L31>
<L30>:
     389:	56 03 06 00 13 00 00 00	if w3 != 0x13 goto +0x6 <L33>
     390:	73 42 1e 00 00 00 00 00	*(u8 *)(r2 + 0x1e) = w4
     391:	73 02 1d 00 00 00 00 00	*(u8 *)(r2 + 0x1d) = w0
     392:	73 52 1c 00 00 00 00 00	*(u8 *)(r2 + 0x1c) = w5
     393:	73 12 1b 00 00 00 00 00	*(u8 *)(r2 + 0x1b) = w1
<L31>:
     394:	b4 00 00 00 02 00 00 00	w0 = 0x2
<L32>:
     395:	95 00 00 00 00 00 00 00	exit
<L33>:
     396:	73 42 1f 00 00 00 00 00	*(u8 *)(r2 + 0x1f) = w4
     397:	73 02 1e 00 00 00 00 00	*(u8 *)(r2 + 0x1e) = w0
     398:	73 52 1d 00 00 00 00 00	*(u8 *)(r2 + 0x1d) = w5
     399:	73 12 1c 00 00 00 00 00	*(u8 *)(r2 + 0x1c) = w1
     400:	b4 00 00 00 02 00 00 00	w0 = 0x2
     401:	05 00 f9 ff 00 00 00 00	goto -0x7 <L32>
```

## Status

ISSUES
