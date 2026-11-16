Observation report for div2: classify this BPF object against the decoder and lifter that already exist, so a later implementer can compile it, without inventing a shared ISA or emitting a converted program.

## Evidence

Commands actually run:

- `shasum -a 256 /Volumes/SSD/bs/build/div2/bpf.o` → `1d590716c4a7f4e3c583280c4a985ddfaa193e758e6c7037c2c36a17df2395a4` (matches the requested hash)
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -a /Volumes/SSD/bs/build/div2/bpf.o`
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r -s --section-headers --syms --full-contents /Volumes/SSD/bs/build/div2/bpf.o`
- A local ELF64 parse of the same file (section flags, 29 instruction slots, `.BTF` strings, `.BTF.ext` func/line/core records). File size 5784, matching `bpf.toml` `size`.

`decode_ebpf` / `lift_ebpf` were not executed. Classification below is the bytes compared with the sources that were read. Notes file: `/Volumes/SSD/bs/build/div2/bpf.toml`. C source cited by BTF, read only as the origin of the line strings: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/div2.c`.

## Entries and executable sections

ELF64, `EM_BPF`, relocatable, `EI_DATA = 1` (little endian). `e_entry = 0`. No program headers. Section header count 25.

Executable sections (`SHF_ALLOC|SHF_EXECINSTR`, flags `0x6`):

| section | file off | size | role |
|---|---|---|---|
| `.text` | `0x40` | 0 | empty. Same file offset as `xdp` only because its size is 0. Not the program. |
| `xdp` | `0x40` | `0xe8` (232) | the program |

One entry. Symbol `div2`, `FUNC`, `GLOBAL`, section `xdp`, value 0, size 232. `.BTF.ext` func_info: section `xdp`, `insn_off = 0`, `type_id = 7` (BTF name `div2`). License section `license` is `SHF_WRITE|SHF_ALLOC`, bytes `47 50 4c 00` (`GPL`), symbol `LICENSE`. Not code.

29 instruction slots. No `LDDW` (`opcode 0x18`), so no second slot is consumed. Slot index equals instruction index. Jump displacement is in slots, from the next slot: target = index + 1 + off (`jump_target` in `alive2/src/ebpf_decode.cpp`, and `exec_jmpcmp` which applies `off` then `nextinstr`).

## Instruction list

Raw little-endian slots from section `xdp`. `off` is the signed 16-bit field. Register nibbles are `src:dst` in the second byte.

| slot | bytes | op | fields | class |
|---|---|---|---|---|
| 0 | `b4 00 00 00 00 00 00 00` | ALU MOV K | `w0 = 0` | scalar |
| 1 | `61 12 04 00 00 00 00 00` | LDX W MEM | `w2 = *(u32 *)(r1 + 4)` | memory |
| 2 | `61 11 00 00 00 00 00 00` | LDX W MEM | `w1 = *(u32 *)(r1 + 0)` | memory |
| 3 | `bf 13 00 00 00 00 00 00` | ALU64 MOV X | `r3 = r1` | scalar |
| 4 | `07 03 00 00 08 00 00 00` | ALU64 ADD K | `r3 += 8` | scalar |
| 5 | `2d 23 16 00 00 00 00 00` | JMP JGT X | `if r3 > r2 goto +22` → slot 28 | jump |
| 6 | `71 13 05 00 00 00 00 00` | LDX B MEM | `w3 = *(u8 *)(r1 + 5)` | memory |
| 7 | `64 03 00 00 08 00 00 00` | ALU LSH K | `w3 <<= 8` | scalar |
| 8 | `71 12 04 00 00 00 00 00` | LDX B MEM | `w2 = *(u8 *)(r1 + 4)` | memory |
| 9 | `4c 23 00 00 00 00 00 00` | ALU OR X | `w3 \|= w2` | scalar |
| 10 | `71 14 06 00 00 00 00 00` | LDX B MEM | `w4 = *(u8 *)(r1 + 6)` | memory |
| 11 | `64 04 00 00 10 00 00 00` | ALU LSH K | `w4 <<= 16` | scalar |
| 12 | `71 12 07 00 00 00 00 00` | LDX B MEM | `w2 = *(u8 *)(r1 + 7)` | memory |
| 13 | `64 02 00 00 18 00 00 00` | ALU LSH K | `w2 <<= 24` | scalar |
| 14 | `4c 42 00 00 00 00 00 00` | ALU OR X | `w2 \|= w4` | scalar |
| 15 | `4c 32 00 00 00 00 00 00` | ALU OR X | `w2 \|= w3` | scalar |
| 16 | `16 02 0b 00 00 00 00 00` | JMP32 JEQ K | `if w2 == 0 goto +11` → slot 28 | jump |
| 17 | `71 13 01 00 00 00 00 00` | LDX B MEM | `w3 = *(u8 *)(r1 + 1)` | memory |
| 18 | `64 03 00 00 08 00 00 00` | ALU LSH K | `w3 <<= 8` | scalar |
| 19 | `71 14 00 00 00 00 00 00` | LDX B MEM | `w4 = *(u8 *)(r1 + 0)` | memory |
| 20 | `4c 43 00 00 00 00 00 00` | ALU OR X | `w3 \|= w4` | scalar |
| 21 | `71 14 02 00 00 00 00 00` | LDX B MEM | `w4 = *(u8 *)(r1 + 2)` | memory |
| 22 | `64 04 00 00 10 00 00 00` | ALU LSH K | `w4 <<= 16` | scalar |
| 23 | `71 10 03 00 00 00 00 00` | LDX B MEM | `w0 = *(u8 *)(r1 + 3)` | memory |
| 24 | `64 00 00 00 18 00 00 00` | ALU LSH K | `w0 <<= 24` | scalar |
| 25 | `4c 40 00 00 00 00 00 00` | ALU OR X | `w0 \|= w4` | scalar |
| 26 | `4c 30 00 00 00 00 00 00` | ALU OR X | `w0 \|= w3` | scalar |
| 27 | `3c 20 00 00 00 00 00 00` | ALU DIV X | `w0 /= w2`, offset 0 (unsigned) | scalar |
| 28 | `95 00 00 00 00 00 00 00` | JMP EXIT | `exit` | jump |

Jump slots: 5 and 16 only. Both are forward. Both land on slot 28 (`<L0>`). No backward edge, so the lifter's loop test (`tgt <= i` in `build_blocks`) would be false. No JA, no CALL, no tail call.

What the slots do, matching `div2.c`:

- Slot 0 plants the failure return in `r0`.
- Slots 1–2 load `xdp_md.data_end` then `xdp_md.data` as `u32`. Slot 2 overwrites `r1`, so `r1` is no longer the context pointer.
- Slots 3–5 are `data + 8 > end` as a 64-bit unsigned compare. The add is ALU64, so a `u32` near `2^32-8` does not wrap before the compare.
- Slots 6–15 assemble little-endian `b` from bytes `data+4..+7` into `w2`.
- Slot 16 skips the division when that `u32` is 0.
- Slots 17–26 assemble little-endian `a` from bytes `data+0..+3` into `w0`.
- Slot 27 is unsigned 32-bit division. Slot 28 returns `r0`.

## Real disassembly

`llvm-objdump -d` of section `xdp` (`.text` has nothing to disassemble):

```
0000000000000000 <div2>:
       0:	b4 00 00 00 00 00 00 00	w0 = 0x0
       1:	61 12 04 00 00 00 00 00	w2 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [2] struct xdp_md::data_end (0:1)
       2:	61 11 00 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [2] struct xdp_md::data (0:0)
       3:	bf 13 00 00 00 00 00 00	r3 = r1
       4:	07 03 00 00 08 00 00 00	r3 += 0x8
       5:	2d 23 16 00 00 00 00 00	if r3 > r2 goto +0x16 <L0>
       6:	71 13 05 00 00 00 00 00	w3 = *(u8 *)(r1 + 0x5)
       7:	64 03 00 00 08 00 00 00	w3 <<= 0x8
       8:	71 12 04 00 00 00 00 00	w2 = *(u8 *)(r1 + 0x4)
       9:	4c 23 00 00 00 00 00 00	w3 |= w2
      10:	71 14 06 00 00 00 00 00	w4 = *(u8 *)(r1 + 0x6)
      11:	64 04 00 00 10 00 00 00	w4 <<= 0x10
      12:	71 12 07 00 00 00 00 00	w2 = *(u8 *)(r1 + 0x7)
      13:	64 02 00 00 18 00 00 00	w2 <<= 0x18
      14:	4c 42 00 00 00 00 00 00	w2 |= w4
      15:	4c 32 00 00 00 00 00 00	w2 |= w3
      16:	16 02 0b 00 00 00 00 00	if w2 == 0x0 goto +0xb <L0>
      17:	71 13 01 00 00 00 00 00	w3 = *(u8 *)(r1 + 0x1)
      18:	64 03 00 00 08 00 00 00	w3 <<= 0x8
      19:	71 14 00 00 00 00 00 00	w4 = *(u8 *)(r1 + 0x0)
      20:	4c 43 00 00 00 00 00 00	w3 |= w4
      21:	71 14 02 00 00 00 00 00	w4 = *(u8 *)(r1 + 0x2)
      22:	64 04 00 00 10 00 00 00	w4 <<= 0x10
      23:	71 10 03 00 00 00 00 00	w0 = *(u8 *)(r1 + 0x3)
      24:	64 00 00 00 18 00 00 00	w0 <<= 0x18
      25:	4c 40 00 00 00 00 00 00	w0 |= w4
      26:	4c 30 00 00 00 00 00 00	w0 |= w3
      27:	3c 20 00 00 00 00 00 00	w0 /= w2
<L0>:
      28:	95 00 00 00 00 00 00 00	exit
```

`bpf.toml` `[xdp].asm` matches this listing, without the CO-RE annotations.

## Relocations, CO-RE, maps, endianness

There is no `.rel.xdp` and no `.rela.xdp`. Nothing in the relocation tables patches an instruction immediate or a register.

Raw references vs other references:

- Slots 1 and 2 already contain offsets `4` and `0` in the instruction offset field. Those are raw object fields, not a relocation to be applied later.
- `.BTF.ext` core_relo (record size 16, section name `xdp`, count 2) describes the same two instructions. `insn_off` 8 and 16 are byte offsets (slots 1 and 2). `type_id` 2, access strings `0:1` and `0:0`, `kind` 0. `llvm-objdump` prints those as `CO-RE <byte_off>` for `xdp_md::data_end` and `xdp_md::data`. BTF strings at those access offsets are `0:1` and `0:0`. This is a side description. It is not an ELF relocation, not an XPOST record, and not a map index.
- No section type is `SHT_XPOST_META` (`0x80000001`) or `SHT_XPOST_IMAGE` (`0x80000002`) from `tooling/vendor/xpost-elf/src/encode.rs`. This object is not an XPOST image.
- No `LDDW`, so there is no `PSEUDO_MAP_FD` / `PSEUDO_MAP_IDX` / `PSEUDO_MAP_IDX_VALUE` (`ebpfSyntax.v` `pseudo_ptr_ty`, `decode_lddw_insn` in `ebpfDecoder.v`). A map-index reference would be an `LDDW` whose source register is `R5`. None exists.
- `.rel.BTF` has one `R_BPF_64_NODYLD32` against symbol `LICENSE` at BTF offset `0x11c`. That is the license string, not code and not a map fd.
- `.rel.BTF.ext` has thirteen `R_BPF_64_NODYLD32` against section symbol `xdp` (symbol index 2). Those relocate BTF.ext section bases. They are not instruction immediates and not map indexes.
- `.rel.debug_info`, `.rel.debug_str_offsets`, `.rel.debug_addr`, `.rel.debug_frame`, `.rel.debug_line` are DWARF (`R_BPF_64_ABS32` / `R_BPF_64_ABS64`).

Symbols: `div2.c` (`FILE`), section symbols, `div2` (`FUNC`), `LICENSE` (`OBJECT`). No map symbol, no `.maps` section.

Endianness: the container is little endian. Every multi-byte field in the slots is little endian (imm 8 is `08 00 00 00`, jump `+0x16` is `16 00`). There is no `BPF_END` / byteswap opcode (`code 0xd` in `decode_insn`). The packet integers are assembled little endian by the shifts and ORs, not by an endian instruction.

BTF line records (byte `insn_off`) name the source lines already stored in `.BTF`: slot 0 `int div2(struct xdp_md *ctx)`; slot 1 `ctx->data_end`; slot 2 `ctx->data`; slots 3 and 5 `if (data + 8 > end)`; slots 6 and 17 the `p[0]|p[1]<<8|p[2]<<16` gather; slot 16 `if (b == 0)`; slot 27 `return a / b;`; slot 28 `}`.

## Semantic rules actually read

Read and used:

- `alive2/src/ebpf.h`. `EbInsn` is only `EbAlu` or `EbJmp`. No load, store, call, or `LDDW` alternative.
- `alive2/src/ebpf_decode.cpp` (whole file). Class is `opcode & 7`. ALU `0x4` and ALU64 `0x7` decode MOV/ADD/OR/LSH/DIV and the rest of that switch. DIV/MOD with offset 0 is unsigned `Div`/`Mod`; offset 1 is signed. JMP `0x5` / JMP32 `0x6` decode JGT, JEQ, EXIT. Any other class, including LDX `0x1`, hits the final `else` and throws `unsupported class in opcode 0x…`.
- `alive2/src/ebpf_lift.cpp`: `build_blocks`, `jump_target` use, `emit` / `emit_alu` / `emit_wide` / `emit_narrow` / `emit_divmod` / `emit_cmp`, `arith_op`, `shift_op`, `icmp_cond`, `make_alive_trace`, and the concrete evaluator's `MemInstr` stop (`trace.memory = Changed`, then unsupported). `eval_op` treats `UDiv`/`SDiv` by zero as `IrResultKind::Ub`. Default `LiftBug::None` does not take that path.
- `alive2/rocq/upstream/theories/ebpfSyntax.v` (whole file): `Pload`, `Palu`, `Pjmpcmp`, `Pret`, widths, `DIV` vs `SDIV`.
- `alive2/rocq/upstream/theories/ebpfDecoder.v` (whole file): `decode_insn` and `find_instr`. `LDDW` is only opcode `0x18` and consumes the next word. LDX mode `opcode>>5 == 3` with imm 0 is `Pload`. Size bits `0` → `Word`, `2` → `Byte`. ALU code `0x3` with offset 0 is `Palu DIV`. JMP code `0x2` is unsigned `GT`. JMP32 code `0x1` is `EQ`. JMP code `0x9` is `Pret`.
- `alive2/rocq/upstream/theories/ebpfBinSem.v`: `nextinstr`; `eval_div_u32` / `eval_div_u64` (zero divisor → 0, not stuck); `eval_alu32` / `eval_alu64` (`LSH` masked by `eval_shift_mask`, ALU32 results `Val.longofintu`); `exec_alu`; `eval_cmp32` / `eval_cmp64` / `exec_jmpcmp` (static shortcut does not fire for these two jumps); `load` / `load_value_casting` / `exec_load` (`Mint32` / `Mint8unsigned`, `Vint` zero-extended to `Vlong`, `Vlong` base goes through `cast_i2p`, miss is `Stuck`); live `exec_ret` at the empty-stack case (`r0` kept, `PC` set to `Vnullptr`); `exec_instr` dispatch. `Pcall` is not `Stuck` only for `CallInternal`; static/BTF calls fall through to `Stuck`. This program has no call.
- `alive2/rocq/upstream/theories/ebpfState.v` lines 83–92 only: `outcome` and `addr_region` (`base_blk`, `size_blk`, `base_addr`).
- `alive2/rocq/upstream/validator/Validation.v` lines 1–80: `bpf_interpreter` calls `find_instr` then `exec_instr`. No theorem about this program in that range.
- `alive2/third_party/alive2/ir/instr.cpp` lines 213–221: `div_ub` adds `b != 0` as guardable UB. That is the Alive2 rule `emit_divmod` is written to avoid.
- `alive2/src/ebpf_concrete.cpp` lines 781–791: a trace whose memory summary is not `Empty` is a memory divergence. Not a semantics of DIV.

Not read, so not used as rules: `GlobalSem.v`, `CMemoryModel.v`, `Nondeterminism.v`, `SCLanguage.v`, `Extraction.v`, and the rest of `Validation.v` past line 80. A search for `Lemma`/`Theorem` under `alive2/rocq` found only `ireg_eq`, `preg_eq`, and `is_label_correct`, and that last one sits inside a comment in `ebpfBinSem.v`.

Per-opcode rule, every slot:

- ALU32 MOV/LSH/OR/DIV and ALU64 MOV/ADD: C++ `decode_ebpf` accepts them. Rocq `decode_insn` accepts them. ALU32 writes the low 32 bits and zero-extends (`emit_alu`: trunc, operate, `zext64`; Rocq `Val.longofintu`). ALU64 MOV copies the full register (`emit_wide` returns `src`; `eval_alu64 MOV` returns `src`). ALU64 ADD K sign-extends the imm (`imm64(..., sign_imm=true)` unless `ImmNoSignExtend`; Rocq `int64_of_int`). LSH K masks the amount with 31 (`shift` and `eval_shift_mask W32`). Amounts 8, 16, 24 are unchanged by that mask. DIV X with offset 0 is unsigned. Both models define divisor 0 as result 0 (`emit_divmod` branches to the zero constant; `eval_div_u32` returns `Vzero`). Signed overflow does not apply. The C++ bug flag `DivZeroAsUb` would instead emit raw `BinOp::UDiv`, which Alive2 treats as UB. `make_alive_trace` uses that flag only when asked.
- JMP JGT X, width 64: unsigned `ICmp::UGT` on the full registers (`icmp_cond`, `emit_cmp`). Rocq `Pjmpcmp (GT Unsigned) W64` via `Val.cmplu_bool`. Taken target slot 28, not-taken fallthrough slot 6.
- JMP32 JEQ K imm 0: compare the low 32 bits (`trunc32` / `Val.loword`). Rocq `eval_cmp_static` does not fold this case. Taken target slot 28, fallthrough slot 17.
- EXIT: C++ `Return` of `r0`. Rocq `Pret` → `exec_ret`. Empty call stack keeps `r0` and sets `PC` to `Vnullptr`. This program never calls, so the stack is empty.
- Every LDX (`0x61` word, `0x71` byte): Rocq `decode_insn` accepts them as `Pload Word` or `Pload Byte` because mode bits are MEM, imm is 0, and size bits match. `exec_load` zero-extends a `Vint` into the destination. A `Vlong` address is resolved only by `cast_i2p` against `addr_map`; failure is `Stuck`, not zero. C++ `decode_ebpf` rejects the first one, slot 1 opcode `0x61`, class `0x1`, before any later slot is decoded.

## IR mapping against the existing C++ lifter only

The lifter never sees this object. `EbInsn.op` cannot represent a load, and `decode_ebpf` throws on class `0x1`. `make_alive_trace` calls `decode_ebpf` before `Lifter::run`.

If the ten LDX slots were deleted, the remaining slots map as follows. Registers are `i64`. ALU32 inserts `trunc i32`, the operation, then `zext i64`. This is the mapping only; it is not a conversion of div2.

| slots | lifter IR, `LiftBug::None` |
|---|---|
| 0 `w0 = 0` | trunc, the imm `0`, zext. Result `i64 0`. |
| 3 `r3 = r1` | `emit_wide(Mov)` returns the `r1` value. No new opcode. |
| 4 `r3 += 8` | `add i64 r3, 8` (imm sign-extended, still 8). |
| 5 `jgt r3, r2, +22` | `icmp ugt i64`, branch to the exit block or the fallthrough block. |
| 7, 11, 13, 18, 22, 24 shifts | `shl` of the truncated value by `(amount & 31)`, then zext. |
| 9, 14, 15, 20, 25, 26 ors | `or i32`, then zext. |
| 16 `jeq w2, 0, +11` | `icmp eq i32` of the truncated register and `0`, branch. |
| 27 `w0 /= w2` | `emit_divmod` on `i32`: `icmp eq` divisor, 0 → constant 0, else `udiv`, phi, then zext to `i64`. Not a bare `udiv`. |
| 28 `exit` | `ret i64 r0`. |

CFG the block builder would make from these jumps, again only after a successful decode: leaders at 0, 6, 17, 28. Block of slots 0–5 branches to 28 or 6. Block of 6–16 branches to 28 or 17. Block of 17–27 falls into 28. Block 28 returns. Three predecessors at 28, so `r0` is a phi (constant 0 from the two early exits, the quotient from the division). `loop` stays false. `r10` is unused. No stack slot.

Pointer origins in the lifter do not apply to a successful load model here: the lifter has no load instruction to attach them to. `init_regs` would mark an unlisted `r1` as poison with `RegOrigin::Pointer` only under `LiftInit` other than `Zero`. `make_alive_trace` uses `LiftInit::Zero`.

## Memory, helper, map, loop

- Memory: required. Two `u32` loads of the context (`r1+0`, `r1+4`) happen on every path. The eight byte loads are not on every path. They run only after `data+8 <= data_end`. Bytes `data+4..7` run even when `b == 0`. Bytes `data+0..3` run only when `b != 0`. A model that faults on a short packet, or that reads packet bytes before slot 5, is wrong. After slot 2 the base of the byte loads is the zero-extended `u32` from `ctx->data`, not the original context pointer.
- Rocq memory requirement, from `exec_load` and `addr_region`: if that `u32` is a `Vlong`, `cast_i2p` must hit a region whose concrete `[base_addr, base_addr+size_blk)` covers each accessed address. A miss is `Stuck`. The C++ lifter has no such region and its concrete walker marks any `MemInstr` as memory-changed and stops.
- Helper: none. No `CALL` (`0x85`), no `Pcall`, no helper id.
- Map: none. No map section, no map symbol, no `LDDW` map fd or map index.
- Loop: none. Both jumps go to slot 28, which is after the jump. The lifter's `loop` flag would stay false.

## Conversion result

NOT CONVERTED.

No `.alive` file is emitted. The first instruction the C++ decoder cannot classify is slot 1, opcode `0x61`. Slots 2, 6, 8, 10, 12, 17, 19, 21, and 23 fail the same way. The scalar and jump slots are in the decoder, but the program is not converted by skipping the loads. Calling the missing load model "unsupported" is the decoder's own error string; it is not a successful conversion.

## Proof coverage

No proof of this program was found in the Rocq tree that was searched. `Validation.v` (lines 1–80) is an interpreter, not a theorem that `div2` returns `a/b`. `ebpfBinSem.v` defines `eval_div_u32`, `exec_load`, `exec_jmpcmp`, and `exec_ret`, and its only `Lemma` is commented out. `ireg_eq` / `preg_eq` are register decidable equality. Nothing ties the 29 slots to a quotient.

The concrete checker refuses a non-empty memory summary (`ebpf_concrete.cpp` around the memory divergence). That gate does not prove the division. It also cannot run until decode succeeds.

## Counterexample idea

Do not treat divisor 0 as Alive2 UB on this object: slot 16 jumps to the exit, and slot 0 already stored 0. A lifter that used `LiftBug::DivZeroAsUb` or a bare `udiv` (`div_ub` in `alive2/third_party/alive2/ir/instr.cpp`) would be wrong for a program that can reach a zero divisor, but this CFG does not reach slot 27 when `w2` is 0.

Three inputs that separate a wrong lift from the rules above. `data_end = data+8` unless said otherwise. Bytes are at `data`, little endian.

1. Short packet. `data_end = data`, packet bytes irrelevant. Slots 1–2 still read the context `u32`s. Slot 5 jumps to 28. Return 0. No byte load. A model that faults, or that returns a quotient, is wrong.
2. Zero divisor. Bytes `01 00 00 00 00 00 00 00`. `a = 1`, `b = 0`. Slots 6–15 run. Slot 16 jumps. Return 0. Slots 17–27 do not run.
3. Unsigned, not signed, and little endian. Bytes `ff ff ff ff 02 00 00 00`. `a = 0xffffffff`, `b = 2`. Unsigned 32-bit quotient is `0x7fffffff`, zero-extended in `r0`. Signed 32-bit division of the same bits is `0`. A second packet, `04 03 02 01 02 00 00 00`, is `a = 0x01020304`, `b = 2`, quotient `0x00810182`. Gathering those bytes big endian would divide `0x04030201` instead.

Status: ISSUES
