# fib observation

Produce an observation report for fib so a later implementer can compile it, without inventing a shared ISA. This file records the object that was actually decoded. It does not convert the program.

Conversion result: **NOT CONVERTED**. No `.alive` file is emitted.

## Evidence

Commands run on the object, not on a copy:

- `shasum -a 256 /Volumes/SSD/bs/build/fib/bpf.o` → `598dbebb210b224b1c8ef5cdbd4245fd5bebfaafc8ca8e0ab29eb4ef601d825c`. Matches the hash given with the task.
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -h -S -s -r -n -W` and `/opt/homebrew/opt/llvm/bin/llvm-objdump -h`, `-d -r --section=xdp`, `-s -j xdp -j license -j .maps`.
- A local struct parse of the same file for slot fields, executable flags, and the `.BTF.ext` core-relo records. It agrees with readelf/objdump.
- Notes read: `/Volumes/SSD/bs/build/fib/bpf.toml`.
- C source read: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/fib.c` (85 lines). The toml `source` field points at that path.

ELF identity from `llvm-readelf -h`: ELF64, little endian (`EI_DATA` = 1, "2's complement, little endian"), `ET_REL`, `EM_BPF`, `e_entry` = 0, no program headers, 26 section headers. Endianness of the instruction encoding is little endian. There is no `END` / byteswap opcode in `xdp`. Packet endianness is the explicit byte/shift sequence below, not a memory-chunk endian flag. `Archi.big_endian` was not read.

## Executable sections

`SHF_EXECINSTR` (objdump `TEXT`, flags `0x6`) is only:

| section | size | file offset | role |
|---|---:|---:|---|
| `.text` | 0 | `0x40` | empty. Not the program. Same file offset as `xdp` only because the size is 0. |
| `xdp` | 328 (`0x148`) | `0x40` | the program |

No other executable section. 328 bytes / 8 = 41 slots. No slot has opcode `0x18`, so there is no LDDW pair. 41 slots are 41 instructions. Symbol `fib` is `GLOBAL FUNC`, value 0, size 328, section index 3 (`xdp`). One entry: slot 0 of `xdp`. `e_entry` is 0 and is not a second entry.

## Entries and instruction list

Entry `fib` at `xdp+0`. Fail paths leave `r0` as the 0 written at slot 0. The success path overwrites `r0` with 2 at slot 39, then `exit`. `fib.c` names those returns `XDP_ABORTED` and `XDP_PASS`. The macro header was not opened; the immediates in the object are 0 and 2.

`r1` enters as the `xdp_md` pointer and is overwritten at slot 2 by the zero-extended `data` pointer. After that, packet loads and stores use `r1`, not the context pointer. `r7` is `data+8` in 64 bits (ALU64 add). `r8`, `r9`, and `r10` are unused. No stack spill.

Jump slots and targets (`target = index + 1 + int16(off)`; exit has no target). All five conditional targets land on slot boundaries. The only backward edge is slot 29 → 25.

| slot | target | raw off |
|---:|---|---:|
| 5 | 40 (`L3`, `exit`) | +34 |
| 11 | 40 | +28 |
| 18 | 20 (`L0`) | +1 |
| 21 | 30 (`L2`) | +8 |
| 29 | 25 (`L1`) | −5 (`0xfffb`) |
| 40 | exit | 0 |

| slot | bytes (opcode regs off imm) | what |
|---:|---|---|
| 0 | `b4 00 00 00` imm 0 | ALU32 MOV `r0 = 0` |
| 1 | `61 14 04 00` imm 0 | LDXW `r4 = *(u32*)(r1+4)` CO-RE byte_off `data_end` |
| 2 | `61 11 00 00` imm 0 | LDXW `r1 = *(u32*)(r1+0)` CO-RE byte_off `data` |
| 3 | `bf 17 00 00` imm 0 | ALU64 MOV `r7 = r1` |
| 4 | `07 07 00 00` imm 8 | ALU64 ADD `r7 += 8` |
| 5 | `2d 47 22 00` off +34 | JMP64 JGT `if r7 > r4 goto 40` unsigned |
| 6 | `71 13 05 00` | LDXB `r3 = *(u8*)(r1+5)` |
| 7 | `71 16 04 00` | LDXB `r6 = *(u8*)(r1+4)` |
| 8 | `71 15 06 00` | LDXB `r5 = *(u8*)(r1+6)` |
| 9 | `71 12 07 00` | LDXB `r2 = *(u8*)(r1+7)` |
| 10 | `1c 74 00 00` | ALU32 SUB `r4 -= r7` |
| 11 | `a6 04 1c 00` imm 4 | JMP32 JLT `if w4 < 4 goto 40` unsigned |
| 12 | `64 03 00 00` imm 8 | ALU32 LSH `r3 <<= 8` |
| 13 | `4c 63 00 00` | ALU32 OR `r3 \|= r6` |
| 14 | `64 05 00 00` imm 16 | ALU32 LSH `r5 <<= 16` |
| 15 | `64 02 00 00` imm 24 | ALU32 LSH `r2 <<= 24` |
| 16 | `4c 52 00 00` | ALU32 OR `r2 \|= r5` |
| 17 | `4c 32 00 00` | ALU32 OR `r2 \|= r3` |
| 18 | `a6 02 01 00` imm 47 | JMP32 JLT `if w2 < 47 goto 20` unsigned |
| 19 | `b4 02 00 00` imm 47 | ALU32 MOV `r2 = 47` |
| 20 | `bc 23 00 00` | ALU32 MOV `r3 = r2` |
| 21 | `a6 02 08 00` imm 2 | JMP32 JLT `if w2 < 2 goto 30` unsigned |
| 22 | `b4 04 00 00` imm 0 | ALU32 MOV `r4 = 0` |
| 23 | `b4 03 00 00` imm 1 | ALU32 MOV `r3 = 1` |
| 24 | `b4 05 00 00` imm 1 | ALU32 MOV `r5 = 1` |
| 25 | `bc 40 00 00` | ALU32 MOV `r0 = r4` (loop head) |
| 26 | `bc 34 00 00` | ALU32 MOV `r4 = r3` |
| 27 | `0c 03 00 00` | ALU32 ADD `r3 += r0` |
| 28 | `04 05 00 00` imm 1 | ALU32 ADD `r5 += 1` |
| 29 | `ae 25 fb ff` off −5 | JMP32 JLT `if w5 < w2 goto 25` unsigned |
| 30 | `bc 32 00 00` | ALU32 MOV `r2 = r3` |
| 31 | `74 02 00 00` imm 24 | ALU32 RSH `r2 >>= 24` |
| 32 | `73 21 0b 00` | STXB `*(u8*)(r1+11) = r2` |
| 33 | `bc 32 00 00` | ALU32 MOV `r2 = r3` |
| 34 | `74 02 00 00` imm 16 | ALU32 RSH `r2 >>= 16` |
| 35 | `73 21 0a 00` | STXB `*(u8*)(r1+10) = r2` |
| 36 | `73 31 08 00` | STXB `*(u8*)(r1+8) = r3` |
| 37 | `74 03 00 00` imm 8 | ALU32 RSH `r3 >>= 8` |
| 38 | `73 31 09 00` | STXB `*(u8*)(r1+9) = r3` |
| 39 | `b4 00 00 00` imm 2 | ALU32 MOV `r0 = 2` |
| 40 | `95 00 00 00` | JMP EXIT |

Counts: 25 ALU, 10 memory (6 LDX, 4 STX), 6 jumps (5 conditional + exit). Registers written by ALU: `r0`, `r2`, `r3`, `r4`, `r5`, `r7`. Memory also writes `r1`, `r2`, `r3`, `r4`, `r5`, `r6`.

What the bytes compute, checked against `fib.c` (`ctx_view`, `load_u32`, `fib_u32`, `store_u32`):

- Slots 1–5: `data_end` in `r4`, `data` in `r1`, reject unless `data+8 <= data_end` as a 64-bit unsigned compare of the zero-extended addresses.
- Slots 6–17: little-endian `u32` at `data+4`. Low byte is the byte at `+4`, high byte is the byte at `+7`. Not a word load of the packet.
- Slot 10–11: `w4 = (u32)data_end - (u32)(data+8)`; reject if that residual is `< 4`. Together with slot 5 this requires 12 bytes (`data+4..+7` readable, `data+8..+11` writable). On the fall-through of slot 5 the 32-bit subtract does not wrap, because both addresses were zero-extended and `data+8 <= data_end` already held in 64 bits.
- Slots 18–19: unsigned clamp to 47. `fib.c` does `if (param > 47) param = 47`.
- Slots 20–29: `fib_u32`. `n < 2` returns `n` (`F0 = 0`, `F1 = 1`). Otherwise `a = 0`, `b = 1`, `i = 1`, and while `i < n`: `b, a = a+b, b` with `i++`, all ALU32. Back-edge count is `n-1`, at most 46 when `n = 47`. `F47 = 2971215073 = 0xb11924e1`, which fits in `u32`. `F48` does not (low 32 bits would be `0x1e8d0a40`). The clamp is what keeps the add inside 32 bits.
- Slots 30–38: store that `u32` little-endian at `data+8` (four byte stores; low byte at `+8`, high byte at `+11`).
- Slot 39–40: return 2.

## Real disassembly

`llvm-objdump -d -r --section=xdp` (bytes kept). CO-RE notes are objdump’s, printed under slots 1 and 2. There is no relocation record on `xdp` itself; see below.

```
0000000000000000 <fib>:
       0:	b4 00 00 00 00 00 00 00	w0 = 0x0
       1:	61 14 04 00 00 00 00 00	w4 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)
       2:	61 11 00 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [17] struct xdp_md::data (0:0)
       3:	bf 17 00 00 00 00 00 00	r7 = r1
       4:	07 07 00 00 08 00 00 00	r7 += 0x8
       5:	2d 47 22 00 00 00 00 00	if r7 > r4 goto +0x22 <L3>
       6:	71 13 05 00 00 00 00 00	w3 = *(u8 *)(r1 + 0x5)
       7:	71 16 04 00 00 00 00 00	w6 = *(u8 *)(r1 + 0x4)
       8:	71 15 06 00 00 00 00 00	w5 = *(u8 *)(r1 + 0x6)
       9:	71 12 07 00 00 00 00 00	w2 = *(u8 *)(r1 + 0x7)
      10:	1c 74 00 00 00 00 00 00	w4 -= w7
      11:	a6 04 1c 00 04 00 00 00	if w4 < 0x4 goto +0x1c <L3>
      12:	64 03 00 00 08 00 00 00	w3 <<= 0x8
      13:	4c 63 00 00 00 00 00 00	w3 |= w6
      14:	64 05 00 00 10 00 00 00	w5 <<= 0x10
      15:	64 02 00 00 18 00 00 00	w2 <<= 0x18
      16:	4c 52 00 00 00 00 00 00	w2 |= w5
      17:	4c 32 00 00 00 00 00 00	w2 |= w3
      18:	a6 02 01 00 2f 00 00 00	if w2 < 0x2f goto +0x1 <L0>
      19:	b4 02 00 00 2f 00 00 00	w2 = 0x2f
      20:	bc 23 00 00 00 00 00 00	w3 = w2
      21:	a6 02 08 00 02 00 00 00	if w2 < 0x2 goto +0x8 <L2>
      22:	b4 04 00 00 00 00 00 00	w4 = 0x0
      23:	b4 03 00 00 01 00 00 00	w3 = 0x1
      24:	b4 05 00 00 01 00 00 00	w5 = 0x1
      25:	bc 40 00 00 00 00 00 00	w0 = w4
      26:	bc 34 00 00 00 00 00 00	w4 = w3
      27:	0c 03 00 00 00 00 00 00	w3 += w0
      28:	04 05 00 00 01 00 00 00	w5 += 0x1
      29:	ae 25 fb ff 00 00 00 00	if w5 < w2 goto -0x5 <L1>
      30:	bc 32 00 00 00 00 00 00	w2 = w3
      31:	74 02 00 00 18 00 00 00	w2 >>= 0x18
      32:	73 21 0b 00 00 00 00 00	*(u8 *)(r1 + 0xb) = w2
      33:	bc 32 00 00 00 00 00 00	w2 = w3
      34:	74 02 00 00 10 00 00 00	w2 >>= 0x10
      35:	73 21 0a 00 00 00 00 00	*(u8 *)(r1 + 0xa) = w2
      36:	73 31 08 00 00 00 00 00	*(u8 *)(r1 + 0x8) = w3
      37:	74 03 00 00 08 00 00 00	w3 >>= 0x8
      38:	73 31 09 00 00 00 00 00	*(u8 *)(r1 + 0x9) = w3
      39:	b4 00 00 00 02 00 00 00	w0 = 0x2
      40:	95 00 00 00 00 00 00 00	exit
```

`llvm-objdump -s` of `license` is `47 50 4c 00` (`GPL\0`). `.maps` is 32 zero bytes.

## Relocations, CO-RE, maps, endianness

No `.rel.xdp` and no `.rel.text`. `llvm-readelf -r` relocation sections and their targets:

- `.rel.debug_info`, `.rel.debug_str_offsets`, `.rel.debug_addr`, `.rel.debug_frame`, `.rel.debug_line`: `R_BPF_64_ABS32` / `R_BPF_64_ABS64` to debug section symbols, to `xdp`, to `LICENSE`, or to `workload`. Debug only.
- `.rel.BTF`: two `R_BPF_64_NODYLD32`, symbol `workload` at BTF offset `0x250`, symbol `LICENSE` at `0x268`.
- `.rel.BTF.ext`: 24 `R_BPF_64_NODYLD32` to section symbol `xdp`.

Those BTF records are raw object references inside `.BTF` / `.BTF.ext`. They are not instruction immediates. They are not XPOST container relocations: the section list has no `.xpost.meta` and no `.xpost.image`. They are not map-index references. A map-index reference in this tree’s decoder is an LDDW whose source register is `R5` (`PSEUDO_MAP_IDX`) or `R6` (`PSEUDO_MAP_IDX_VALUE`) in `alive2/rocq/upstream/theories/ebpfDecoder.v` (`decode_lddw_insn`) and `ebpfSyntax.v` (`pseudo_ptr_ty`). This object has no LDDW.

CO-RE is separate from ELF relocations. `.BTF.ext` header: magic `0xeb9f`, version 1, `hdr_len` 32, `core_relo_off` 368, `core_relo_len` 44, record size 16. One section, name `xdp`, two records, kind 0. objdump prints kind 0 as `CO-RE <byte_off>`:

| insn byte off | slot | type id | access | kind | encoded `off` | encoded imm |
|---:|---:|---:|---|---:|---:|---:|
| `0x8` | 1 | 17 | `0:1` | 0 | 4 | 0 |
| `0x10` | 2 | 17 | `0:0` | 0 | 0 | 0 |

Objdump names type 17 `struct xdp_md`, access `0:1` as `data_end` and `0:0` as `data`. The 16-bit offset field already holds that local layout (0 and 4). The immediate is 0 and is not a map fd or a map index. A later compiler must treat these as CO-RE byte-offset patches of the two context loads, not as `R_BPF_64_64` and not as XPOST metadata. Ignoring them happens to match this object’s own BTF layout. That is not a license to drop the records, and it is not a license to add the patch on top of the offset that is already there.

Map symbol `workload`: `GLOBAL OBJECT`, section `.maps`, size 32, file bytes all zero. BTF strings name `workload`, `exec_val`, and `w0`..`w7`. The toml says `BPF_MAP_TYPE_HASH`, `max_entries = 2`, `key_size = 1`, `value_size = 32`, `aot_addr = 0x40380290`. That address does not appear in any `xdp` immediate. Immediates in `xdp` are only 0, 1, 2, 4, 8, 16, 24, and 47. `fib.c` declares the map and comments that an app copies it into the context; the compiled body never loads the map and never calls a helper. Do not invent a map lookup from the section’s existence.

`.BTF` is 0x53a bytes, `.BTF.ext` is 0x1bc bytes. Both are present. `llvm-readelf -n` printed no notes.

## Semantic rules actually read

Read and used:

- `alive2/src/ebpf.h`. `EbInsn.op` is only `std::variant<EbAlu, EbJmp>`. There is no memory instruction in the C++ AST.
- `alive2/src/ebpf_decode.cpp`, whole file. Classes decoded: ALU `0x04`, JMP `0x05`, JMP32 `0x06`, ALU64 `0x07`. Anything else, including LD `0x00`, LDX `0x01`, ST `0x02`, STX `0x03`, hits the final `else` and throws `unsupported class` (`ebpf_decode.cpp` lines 164–168). ALU opcodes read: ADD `0x00`, SUB `0x10`, MUL `0x20`, DIV/SDIV `0x30`, OR `0x40`, AND `0x50`, LSH `0x60`, RSH `0x70`, NEG `0x80`, MOD/SMOD `0x90`, XOR `0xa0`, MOV/MOVSX `0xb0`, ARSH `0xc0`. JMP opcodes read: JA `0x00`, JEQ `0x10`, JGT `0x20`, JGE `0x30`, JLT `0xa0`, JLE `0xb0`, JSGT `0x60`, JSGE `0x70`, JSLT `0xc0`, JSLE `0xd0`, JNE `0x50`, EXIT `0x90`. `jump_target` is `index + 1 + off`, or `imm` only when `ja_uses_imm` (JMP32 JA).
- `alive2/src/ebpf_lift.cpp`, whole file, and `ebpf_lift.h`. ALU32 is trunc to i32, operate, zext to i64 (`emit_alu`). ALU64 MOV is the source value; ALU64 ADD is `BinOp::Add` on i64. ALU32 MOV of an immediate zero-extends (`sign_imm` is false for W32). Shifts are `BinOp::Shl` / `LShr` / `AShr` with the amount masked by 31 or 63 unless `LiftBug::ShiftWithoutMask`. Compares: `icmp_cond` maps JGT to `ICmp::UGT` and JLT to `ICmp::ULT` (unsigned). EXIT is `Return(i64, r0)`. A target `<=` the jump index sets `LiftInfo.loop` and does not reject the function. `schedule` throws `eBPF CFG is not reducible` only when no unfinished block has a finished predecessor. The concrete `eval_op` / tracer switch implements only Add, Sub, And, UDiv, SDiv, `ICmp::EQ`, and `ICmp::UGT`. Other binops and other compares call `stop_unsupported`. A `MemInstr` is not produced by this lifter; the tracer would mark one unsupported and set `MemorySummary::Changed`. The block-visit guard is `code.size() + 8`.
- `alive2/rocq/upstream/theories/ebpfSyntax.v`: `instruction`, `aluOp`, `cmpOp`, `width`, `sizeOp`, `pseudo_ptr_ty`, `Pload` / `Pstore` / `Palu` / `Pjmpcmp` / `Pret`.
- `alive2/rocq/upstream/theories/ebpfDecoder.v`, whole file. `decode_insn` accepts LDX/ST/STX mode `0x60` as `Pload` / `Pstore`. Size field `(opcode >> 3) & 3`: 0 Word, 1 HalfWord, 2 Byte, 3 DBWord. `0x61` is `Pload Word`. `0x71` is `Pload Byte`. `0x73` is `Pstore Byte` from the source register (`check_imm_0`). ALU32/ALU64 and JMP32/JMP64 match the C++ opcode map for the opcodes this object uses, including JMP32 class `0x06` with code `0xa` as `Pjmpcmp (LT Unsigned) W32`. LDDW (`opcode 0x18`) consumes the next slot in `find_instr`; this object never takes that path. No `Pcall`.
- `alive2/rocq/upstream/theories/ebpfState.v`: `regset`, `outcome` (`Next` or `Stuck`). No fib-specific state.
- `alive2/rocq/upstream/theories/ebpfBinSem.v`, the definitions cited here, not a line-by-line reading of the commented-out frame allocator or the later atomic/race section. Rules used:
  - `eval_alu32` / `eval_alu64` / `exec_alu` (lines 331–390). ALU32 result is `Val.longofintu` of the 32-bit op (zero-extend). ALU64 ADD is `Val.addl`. ALU64 immediate uses `int64_of_int` (signed). MOV32 is `Val.longofintu` of the source. Shifts go through `eval_shift_mask` (W32 mask 31, W64 mask 63), including immediate shifts. The comment above `eval_shift_mask` says the kernel interpreter does not mask immediate shifts and the verifier rejects an immediate outside `0 .. width-1`. This object’s shift immediates are 8, 16, and 24, so the mask is not observable.
  - `eval_cmp32` / `eval_cmp64` / `exec_jmpcmp` (lines 412–498). JGT is unsigned `Cgt`. JLT is unsigned `Clt`. JMP32 compares `Val.loword`. JMP64 compares the full register. A taken branch does `Val.offset_ptr` of the PC by `off`, then `nextinstr`.
  - `exec_load` / `load` / `load_value_casting` (lines 560–589). A `Vlong` base is `cast_i2p` of `base + signed(off)` through `addr_map`. A `Vptr` base is `Val.offset_ptr`. Byte load is `Mint8unsigned`. Word load is `Mint32`, then a `Vint` is zero-extended to `Vlong`. Failure is `Stuck`.
  - `exec_store` / `store` (lines 633–646). Address is only `Val.offset_ptr` of the base. `cast_i2p` is not called. `exec_instr` does not pass `addr_map` into `exec_store` (line 897) but does pass it into `exec_load` (line 896). Byte store uses `eval_reg_immw W32` (`sizew Byte = W32`) and `Mint8unsigned`. CompCert’s `Val.offset_ptr` is not in this tree and was not read, so this report does not say what `offset_ptr` returns on a `Vlong`. The gap is the asymmetry: packet loads have an integer-address cast and packet stores do not.
  - `exec_ret` on an empty call stack (lines 819–821): `PC := Vnullptr`, `r0` kept. This program has no `Pcall`, so the stack stays empty if it starts empty.
  - `exec_instr` (lines 888–905). The catch-all is `Stuck`.
- `alive2/rocq/upstream/validator/Validation.v`, head through `bpf_interpreter`. Fuel 0 returns `Stuck`. No theorem about fib. `debug_fail_*` are constants `false`.
- `doc/观察.md` and `doc/局限.md`. Observation forms are `helper`, `branch`, `ret`, `mapWrite`, `packetWrite`. The loop section of `局限.md` says a program whose match is cut on a back edge is at most a weak match and does not enter the acceptance premise. That is a project limitation, not an instruction-set rule.

Not read, so not used as rules: CompCert `Values.v` / `Val.offset_ptr` / `decode_val` endianness, `Archi.big_endian`, `third_party/alive2/ir/instr.cpp` (only mentioned in a comment in `ebpf_lift.cpp`), the `XDP_*` macro header, any proof that this object implements `fib_u32`. In the theories searched, the only `Qed` spotted was `is_label_correct` in `ebpfBinSem.v`; its proof body was not used. `ebpfSyntax.v` has decidable register equality only.

Per-slot classification against those rules:

- Slot 0 and every later ALU/JMP slot matches a C++ `EbAlu` or `EbJmp` case and a Rocq `Palu` / `Pjmpcmp` / `Pret` case. Opcode class and alu/jmp code were checked against both decoders. Width: slots 3 and 4 are ALU64 (`0x07`); slot 5 is JMP64 (`0x05`); the other ALU slots are ALU32 (`0x04`); slots 11, 18, 21, 29 are JMP32 (`0x06`).
- Slots 1, 2, 6, 7, 8, 9 are LDX. Rocq `decode_insn` returns `Pload`. C++ `decode_ebpf` throws `unsupported class` at the first of them (slot 1) and never returns a vector, so `lift_ebpf` does not run on this object.
- Slots 32, 35, 36, 38 are STX. Rocq returns `Pstore Byte`. C++ has no STX class and no store constructor.

## IR mapping against the existing C++ lifter only

The mapping below is what `emit_alu` / `emit_cmp` / the EXIT arm would build for `LiftBug::None` if the decoder returned. It is not a conversion. The decoder throws at slot 1, so none of these instructions are lifted for this file.

ALU32 (`emit_alu`, `w32` true): `trunc` dst (and reg src) to i32, operate, `zext` to i64. Immediate src is `imm64` zero-extended, then truncated to i32.

| slots | C++ op | IR |
|---|---|---|
| 0, 19, 22, 23, 24, 39 | `EbAlu::Mov` imm W32 | zext(i32 imm) |
| 20, 25, 26, 30, 33 | `EbAlu::Mov` reg W32 | zext(trunc src) |
| 27, 28 | `EbAlu::Add` W32 | zext(i32 `BinOp::Add`) |
| 10 | `EbAlu::Sub` W32 | zext(i32 `BinOp::Sub`) |
| 13, 16, 17 | `EbAlu::Or` W32 | zext(i32 `BinOp::Or`) |
| 12, 14, 15 | `EbAlu::Lsh` W32 | zext(i32 `BinOp::Shl` by amount `& 31`) |
| 31, 34, 37 | `EbAlu::Rsh` W32 | zext(i32 `BinOp::LShr` by amount `& 31`) |
| 3 | `EbAlu::Mov` reg W64 | the i64 source, no trunc |
| 4 | `EbAlu::Add` imm W64 | i64 `BinOp::Add` of dst and sign-extended imm 8 |
| 5 | `EbJmp::Jgt` W64 | `ICmp::UGT` on the full i64 values; true edge to the exit block, false edge fall-through |
| 11, 18, 21, 29 | `EbJmp::Jlt` W32 | `ICmp::ULT` on i32 truncations; imm is `c32(uint32(imm))` |
| 40 | `EbJmp::Exit` | `Return(i64, r0)` |

Slot 29’s target is `<=` its index, so `build_blocks` would set `loop = true` and the header would get i64 phis. That CFG is a single natural loop (header at slot 25, one forward predecessor from slot 22, one back edge). This report does not claim `schedule` throws on it. It also does not claim the concrete tracer can execute it: `BinOp::Or`, `Shl`, and `LShr` are outside `eval_op`, `ICmp::ULT` is outside the tracer’s compare switch, and the block guard is 41+8 = 49 visits, while `n = 47` walks the body 46 times after several earlier blocks.

No C++ IR exists for slots 1, 2, 6–9, 32, 35, 36, 38. Do not invent loads, stores, a packet memory, or a CO-RE operator in that lifter. `LiftInit::Rocq` poisons `r1` and `r10` as `RegOrigin::Pointer` and would mark pointer ALU/JMP, but it still has no memory instructions. `make_alive_trace` uses `LiftInit::Zero` and would not be reached anyway.

## Memory, helper, map, and loop requirements

- Memory: required. Two word loads of `xdp_md` (`data`, `data_end`) with CO-RE byte_off records. Four zero-extending byte loads at `data+4..+7`. Four truncating byte stores at `data+8..+11`. The stores are `PacketWrite` in the sense of `doc/观察.md` (address comes from the packet pointer, not from a map value). Bounds are the JMP64 compare at slot 5 and the JMP32 compare at slot 11. Both must be kept; either one alone is a different program (counterexamples below).
- Helper: none. No `CALL` opcode (`0x85` or otherwise). No `Pcall`. Flag: no.
- Map: an ELF map object exists and is unused by `xdp`. No map load, no map store, no helper, no LDDW, no map fd, no map index. Flag: map symbol present, map operation absent. Do not emit `MapWrite`.
- Loop: one back edge, slot 29 → 25, unsigned `w5 < w2`, trip count `max(n, 0)` clamped so the taken count is at most 46. Not a helper loop. `doc/局限.md` says a back edge keeps the existing matcher at a weak match and out of the acceptance premise. Flag: yes.
- XPOST: none.
- Context pointer: `r1` on entry. Destroyed by slot 2. The data pointer used for packet memory is an integer (zero-extended `u32`), then slot 4 adds 8 with ALU64, which can produce bit 32. Slot 5 must stay a 64-bit unsigned compare.

## Conversion result

**NOT CONVERTED.**

`decode_ebpf` throws at slot 1 (`opcode 0x61`, class LDX). `lift_ebpf` is not run. The C++ AST cannot represent the ten memory instructions. Rocq can decode them, but `exec_store` does not apply the integer-to-region cast that `exec_load` applies, and no proof in the files read says the resulting memory operations match `fib.c`. Calling the missing C++ memory model unsupported and then reporting success would be false. This report does not do that.

## Proof coverage

No proof was read that this object implements `fib_u32` or that its packet stores match `store_u32`.

What exists, and was read, is an operational semantics, not a derivation for fib:

- Rocq `eval_alu32` / `eval_alu64` / `exec_jmpcmp` / `exec_load` / `exec_store` / `exec_ret` define the opcodes above. They are definitions. `Validation.v`’s interpreter returns `Stuck` when fuel runs out. It is not a proof.
- The C++ lifter is a translator for ALU and JMP only. Its concrete tracer does not even evaluate the `Or`, `Shl`, `LShr`, and `ULT` forms the symbolic lifter would emit. No theorem file was read next to `ebpf_lift.cpp`.
- `doc/局限.md` (loop section), read in full: matching does not build a “offset equals counter” relation across iterations, loop regions are not strictly expression-matched, and a back-edge cut is at most a weak match. fib’s only interesting computation is that loop, followed by four `PacketWrite`s whose values are the loop result. Even after a memory lifter exists, the current acceptance story does not cover this program.
- `doc/观察.md`: proposition 2 (behavior ↔ observation) is stated as not fully proved. Not claimed here.

Covered as decoded behavior, not as a proof: every slot’s opcode, width, registers, immediate, and jump target, against the decoder text. Not covered: CO-RE application as a semantics, integer packet addresses as CompCert pointers, store truncation versus `encode_val`, loop invariant for `fib_u32`, and the relationship between the unused `workload` map and the packet.

## Counterexample idea

Do not compare return codes alone. Both a correct run and a run that skips the stores can return 2. Observe the four bytes at `data+8` and the early-exit code 0.

1. Signed compare vs the real unsigned JMP32 JLT, clamp. Packet length 12, little-endian word at `data+4` equal to `0x80000000` (bytes `00 00 00 80`). Unsigned `w2 < 47` is false, so slot 19 sets `w2 = 47`, the loop writes `F47 = 0xb11924e1` as bytes `e1 24 19 b1` at `data+8`, and `r0 = 2`. A lifter that uses `ICmp::SLT` for opcode `0xa6` keeps `0x80000000`, then signed `< 2` skips the loop and stores `00 00 00 80`. Same shape distinguishes a signed reading of slot 21 or slot 29.

2. ALU64 add and JMP64 compare vs a 32-bit fold, slots 4–5. `data = 0xfffffff8`, `data_end = 4`, length field not relevant because the first check must fail. ALU64 `r7 = 0xfffffff8 + 8 = 0x100000000`. Unsigned 64-bit `r7 > r4` is true, so the program exits with `r0 = 0` and does not store. Treating slot 4 as ALU32 wraps `r7` to 0; a JMP32 compare then sees `0 > 4` and falls into the loads. The width of these two instructions is observable exactly at the 32-bit boundary. Slot 3’s MOV width is not, because `r1` is already zero-extended.

3. Dropping the clamp (slots 18–19) while keeping ALU32 add. `n = 48` is one past the clamp. `F48` does not fit in `u32`; the low 32 bits are `0x1e8d0a40`. The real object stores `F47` for every `n >= 47`. A model that deletes the clamp and still claims 32-bit wrap matches fib is wrong for `n = 48`. `n = 47` does not catch it.

4. Dropping slot 11 and keeping only slot 5. Length 11: `data+8 <= data_end` is true, residual `3 < 4` is true, real result is `r0 = 0` and no store. A model that stores `fib` at `data+8` writes past `data_end`.

5. Loop fuel. A concrete walker with a limit of `41 + 8` block visits cannot finish `n = 47` (46 body iterations plus the blocks before the header) and must not be reported as the fib result. Symbolic IR with a phi at slot 25 is not that walker, and it is also not a proof.

## Status

STATUS: ISSUES
