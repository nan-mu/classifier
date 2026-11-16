# buf observation

Observation of one BPF ELF so a later implementer can compile it. This report does not invent an ISA and does not emit a `.alive` file. Conversion result: **NOT CONVERTED**.

## Identity

- ELF: `/Volumes/SSD/bs/build/buf/bpf.o`
- sha256 computed with `shasum -a 256`: `9850410ce7b7fbef0174791ecfe621d485909c193294cf5ffab180d5c45c899c` (matches the requested digest; file length 8656)
- Notes read: `/Volumes/SSD/bs/build/buf/bpf.toml` (source path `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/buf.c`, which was also read)
- Tools actually run: `/opt/homebrew/opt/llvm/bin/llvm-readelf -a -S -r -s -h`, `/opt/homebrew/opt/llvm/bin/llvm-objdump -d --print-imm-hex --section=xdp`, `--section=.text`, `-s` for `xdp`, `license`, `.maps`, and a Python struct walk of the same bytes for slots, relocation types, BTF, and `.BTF.ext`
- Endianness: ELF `Data: 2's complement, little endian` (`ELFDATA2LSB`, `e_ident[5] = 1`). Class ELF64. `e_machine` EM_BPF. `e_type` REL. `e_entry` 0. No program headers. BTF magic `0xeb9f`, version 1, flags 0 (little-endian BTF). Every instruction field below was unpacked little-endian and matches `llvm-objdump`.

## Executable sections

`llvm-readelf -S` flags `AX` on exactly two sections. Both start at file offset `0x40`.

| index | name | size | flags | role |
| --- | --- | --- | --- | --- |
| 2 | `.text` | 0 | AX | empty. Not the program. `llvm-objdump -d --section=.text` prints no instructions. |
| 3 | `xdp` | `0x170` = 368 | AX, align 8 | the program. 368/8 = 46 slots. |

No other section is executable. There is no `.rel.xdp` and no `SHT_REL` whose `sh_info` is 3.

## Entry

One function.

- Symbol 11: `buf`, `FUNC GLOBAL`, section index 3 (`xdp`), value 0, size 368.
- `.BTF.ext` func_info (header `hdr_len` 32, `func_off` 0, `func_len` 20, record size 8): one record, `insn_off = 0`, `type_id = 0x13` = BTF type 19 `FUNC buf` / proto `(ctx: ptr xdp_md) -> int`. Section name at BTF string 217 is `xdp`.
- `llvm-objdump` labels the body `0000000000000000 <buf>:`.

There is no second entry and no jump table. LDDW does not appear: opcode `0x18` is absent, so no slot consumes a second word. Slot count equals instruction count: 46.

## Instruction list

Slots are instruction indices. `off` is the signed 16-bit field. Jump target is `slot + 1 + off` (`alive2/src/ebpf_decode.cpp` `jump_target`, lines 26-31), which matches the objdump labels. Class/opcode names below are the bitfields of the byte, checked against `alive2/rocq/upstream/theories/ebpfDecoder.v` `BPF_CLASS` and `decode_insn`. They are not a new encoding.

| slot | bytes (opcode regs off imm) | class | operation | jump |
| --- | --- | --- | --- | --- |
| 0 | `b4 00 0000 00000000` | ALU K | mov32 r0, 0 | |
| 1 | `61 12 0004 00000000` | LDX MEM W | r2 = *(u32*)(r1+4) | |
| 2 | `61 13 0000 00000000` | LDX MEM W | r3 = *(u32*)(r1+0) | |
| 3 | `bf 31 0000 00000000` | ALU64 X | r1 = r3 | |
| 4 | `07 01 0000 00000008` | ALU64 K | r1 += 8 | |
| 5 | `2d 21 0027 00000000` | JMP X | jgt r1, r2 | +39 → 45 `<L2>` |
| 6 | `71 34 0004 00000000` | LDX MEM B | r4 = *(u8*)(r3+4) | |
| 7 | `71 35 0005 00000000` | LDX MEM B | r5 = *(u8*)(r3+5) | |
| 8 | `67 05 0000 00000008` | ALU64 K | r5 <<= 8 | |
| 9 | `4f 45 0000 00000000` | ALU64 X | r5 \|= r4 | |
| 10 | `71 34 0006 00000000` | LDX MEM B | r4 = *(u8*)(r3+6) | |
| 11 | `67 04 0000 00000010` | ALU64 K | r4 <<= 16 | |
| 12 | `71 33 0007 00000000` | LDX MEM B | r3 = *(u8*)(r3+7) | |
| 13 | `67 03 0000 00000018` | ALU64 K | r3 <<= 24 | |
| 14 | `4f 43 0000 00000000` | ALU64 X | r3 \|= r4 | |
| 15 | `4f 53 0000 00000000` | ALU64 X | r3 \|= r5 | |
| 16 | `1c 12 0000 00000000` | ALU X | r2 -= r1 (32-bit) | |
| 17 | `2e 23 001b 00000000` | JMP32 X | jgt r3, r2 | +27 → 45 `<L2>` |
| 18 | `b4 04 0000 00000000` | ALU K | mov32 r4, 0 | |
| 19 | `16 03 000a 00000000` | JMP32 K | jeq r3, 0 | +10 → 30 `<L1>` |
| 20 | `b7 05 0000 00000000` | ALU64 K | r5 = 0 | |
| 21 | `bf 10 0000 00000000` | ALU64 X | r0 = r1 | `<L0>` |
| 22 | `0f 50 0000 00000000` | ALU64 X | r0 += r5 | |
| 23 | `71 06 0000 00000000` | LDX MEM B | r6 = *(u8*)(r0+0) | |
| 24 | `0c 56 0000 00000000` | ALU X | r6 += r5 (32-bit) | |
| 25 | `73 60 0000 00000000` | STX MEM B | *(u8*)(r0+0) = r6 | |
| 26 | `54 06 0000 000000ff` | ALU K | r6 &= 255 (32-bit) | |
| 27 | `0c 64 0000 00000000` | ALU X | r4 += r6 (32-bit) | |
| 28 | `07 05 0000 00000001` | ALU64 K | r5 += 1 | |
| 29 | `ad 35 fff7 00000000` | JMP X | jlt r5, r3 | **-9 → 21 `<L0>`** |
| 30 | `b4 00 0000 00000002` | ALU K | mov32 r0, 2 | `<L1>` |
| 31 | `bc 35 0000 00000000` | ALU X | mov32 r5, r3 | |
| 32 | `04 05 0000 00000004` | ALU K | r5 += 4 (32-bit) | |
| 33 | `ae 52 000b 00000000` | JMP32 X | jlt r2, r5 | +11 → 45 `<L2>` |
| 34 | `0f 31 0000 00000000` | ALU64 X | r1 += r3 | |
| 35 | `bc 42 0000 00000000` | ALU X | mov32 r2, r4 | |
| 36 | `74 02 0000 00000018` | ALU K | r2 >>= 24 (32-bit logical) | |
| 37 | `73 21 0003 00000000` | STX MEM B | *(u8*)(r1+3) = r2 | |
| 38 | `bc 42 0000 00000000` | ALU X | mov32 r2, r4 | |
| 39 | `74 02 0000 00000010` | ALU K | r2 >>= 16 (32-bit logical) | |
| 40 | `73 21 0002 00000000` | STX MEM B | *(u8*)(r1+2) = r2 | |
| 41 | `bc 42 0000 00000000` | ALU X | mov32 r2, r4 | |
| 42 | `74 02 0000 00000008` | ALU K | r2 >>= 8 (32-bit logical) | |
| 43 | `73 21 0001 00000000` | STX MEM B | *(u8*)(r1+1) = r2 | |
| 44 | `73 41 0000 00000000` | STX MEM B | *(u8*)(r1+0) = r4 | |
| 45 | `95 00 0000 00000000` | JMP | exit | `<L2>` |

Jump slots: 5, 17, 19, 29, 33, and exit at 45. The only backward edge is slot 29 → 21. No unconditional JA, no CALL (`0x85`), no tail call, no atomic opcode, no `0x18` LDDW.

What the bytes do, following `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/buf.c` (the ELF was built from that file; BTF string `int buf(struct xdp_md *ctx)`):

- r1 on entry is `ctx`. Slot 1 loads `xdp_md.data_end` (u32 at +4). Slot 2 loads `xdp_md.data` (u32 at +0).
- Slot 3 copies data into r1; slot 4 adds 8. Slot 5 exits if `data+8 > data_end` (64-bit unsigned). r0 is still the 0 written at slot 0.
- Slots 6-15 assemble a little-endian u32 from bytes `data[4..7]` into r3 (explicit byte loads and shifts, not one `LDX W`). That overwrites the data pointer; the payload pointer stays in r1.
- Slot 16 is 32-bit `r2 -= r1`, i.e. `avail = (u32)(data_end - (data+8))`. Slot 17 exits if `param > avail` (32-bit unsigned).
- Slots 21-29 loop while `r5 < r3` (64-bit). Each iteration reads `payload[i]`, adds the index in 32-bit, stores the low byte, masks that byte, and adds it into r4. r5 starts at 0 (slot 20) and increments by 1. Slot 19 skips the loop when param is 0.
- Slot 30 sets r0 to 2 before the trailing check. Slot 32 does 32-bit `param+4` (wraps mod 2^32). Slot 33 skips the stores if `avail < param+4` (32-bit unsigned) and still exits with r0 = 2.
- Slots 34-44 store r4 little-endian at `payload+param` as four byte stores (>>24 at +3, >>16 at +2, >>8 at +1, low byte at +0).
- Early exits (slots 5 and 17) reach slot 45 with r0 = 0. The other paths reach it with r0 = 2. The C source names those returns `XDP_ABORTED` and `XDP_PASS`. BTF has no ENUM type for `xdp_action`; the immediates in the object are 0 and 2. DWARF/BTF strings list `XDP_ABORTED`, `XDP_DROP`, `XDP_PASS`, `XDP_TX`, `XDP_REDIRECT` but this report does not treat string order as a decoded enum.

r7, r8, r9, r10 are never written. No stack slot is addressed.

## Real disassembly

Command: `/opt/homebrew/opt/llvm/bin/llvm-objdump -d --print-imm-hex --section=xdp /Volumes/SSD/bs/build/buf/bpf.o`

```
0000000000000000 <buf>:
       0:	b4 00 00 00 00 00 00 00	w0 = 0x0
       1:	61 12 04 00 00 00 00 00	w2 = *(u32 *)(r1 + 0x4)
       2:	61 13 00 00 00 00 00 00	w3 = *(u32 *)(r1 + 0x0)
       3:	bf 31 00 00 00 00 00 00	r1 = r3
       4:	07 01 00 00 08 00 00 00	r1 += 0x8
       5:	2d 21 27 00 00 00 00 00	if r1 > r2 goto +0x27 <L2>
       6:	71 34 04 00 00 00 00 00	w4 = *(u8 *)(r3 + 0x4)
       7:	71 35 05 00 00 00 00 00	w5 = *(u8 *)(r3 + 0x5)
       8:	67 05 00 00 08 00 00 00	r5 <<= 0x8
       9:	4f 45 00 00 00 00 00 00	r5 |= r4
      10:	71 34 06 00 00 00 00 00	w4 = *(u8 *)(r3 + 0x6)
      11:	67 04 00 00 10 00 00 00	r4 <<= 0x10
      12:	71 33 07 00 00 00 00 00	w3 = *(u8 *)(r3 + 0x7)
      13:	67 03 00 00 18 00 00 00	r3 <<= 0x18
      14:	4f 43 00 00 00 00 00 00	r3 |= r4
      15:	4f 53 00 00 00 00 00 00	r3 |= r5
      16:	1c 12 00 00 00 00 00 00	w2 -= w1
      17:	2e 23 1b 00 00 00 00 00	if w3 > w2 goto +0x1b <L2>
      18:	b4 04 00 00 00 00 00 00	w4 = 0x0
      19:	16 03 0a 00 00 00 00 00	if w3 == 0x0 goto +0xa <L1>
      20:	b7 05 00 00 00 00 00 00	r5 = 0x0
<L0>:
      21:	bf 10 00 00 00 00 00 00	r0 = r1
      22:	0f 50 00 00 00 00 00 00	r0 += r5
      23:	71 06 00 00 00 00 00 00	w6 = *(u8 *)(r0 + 0x0)
      24:	0c 56 00 00 00 00 00 00	w6 += w5
      25:	73 60 00 00 00 00 00 00	*(u8 *)(r0 + 0x0) = w6
      26:	54 06 00 00 ff 00 00 00	w6 &= 0xff
      27:	0c 64 00 00 00 00 00 00	w4 += w6
      28:	07 05 00 00 01 00 00 00	r5 += 0x1
      29:	ad 35 f7 ff 00 00 00 00	if r5 < r3 goto -0x9 <L0>
<L1>:
      30:	b4 00 00 00 02 00 00 00	w0 = 0x2
      31:	bc 35 00 00 00 00 00 00	w5 = w3
      32:	04 05 00 00 04 00 00 00	w5 += 0x4
      33:	ae 52 0b 00 00 00 00 00	if w2 < w5 goto +0xb <L2>
      34:	0f 31 00 00 00 00 00 00	r1 += r3
      35:	bc 42 00 00 00 00 00 00	w2 = w4
      36:	74 02 00 00 18 00 00 00	w2 >>= 0x18
      37:	73 21 03 00 00 00 00 00	*(u8 *)(r1 + 0x3) = w2
      38:	bc 42 00 00 00 00 00 00	w2 = w4
      39:	74 02 00 00 10 00 00 00	w2 >>= 0x10
      40:	73 21 02 00 00 00 00 00	*(u8 *)(r1 + 0x2) = w2
      41:	bc 42 00 00 00 00 00 00	w2 = w4
      42:	74 02 00 00 08 00 00 00	w2 >>= 0x8
      43:	73 21 01 00 00 00 00 00	*(u8 *)(r1 + 0x1) = w2
      44:	73 41 00 00 00 00 00 00	*(u8 *)(r1 + 0x0) = w4
<L2>:
      45:	95 00 00 00 00 00 00 00	exit
```

The notes file `bpf.toml` `[xdp]` asm block matches this listing, including the `0x170` size.

## Relocations, objects, maps, BTF

No relocation applies to the `xdp` instruction bytes. Relocation types present, counted from `SHT_REL` entries (`r_info` low 32 bits):

| section | `sh_info` | type | count | meaning for this object |
| --- | --- | --- | --- | --- |
| `.rel.debug_info` | 8 | 3 `R_BPF_64_ABS32` | 5 | debug, not code |
| `.rel.debug_str_offsets` | 10 | 3 | 52 | debug |
| `.rel.debug_addr` | 13 | 2 `R_BPF_64_ABS64` | 6 | symbols `xdp` (4), `LICENSE`, `workload` |
| `.rel.BTF` | 15 | 4 `R_BPF_64_NODYLD32` | 2 | BTF datasec fixups, not code |
| `.rel.BTF.ext` | 17 | 4 `R_BPF_64_NODYLD32` | 30 | all against section symbol `xdp` |
| `.rel.debug_frame` | 19 | 3 and 2 | 1 + 1 | debug, one `xdp` ABS64 |
| `.rel.debug_line` | 21 | 3 and 2 | 5 + 1 | debug, one `xdp` ABS64 |

Type 1 (`R_BPF_64_64`, the LDDW map/fd reloc that `tooling/server/src/bpf_image.rs` `map_lddw_slots` looks for) does not occur. There is no map-index immediate and no `PSEUDO_MAP_IDX` / `PSEUDO_MAP_FD` LDDW (`ebpfDecoder.v` `decode_lddw_insn` is unused here).

Three different references, kept apart:

1. Raw object `workload`. Symbol 13, `OBJECT GLOBAL`, section 5 `.maps`, value 0, size 32. Section image is 32 zero bytes (`llvm-objdump -s --section=.maps`). BTF type 15 `VAR workload` linkage 1, type 14 anonymous struct size 32 (`type`, `max_entries`, `key`, `value` at bit offsets 0, 64, 128, 192). BTF type 23 `DATASEC .maps` records that var at offset 0 size 32. `.rel.BTF` offset `0x250` is `R_BPF_64_NODYLD32` against `workload`. `.rel.debug_addr` has one `R_BPF_64_ABS64` against `workload`. None of these patch `xdp`. The notes file says `BPF_MAP_TYPE_HASH`, `max_entries = 2`, `key_size = 1`, `value_size = 32` (`struct exec_val`, BTF type 11, eight `__u32`, size 32). Those integers are not stored in the `.maps` image; the image is zeros. The program text never names this object.
2. Raw object `LICENSE`. Symbol 12, section 4 `license`, size 4, bytes `47 50 4c 00` (`GPL\0`). BTF type 22 `VAR LICENSE`, datasec `license`. `.rel.BTF` offset `0x268` is `R_BPF_64_NODYLD32` against `LICENSE`. Not a code reference.
3. Not an XPOST relocation. No `.xpost.meta`, `.xpost.image`, or `.xpost.mem`. The file is ET_REL EM_BPF, not the compact container in `tooling/vendor/xpost-elf`. No map-index reference in the instruction stream.

CO-RE, from `.BTF.ext` (`core_off` 464, `core_len` 44, record size 16, two records, section name `xdp`), not from an ELF reloc on the insn:

| insn byte off | slot | type_id | access string | kind |
| --- | --- | --- | --- | --- |
| `0x8` | 1 | 17 `xdp_md` | `0:1` | 0 |
| `0x10` | 2 | 17 `xdp_md` | `0:0` | 0 |

BTF type 17 `xdp_md` size 24: `data` at bit 0, `data_end` at bit 32, then `data_meta`, `ingress_ifindex`, `rx_queue_index`, `egress_ifindex`, each `__u32`. Access `0:0` is `data`, `0:1` is `data_end`. The instruction offsets are already 0 and 4, which match that layout. Kind is the numeric field 0; this report did not read an enum definition that names kind 0. A loader could still patch those offsets if a target `xdp_md` differed. As the file sits, nothing rewrites the `xdp` bytes.

The other 28 `.rel.BTF.ext` entries are the func/line section-symbol fixups (record headers and line records), still not instruction patches. Line info has 27 records; this report did not decode every line-number field.

## Semantic rules actually read

C++ decoder, `alive2/src/ebpf_decode.cpp`, read in full. `alive2/src/ebpf.h`, read in full.

- ALU class `0x04` and ALU64 class `0x07` (lines 61-120): ADD `0x00`, SUB `0x10`, OR `0x40`, AND `0x50`, LSH `0x60`, RSH `0x70`, MOV `0xb0` with offset 0. Register vs immediate is opcode bit `0x08`. A non-zero ALU offset is rejected except for the DIV/MOD and MOVSX cases, which this object does not use. Immediate ALU requires `src == 0`.
- JMP class `0x05` and JMP32 class `0x06` (lines 121-163): JEQ `0x10`, JGT `0x20`, JLT `0xa0`, EXIT `0x90`. EXIT requires class JMP, immediate source, offset 0, src 0, dst 0. Conditional jump target is `index + 1 + off`.
- Any other class, including LDX `0x01` and STX `0x03`, hits lines 164-168 and throws `unsupported class in opcode`. That is the first instruction of this object after slot 0: slot 1, opcode `0x61`.

C++ lifter, `alive2/src/ebpf_lift.cpp` and `alive2/src/ebpf_lift.h`, read in full. It only consumes `EbInsn`, whose payload is `std::variant<EbAlu, EbJmp>` (`ebpf.h` lines 38-41). There is no load or store constructor.

- `build_blocks` (lines 214-229): a jump whose target is `<=` its own index sets `loop`.
- `emit_alu` (lines 516-539): ALU64 immediate is sign-extended (`imm64`, lines 196-199) unless `LiftBug::ImmNoSignExtend`. ALU32 truncates both operands to i32, operates, then zero-extends to i64.
- `emit_wide` / `emit_narrow` / `arith_op` / `shift_op` (lines 552-677): ADD → `BinOp::Add`, SUB → `BinOp::Sub`, OR → `BinOp::Or`, AND → `BinOp::And`, LSH → `BinOp::Shl` after AND 63 (64-bit) or 31 (32-bit), RSH → `BinOp::LShr` with the same mask, MOV → the source value (32-bit MOV then zext). ALU64 MOV is `bare_mov`.
- `emit_cmp` / `icmp_cond` (lines 643-693): JEQ → `ICmp::EQ`, JGT → `ICmp::UGT`, JLT → `ICmp::ULT`. JMP32 compares the truncated 32-bit values. Taken edge is `jump_target`; not-taken edge is the next instruction. EXIT becomes `Return` of r0 (lines 496-497).
- `LiftInit::Zero` (default of `lift_ebpf`) zeros every register, then replaces named inputs. `LiftInit::Rocq` poisons r1 and r10 and marks that poison `RegOrigin::Pointer`; other registers are undef. `execute_ebpf` uses the default Zero init (`ebpf_run.cpp` line 51, no init argument).
- `Lifter::concrete` (lines 713-978) evaluates only `BinOp` Add, Sub, And, UDiv, SDiv and `ICmp` EQ, UGT. OR, shifts, ULT, and `ConversionOp` (the trunc/zext on every ALU32) take the unsupported path (lines 877-889 and 962-966). A step cap of `code.size() + 8` marks the trace incomplete (lines 844-851). `MemInstr` is recorded as memory-changed and then unsupported (lines 962-966). This object was not executed.

Rocq decoder, `alive2/rocq/upstream/theories/ebpfDecoder.v`, read in full.

- Same ALU and JMP opcodes as above, producing `Palu` / `Pjmpcmp` / `Pret` (`decode_insn` lines 54-159).
- Memory mode `(opcode >> 5) == 3` (the `0x60` MEM mode), size bits `(opcode >> 3) & 3`: 0 Word, 1 HalfWord, 2 Byte, 3 DBWord (lines 161-183). LDX with imm 0 is `Pload`. STX with imm 0 is `Pstore` of the source register. That covers every LDX/STX in this object (sizes Word and Byte only).
- `find_instr` (lines 257-285) treats opcode `0x18` as a two-slot LDDW. This object never takes that branch.
- `decode_lddw_insn` (lines 235-246) is the map-fd / map-index / map-value split. Unused here.

Rocq syntax, `alive2/rocq/upstream/theories/ebpfSyntax.v`, read in full. Relevant constructors: `Pload`, `Pstore`, `Palu`, `Pjmpcmp`, `Pret` (lines 224-245). `sizew Byte/HalfWord/Word = W32`, `DBWord = W64`.

Rocq step rules, `alive2/rocq/upstream/theories/ebpfBinSem.v`, these definitions were read: `nextinstr` (66-67), `eval_reg_immw` (94-106), `eval_val_int` (108-116), `eval_shift_mask` (236-243), `eval_alu32` (332-353), `eval_alu64` (355-375), `exec_alu` (377-390), `eval_cmp32` / `eval_cmp64` (412-444), `exec_jmpcmp` (484-498), `cast_i2p` (512-522), `loadv_unaligned` / `storev_unaligned` / `load` (544-567), `load_value_casting` (569-573), `exec_load` (575-589), `store` / `exec_store` (633-646), `exec_ret` (819-839), `exec_instr` (888-905). Also the comment at 198-234 that the kernel interpreter masks register shifts but not immediate shifts, while the verifier rejects an immediate shift outside `0 .. width-1`, and the Coq model masks both.

Rules that apply to these opcodes:

- `nextinstr` adds `Ptrofs.one` to PC. `exec_jmpcmp` adds `off` to PC only when the condition is true, then `nextinstr`. Net displacement of a taken branch is `1 + off`, same as the C++ target. A `None` condition is `Stuck`.
- ALU32 (`eval_alu32`): `Val.loword` of both operands, then `Val.longofintu` (zero-extend). ADD/SUB/OR/AND/MOV are the CompCert `Val` operations. LSH/RSH use `eval_shift_mask W32`, which is AND 31. ALU64 (`eval_alu64`): `eval_val_int W64` sign-extends an immediate (`int64_of_int` = `Int64.repr (Int.signed i)`, line 81). Shifts use `eval_shift_mask W64`, which first narrows a `Vlong` through `int_of_int64` and then ANDs 63. The immediates in this object are 1, 8, 16, 24, all inside both the mask and the verifier range, so the C++ `And 63/31` and this mask agree on these particular instructions. `exec_alu` has a same-register special case (SUB/XOR become 0). No instruction here has `dst == src`.
- Unsigned jumps: `eval_cmp64` / `eval_cmp32` use `Val.cmplu_bool` / `Val.cmpu_bool` with `Cgt` or `Clt`. JEQ uses `Ceq`. JMP32 compares `Val.loword`. JMP64 compares the full register. A 64-bit immediate is sign-extended; the only immediate compare here is JEQ against 0.
- `exec_load`: if the address register is `Vptr`, `Val.offset_ptr` plus the offset; if it is `Vlong`, `cast_i2p` of `base + signed(offset)` through `addr_map`. Anything else, or a failed `cast_i2p`, or a failed `Mem.loadbytes`, is `Stuck`. The loaded value passes through `load_value_casting`: a `Vint` becomes `Vlong` of `Int.unsigned` (zero-extend). Byte and word loads in this object therefore write a zero-extended `Vlong`, not a `Vptr`. `load` uses `Mint8unsigned` for Byte and `Mint32` for Word.
- `exec_store`: `Val.offset_ptr` on the address register, then `storev_unaligned`. It does **not** call `cast_i2p`. The stored value is `eval_reg_immw (sizew k)`. For Byte, `sizew` is W32, so a `Vlong` is narrowed with `Int.repr (Int64.unsigned i)` and `Mint8unsigned` keeps the low 8 bits. `storev_unaligned` returns `None` unless the address is a `Vptr`, and `exec_store` then returns `Stuck`.
- `exec_ret` with an empty call stack sets PC to `Vnullptr` and leaves r0. This program has no call, so the stack stays empty if it started empty. `exec_instr` routes `Pload` to `exec_load`, `Pstore` to `exec_store`, `Palu` to `exec_alu`, `Pjmpcmp` to `exec_jmpcmp`, `Pret` to `exec_ret`. `exec_instr_event` records `eBPF_vload` / `eBPF_vstore` for those two.

`alive2/rocq/upstream/validator/Validation.v` was read through `compare_final_state` (lines 1-120) and searched for `Theorem` / `Lemma` (none). `bpf_interpreter` (lines 25-45) is an executable fuel loop: fuel 0 returns `Stuck`; PC must be a `Vptr` or the step is `Stuck`. It is not a proof about `buf`.

`alive2/rocq/upstream/theories/CMemoryModel.v` was read only through line 80. It is a separate action model (Lock/Load/Store/RMW with memory orders). It is not the memory `exec_load` uses. The rest of that file was not read. Not read at all: `ebpfState.v`, `GlobalSem.v`, `Nondeterminism.v`, `SCLanguage.v`, and the body of `Lemma is_label_correct` in `ebpfBinSem.v` (the only lemma name the search hit). CompCert's `Val.offset_ptr` definition was not opened; the Stuck path is the `None` branch of `exec_store` / `storev_unaligned`, which this report did read.

`alive2/src/ebpf_run.cpp` was read through `observe_ebpf`'s symexec setup (lines 1-237). `configure_pure_alu` forces `does_int_load`, `does_int_store`, `does_ptr_load`, `does_ptr_store` false. `execute_ebpf` calls `decode_ebpf` first; on a loop it throws unless `unroll != 0`, then `fn.unroll(unroll)`. `observe_ebpf` uses `LiftInit::Rocq` and, when `info.loop` is true, returns before `sym_exec` (lines 227-228).

## IR mapping against the existing C++ lifter only

`decode_ebpf` throws at slot 1. `lift_ebpf` is not reached. There is no IR for this object. The rows below are the mapping those functions implement for the ALU/JMP opcodes that do occur, if a memory instruction were ever represented. LDX and STX have no row: they are not in `EbInsn`, `emit` never builds a `MemInstr`, and `configure_pure_alu` turns packet memory off.

| slots | decoded as | IR the lifter would emit |
| --- | --- | --- |
| 0, 18, 30 | `EbAlu::Mov` W32 imm 0, 0, 2 | trunc of the zero-extended imm, then `ZExt` to i64 |
| 3, 21 | `EbAlu::Mov` W64 reg | copy the source value (`bare_mov`) |
| 31, 35, 38, 41 | `EbAlu::Mov` W32 reg | `Trunc` to i32, `ZExt` to i64 (clears bits 32-63) |
| 4, 28 | `EbAlu::Add` W64 imm 8, 1 | `BinOp::Add` i64, imm sign-extended |
| 22, 34 | `EbAlu::Add` W64 reg | `BinOp::Add` i64 |
| 24, 27 | `EbAlu::Add` W32 reg | trunc both, `BinOp::Add` i32, zext |
| 32 | `EbAlu::Add` W32 imm 4 | same, 32-bit add, wraps in i32 |
| 16 | `EbAlu::Sub` W32 reg | trunc both, `BinOp::Sub` i32, zext |
| 8, 11, 13 | `EbAlu::Lsh` W64 imm 8, 16, 24 | `BinOp::And` with 63, then `BinOp::Shl` |
| 36, 39, 42 | `EbAlu::Rsh` W32 imm 24, 16, 8 | trunc, `BinOp::And` with 31, `BinOp::LShr`, zext |
| 9, 14, 15 | `EbAlu::Or` W64 reg | `BinOp::Or` i64 |
| 26 | `EbAlu::And` W32 imm 255 | trunc, `BinOp::And` i32, zext |
| 5 | `EbJmp::Jgt` W64 r1, r2, +39 | `ICmp::UGT` i64, branch to the block at 45 or fall through to 6 |
| 17 | `EbJmp::Jgt` W32 r3, r2, +27 | trunc, `ICmp::UGT`, branch to 45 or 18 |
| 19 | `EbJmp::Jeq` W32 r3, imm 0, +10 | trunc, `ICmp::EQ` against i32 0, branch to 30 or 20 |
| 29 | `EbJmp::Jlt` W64 r5, r3, -9 | `ICmp::ULT` i64, branch to 21 or 30; `loop = true` |
| 33 | `EbJmp::Jlt` W32 r2, r5, +11 | trunc, `ICmp::ULT`, branch to 45 or 34 |
| 45 | `EbJmp::Exit` | `Return` i64 r0 |
| 1, 2, 6, 7, 10, 12, 23 | LDX | no IR. Decoder throws. |
| 25, 37, 40, 43, 44 | STX | no IR. Decoder throws. |

`build_blocks`, applied to this jump set and not run: leaders at 0 and at every jump target and every instruction after a jump, so blocks `[0,5]`, `[6,17]`, `[18,19]`, `[20,20]`, `[21,29]`, `[30,33]`, `[34,44]`, `[45,45]`. The block at 21 has a back-edge from 29, so the lifter would `place_phis` for written registers, including r0 and r4. Exit has predecessors from slots 5, 17, 33, and the fall-through of 44, so r0 at the exit is a join of 0 and 2, not the constant 2.

`Lifter::concrete` would still refuse the OR, the shifts, the ULT back-edge, and every ALU32 `ConversionOp` even if decode succeeded. That function is not a substitute for the symbolic `BinOp` mapping above.

## Memory, helper, map, loop

- Memory: required. 7 loads (2× u32 from `ctx`, 5× u8 from the packet) and 5 byte stores (1 inside the loop, 4 for the little-endian accumulator). The u32 ctx loads are the only accesses CO-RE describes. The byte accesses are ordinary packet offsets with no reloc. Bounds the object itself checks: `data+8 <= data_end` (64-bit, slot 5), `param <= avail` (32-bit, slot 17), `avail >= param+4` (32-bit, slot 33, wrapping). It does not check that each `payload[i]` is in range beyond `param <= avail`, and it does not check that `param+4` avoids 32-bit wrap.
- Address kind the Rocq rules actually implement: slots 1-2, if r1 is a `Vptr`, load u32 and zero-extend to `Vlong`. Slot 3 copies that integer into r1. Later byte loads (slots 6, 7, 10, 12, 23) therefore see a `Vlong` and succeed only if `cast_i2p` hits `addr_map`. Later byte stores (25, 37, 40, 43, 44) call `exec_store`, which does not use `cast_i2p`. A `Vlong` address becomes `Stuck` there. `exec_alu` ADD does not turn a `Vlong` into a `Vptr`. An implementer who only adds a decoder still cannot store the checksum or the updated payload byte under the rule that was read.
- Helper: none. No call instruction. Flag: no.
- Map: the ELF contains one unused hash-map object (`workload`), described above. The program does not load a map fd, does not use a map index, and does not call a map helper. Flag: object present, program reference absent. Do not treat the zero `.maps` image as a map type.
- Loop: yes. Slot 29 offset -9 to slot 21, bounded by the u32 in r3 when that value's high bits stay 0 (they do if r3 is the zero-extended byte assembly). `execute_ebpf` refuses `unroll == 0`. `observe_ebpf` returns before symbolic execution when `loop` is set. The concrete step cap is `46 + 8` instructions, which cannot finish a loop whose `param` is larger than a handful of iterations. Flag: yes.

## Conversion result

**NOT CONVERTED.**

`decode_ebpf` rejects opcode `0x61` at slot 1 (`ebpf_decode.cpp` lines 164-168). No `EbInsn` vector is produced, so `lift_ebpf`, `execute_ebpf`, and `observe_ebpf` do not run. No `.alive` file is emitted. This is not a successful classification of an unsupported model: the C++ lifter has no memory instruction to be unsupported, and the Rocq store rule as read gets stuck on the integer packet pointer this object computes.

## Proof coverage

Nothing read proves this program.

- `Validation.v` has an interpreter and a concrete-register comparison (`compare_final_state` checks r0 only). No theorem. Fuel exhaustion is `Stuck`. PC must already be a code pointer.
- `ebpfBinSem.v` defines the step rules above. The only lemma name found by search is `is_label_correct`; its statement was not read. No equivalence with `buf.c`.
- The C++ checker path never sees this object, because decode throws first. Even a loop-free ALU fragment would be symbolically executed with packet loads and stores disabled (`configure_pure_alu`). A loop, which this program has, is dropped by `observe_ebpf` before `sym_exec`.
- `CMemoryModel.v` was not used as a proof of these loads. It is a different model, and only its opening was read.

## Counterexample idea

Do not use i ≥ 256 to claim the stored byte differs from `(__u8)(payload[i] + (__u8)i)`. `256*k` does not change the low 8 bits, and slot 26 masks with `0xff` before r4 accumulates, so the byte and the accumulator match that expression.

A real split is the 32-bit `param+4` at slot 32.

- Let `data_end - data = 8 + avail` with `avail = param = 0xfffffffe` (both fit in the u32 fields). Slot 5 does not exit (`data+8 <= data_end`). Slot 17 does not exit (`param > avail` is false). Slot 32 computes `param+4` as `2` mod 2^32. Slot 33's `avail < 2` is false, so slots 37-44 store four bytes at `payload+param`, which is `data+8+0xfffffffe`, past a packet whose length is `8+0xfffffffe`. A spec that compares `avail >= param+4` in unbounded integers refuses that store. The object performs it. r0 is 2 either way only if the spec still returns PASS while skipping the store; the memory differs.
- A small witness for the early exit, not the wrap: `data_end = data` (or any span shorter than 8). Slot 5 jumps to 45. r0 stays 0. No byte store runs.
- A small witness for the success path: 13-byte region, bytes at `data+4..7` equal the little-endian u32 `1`, byte at `data+8` equal `0x10`, and `data_end = data+13` so `avail = 5`. The loop runs once, stores `0x11` at `data+8`, stores u32 `0x11` little-endian at `data+9`, returns 2. If `exec_store` is left as read, this same input is `Stuck` on slot 25 even though the loads can be `cast_i2p`'d. That separates "Linux would write" from "the Rocq store rule returns Stuck".

## Status

ISSUES
