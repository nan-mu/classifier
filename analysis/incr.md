# incr observation

Observation for a later implementer. This file does not invent a shared ISA and does not emit an Alive2 program. Conversion result: **NOT CONVERTED**.

## Evidence

Commands actually run:

- `shasum -a 256 /Volumes/SSD/bs/build/incr/bpf.o` → `8103639ae59dff73ffe7eef0c43cd9e7c3893bcc4a570bfad674635b66eca99b` (matches the expected digest)
- `file` on that path: ELF 64-bit LSB relocatable, eBPF, not stripped
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -a -S -s -r -n --section-headers --symbols --relocations --program-headers --notes`
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -h -t -r -s` and `-s -j xdp -j license -j .maps -j .text`
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r --section=xdp` and `-d -r` on the whole file (only `xdp` is disassembled)
- `bpf.toml` at `/Volumes/SSD/bs/build/incr/bpf.toml`. Its `[xdp]` asm matches the objdump mnemonics. Its `[CORE]` records match the `.BTF.ext` core-relo records parsed below.
- C input named by that toml: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/incr.c` (read only as the named source, not as the ISA)

Slot fields below were unpacked from the `xdp` bytes at file offset `0x40` (little-endian `opcode, dst:4|src:4, off:i16, imm:i32`). They match the objdump raw encoding.

Rules read:

- `alive2/src/ebpf.h` (`EbInsn` is only `EbAlu` or `EbJmp`)
- `alive2/src/ebpf_decode.cpp` (whole file). ALU/JMP only. Any other class throws at lines 164–167.
- `alive2/src/ebpf_lift.cpp`: `jump` handling via `build_blocks` / `jump_target`, `emit_alu`, `emit_wide`, `emit_narrow`, `shift`, `emit_cmp`, `icmp_cond`, `concrete` (ICmp only EQ/UGT; BinOp only Add/Sub/And/UDiv/SDiv; a `MemInstr` is marked unsupported), `make_alive_trace`
- `alive2/src/ebpf_lift.h` (`LiftInfo.loop`, register origins; no memory opcode)
- `alive2/src/ebpf_run.cpp` lines 18–44 (`configure_pure_alu` forces every memory flag off, then `execute_ebpf` calls `decode_ebpf`)
- `alive2/src/ebpf_test.cpp` lines 67–87 (`reject_encoding("LDX", 0x61, ...)`, and the same for ST/STX/LDDW/CALL)
- `alive2/src/ebpf_file.cpp` (reads the whole file as a raw bytecode blob; it does not parse ELF sections)
- `alive2/rocq/upstream/theories/ebpfSyntax.v` (`instruction`, `aluOp`, `cmpOp`, `pseudo_ptr_ty`, lines 148–245)
- `alive2/rocq/upstream/theories/ebpfDecoder.v` (`decode_insn`, `decode_lddw_insn`, `find_instr`)
- `alive2/rocq/upstream/theories/ebpfBinSem.v`: `nextinstr` (line 66), `int64_of_int` (line 81), `eval_reg_immw`, `eval_val_int`, `eval_shift_mask` (line 236), `eval_alu32`, `eval_alu64`, `exec_alu`, the jump comment at lines 392–410, `eval_cmp32`, `eval_cmp64`, `exec_jmpcmp`, `cast_i2p`, `load` / `loadv_unaligned`, `exec_load`, `store` / `exec_store`, the live `exec_ret` at line 819 (not the commented definition at 811), `exec_instr` at line 888. Also `Lemma is_label_correct` (lines 41–47): it matches a `Plabel` constructor. That constructor is not in the `instruction` inductive read in `ebpfSyntax.v`, and this object has no labels, so the lemma is not a rule for these jumps.
- `alive2/rocq/upstream/validator/Validation.v` lines 25–45 only (`bpf_interpreter` fetches only when `rs PC` is `Vptr`; otherwise `Stuck`)
- `alive2/rocq/upstream/validator/Extraction.v` lines 13–14 (`Archi.ptr64` true, `Archi.big_endian` false)
- `tooling/vendor/xpost-elf/src/lib.rs` and `encode.rs` section names (`.xpost.meta`, `.xpost.image`, `.xpost.mem`) so XPOST is not confused with this object

Not read, so not used as rules: `CMemoryModel.v`, `GlobalSem.v`, `SCLanguage.v`, `Nondeterminism.v`, `ebpfState.v` past the `outcome` / `addr_region` declarations, the rest of `Validation.v`, CompCert `decode_val` / `encode_val` / `Val.offset_ptr`. The bpf wrappers select `Mint8unsigned` or `Mint32`; what those chunks do to bytes is CompCert, and that code was not read. A `Theorem`/`Lemma` search under `alive2/rocq` found only `ireg_eq`, `preg_eq`, and `is_label_correct`. No proof about this program was read.

## ELF

| field | value |
| --- | --- |
| class / data | ELF64, little endian (`EI_CLASS` = 2, `EI_DATA` = 1) |
| type / machine | `REL` (`e_type` 1), `EM_BPF` (247) |
| entry | `e_entry` 0. No program headers. This is not an executable image. |
| endianness of the encoding | little endian. Each slot is 8 bytes, opcode at the first byte. |
| section headers | 26, starting at file offset `0x19f8` |

Executable sections (`AX`), from `llvm-readelf -S`:

| section | off | size | align | flags | role |
| --- | --- | --- | --- | --- | --- |
| `.text` | `0x40` | **0** | 4 | `AX` | empty. Not the program. |
| `xdp` | `0x40` | **240** (`0xf0`) | 8 | `AX` | the program |

`.text` and `xdp` share file offset `0x40` because `.text` has size 0. `llvm-objdump -d` on the whole file prints only `xdp`. No other section has the execute flag. `license` and `.maps` are `WA`, not executable.

Entry symbol: `incr`, `FUNC GLOBAL`, value 0, size 240, section index 3 (`xdp`). One function. The only entry is slot 0. BTF.ext func_info agrees: section name `xdp`, `insn_off` 0, `type_id` 19, which the BTF walk below names `FUNC incr`.

Other symbols that are not code:

| symbol | type | size | section | bytes |
| --- | --- | --- | --- | --- |
| `LICENSE` | OBJECT GLOBAL | 4 | `license` (`PROGBITS` `WA`) | `47 50 4c 00` (`GPL`) |
| `workload` | OBJECT GLOBAL | 32 | `.maps` (`PROGBITS` `WA`, 32 bytes) | 32 zero bytes |
| `xdp` | SECTION | 0 | `xdp` | the section symbol, not an instruction operand |

No `.xpost.meta`, `.xpost.image`, or `.xpost.mem` (those names are absent from the file bytes).

## Relocations, CO-RE, maps

There is **no** `.rel.xdp` and **no** relocation whose section is the instruction bytes.

`llvm-readelf -r` / `llvm-objdump -r` relocations:

- `.rel.debug_info` (5), `.rel.debug_str_offsets` (51), `.rel.debug_line` (5 of the 6): `R_BPF_64_ABS32` to debug section symbols
- `.rel.debug_addr` (6), `.rel.debug_frame` (1 of 2), `.rel.debug_line` (1): `R_BPF_64_ABS64` to the section symbol `xdp`, to `LICENSE`, or to `workload` (debug_addr offsets `0x28` and `0x30`)
- `.rel.debug_frame` offset `0x14`: `R_BPF_64_ABS32` to `.debug_frame`
- `.rel.BTF` (2): `R_BPF_64_NODYLD32`
- `.rel.BTF.ext` (29): `R_BPF_64_NODYLD32` to the section symbol `xdp`

Those are raw section-symbol or object-symbol references inside DWARF/BTF. They are not instruction operands, not XPOST relocations, and not map-index references.

`.rel.BTF` in particular patches DATASEC variable **offset** fields, not code:

| section offset | symbol | what the bytes are |
| --- | --- | --- |
| `0x250` | `workload` | offset field of the `.maps` DATASEC `btf_var_secinfo` (type id 23). Addend in the file is 0. Size field next to it is 32. |
| `0x268` | `LICENSE` | offset field of the `license` DATASEC `btf_var_secinfo` (type id 24). Addend 0. Size field is 4. |

That is a raw object reference inside BTF metadata. It is not an `R_BPF_64_64` map-fd relocation, not an `lddw` with `src = R1` (`PSEUDO_MAP_FD`) or `src = R5` (`PSEUDO_MAP_IDX`), and not an instruction immediate.

`.rel.BTF.ext`'s 29 relocs sit on the `insn_off` field of each func/line/core record (1 + 26 + 2), all against section symbol `xdp` (value 0). The addends are the byte offsets already stored in those records. They do not patch `xdp` instruction bytes.

`llvm-objdump -d -r --section=xdp` prints two lines marked `CO-RE <byte_off>`. That text comes from `.BTF.ext`, not from an ELF relocation on `xdp`. Parsed `.BTF.ext` (file offset `0xda0`, size `0x20c`): magic `0xeb9f`, version 1, `hdr_len` 32, `func_info_len` 20, `line_info_len` 428, `core_relo_off` 448, `core_relo_len` 44. Core-relo blob: `rec_size` 16, one section named `xdp`, `num_info` 2. Kind is the integer 0. Objdump labels it `byte_off`. The enum that names kind 0 was not read in this repo, so it is not given another name here.

| insn byte off | slot | type id | access | kind | objdump | offset already in the slot |
| --- | --- | --- | --- | --- | --- | --- |
| `0x0008` | 1 | 17 | `0:1` | 0 | `struct xdp_md::data_end (0:1)` | `+4` |
| `0x0010` | 2 | 17 | `0:0` | 0 | `struct xdp_md::data (0:0)` | `+0` |

`bpf.toml` `[CORE]` lists the same two rows. BTF type id 17 is `STRUCT xdp_md`, size 24, `kflag` 0, six members, offsets stored in **bits**:

| member | type | bit offset | byte offset |
| --- | --- | --- | --- |
| `data` | 12 (`typedef __u32` → `unsigned int`, 32 bits, encoding 0) | 0 | 0 |
| `data_end` | 12 | 32 | 4 |
| `data_meta` | 12 | 64 | 8 |
| `ingress_ifindex` | 12 | 96 | 12 |
| `rx_queue_index` | 12 | 128 | 16 |
| `egress_ifindex` | 12 | 160 | 20 |

The encoded load offsets (`+4`, `+0`) already match that layout. A loader may patch the offset field later. As stored in this object they are raw encoded offsets, not relocations. No other instruction has a CO-RE record. The byte loads and stores at `r1+8..+11` are plain `MEM` operations, not CO-RE.

No LDDW. Opcode byte `0x18` does not occur. The immediate byte `0x18` does occur, twice, and it is the shift amount 24, not a second slot:

- slot 16: `64 03 00 00 18 00 00 00` → `w3 <<= 0x18` (opcode `0x64`)
- slot 20: `74 03 00 00 18 00 00 00` → `w3 >>= 0x18` (opcode `0x74`)

`decode_lddw_insn` (`ebpfDecoder.v` lines 235–246) is therefore unused. There is no `PSEUDO_MAP_IDX`, `PSEUDO_MAP_FD`, `PSEUDO_MAP_VALUE`, or `PSEUDO_FUNC` reference. 240 bytes / 8 = 30 slots = 30 instructions. No slot is a second half of a wide instruction.

The `.maps` symbol is still real ELF data, and it is unused by the instruction stream:

- BTF `VAR workload` (type id 15) points at type id 14, an anonymous 32-byte struct of four members (`type`, `max_entries`, `key`, `value` in the string table). BTF `STRUCT exec_val` (type id 11) is eight `__u32` fields `w0`..`w7`.
- `bpf.toml` `[maps.workload]` says `BPF_MAP_TYPE_HASH`, `max_entries` 2, key 1 byte, value 32 bytes, `aot_addr = 0x4038026c`. That address is toml metadata. It is not an immediate in `xdp`.
- The C comment says the host copies map key 0 into the context and copies the context back to key 1. No instruction here calls a helper or touches the map. Changing the 32 zero bytes in `.maps` changes no opcode.

## Real disassembly

`llvm-objdump -d -r --section=xdp` (raw bytes included). `<L0>` is slot 29.

```
0000000000000000 <incr>:
       0:	b4 00 00 00 00 00 00 00	w0 = 0x0
       1:	61 12 04 00 00 00 00 00	w2 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)
       2:	61 11 00 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [17] struct xdp_md::data (0:0)
       3:	bf 13 00 00 00 00 00 00	r3 = r1
       4:	07 03 00 00 08 00 00 00	r3 += 0x8
       5:	2d 23 17 00 00 00 00 00	if r3 > r2 goto +0x17 <L0>
       6:	1c 32 00 00 00 00 00 00	w2 -= w3
       7:	a6 02 15 00 04 00 00 00	if w2 < 0x4 goto +0x15 <L0>
       8:	71 12 09 00 00 00 00 00	w2 = *(u8 *)(r1 + 0x9)
       9:	64 02 00 00 08 00 00 00	w2 <<= 0x8
      10:	71 13 08 00 00 00 00 00	w3 = *(u8 *)(r1 + 0x8)
      11:	4c 32 00 00 00 00 00 00	w2 |= w3
      12:	71 13 0a 00 00 00 00 00	w3 = *(u8 *)(r1 + 0xa)
      13:	64 03 00 00 10 00 00 00	w3 <<= 0x10
      14:	4c 32 00 00 00 00 00 00	w2 |= w3
      15:	71 13 0b 00 00 00 00 00	w3 = *(u8 *)(r1 + 0xb)
      16:	64 03 00 00 18 00 00 00	w3 <<= 0x18
      17:	4c 32 00 00 00 00 00 00	w2 |= w3
      18:	04 02 00 00 01 00 00 00	w2 += 0x1
      19:	bc 23 00 00 00 00 00 00	w3 = w2
      20:	74 03 00 00 18 00 00 00	w3 >>= 0x18
      21:	73 31 0b 00 00 00 00 00	*(u8 *)(r1 + 0xb) = w3
      22:	bc 23 00 00 00 00 00 00	w3 = w2
      23:	74 03 00 00 10 00 00 00	w3 >>= 0x10
      24:	73 31 0a 00 00 00 00 00	*(u8 *)(r1 + 0xa) = w3
      25:	73 21 08 00 00 00 00 00	*(u8 *)(r1 + 0x8) = w2
      26:	74 02 00 00 08 00 00 00	w2 >>= 0x8
      27:	73 21 09 00 00 00 00 00	*(u8 *)(r1 + 0x9) = w2
      28:	b4 00 00 00 02 00 00 00	w0 = 0x2
      29:	95 00 00 00 00 00 00 00	exit
```

Jump slots are 5 and 7 only. Both are forward. Offset is from the next slot (`jump_target` in `ebpf_decode.cpp` line 31, and `exec_jmpcmp` which writes `PC + off` and then `nextinstr` adds one):

| slot | opcode | off | target |
| --- | --- | --- | --- |
| 5 | `0x2d` JGT64 reg | +23 (`0x17`) | 5+1+23 = **29** |
| 7 | `0xa6` JLT32 imm | +21 (`0x15`) | 7+1+21 = **29** |

No back edge. Nothing falls off the end: slot 29 is `exit`.

## Instruction list

Classes present in opcode byte `& 7`: LDX `1`, STX `3`, ALU `4`, JMP `5`, JMP32 `6`, ALU64 `7`. No class LD `0`, so no LDDW and no ABS/IND. No `0x85` CALL, no `0xd4`/`0xdc` END, no atomic mode.

Rocq column is `decode_insn` (`ebpfDecoder.v`), which does accept these memory opcodes. C++ column is `decode_ebpf`, which does not.

| slot | op | dst | src | off | imm | Rocq (`decode_insn`) | C++ `decode_ebpf` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | `0xb4` | r0 | r0 | 0 | 0 | `Palu MOV W32 r0 (imm 0)` | `alu32 mov r0, 0` |
| 1 | `0x61` | r2 | r1 | 4 | 0 | `Pload Word r2 r1 +4` | **reject**, class LDX |
| 2 | `0x61` | r1 | r1 | 0 | 0 | `Pload Word r1 r1 +0` | **reject**, class LDX |
| 3 | `0xbf` | r3 | r1 | 0 | 0 | `Palu MOV W64 r3 r1` | `alu64 mov r3, r1` |
| 4 | `0x07` | r3 | r0 | 0 | 8 | `Palu ADD W64 r3 (imm 8)` | `alu64 add r3, 8` |
| 5 | `0x2d` | r3 | r2 | 23 | 0 | `Pjmpcmp (GT Unsigned) W64 r3 r2 +23` | `jmp jgt r3, r2, 23` |
| 6 | `0x1c` | r2 | r3 | 0 | 0 | `Palu SUB W32 r2 r3` | `alu32 sub r2, r3` |
| 7 | `0xa6` | r2 | r0 | 21 | 4 | `Pjmpcmp (LT Unsigned) W32 r2 (imm 4) +21` | `jmp32 jlt r2, 4, 21` |
| 8 | `0x71` | r2 | r1 | 9 | 0 | `Pload Byte r2 r1 +9` | **reject**, class LDX |
| 9 | `0x64` | r2 | r0 | 0 | 8 | `Palu LSH W32 r2 (imm 8)` | `alu32 lsh r2, 8` |
| 10 | `0x71` | r3 | r1 | 8 | 0 | `Pload Byte r3 r1 +8` | **reject**, class LDX |
| 11 | `0x4c` | r2 | r3 | 0 | 0 | `Palu OR W32 r2 r3` | `alu32 or r2, r3` |
| 12 | `0x71` | r3 | r1 | 10 | 0 | `Pload Byte r3 r1 +10` | **reject**, class LDX |
| 13 | `0x64` | r3 | r0 | 0 | 16 | `Palu LSH W32 r3 (imm 16)` | `alu32 lsh r3, 16` |
| 14 | `0x4c` | r2 | r3 | 0 | 0 | `Palu OR W32 r2 r3` | `alu32 or r2, r3` |
| 15 | `0x71` | r3 | r1 | 11 | 0 | `Pload Byte r3 r1 +11` | **reject**, class LDX |
| 16 | `0x64` | r3 | r0 | 0 | 24 | `Palu LSH W32 r3 (imm 24)` | `alu32 lsh r3, 24` |
| 17 | `0x4c` | r2 | r3 | 0 | 0 | `Palu OR W32 r2 r3` | `alu32 or r2, r3` |
| 18 | `0x04` | r2 | r0 | 0 | 1 | `Palu ADD W32 r2 (imm 1)` | `alu32 add r2, 1` |
| 19 | `0xbc` | r3 | r2 | 0 | 0 | `Palu MOV W32 r3 r2` | `alu32 mov r3, r2` |
| 20 | `0x74` | r3 | r0 | 0 | 24 | `Palu RSH W32 r3 (imm 24)` | `alu32 rsh r3, 24` |
| 21 | `0x73` | r1 | r3 | 11 | 0 | `Pstore Byte r1 (reg r3) +11` | **reject**, class STX |
| 22 | `0xbc` | r3 | r2 | 0 | 0 | `Palu MOV W32 r3 r2` | `alu32 mov r3, r2` |
| 23 | `0x74` | r3 | r0 | 0 | 16 | `Palu RSH W32 r3 (imm 16)` | `alu32 rsh r3, 16` |
| 24 | `0x73` | r1 | r3 | 10 | 0 | `Pstore Byte r1 (reg r3) +10` | **reject**, class STX |
| 25 | `0x73` | r1 | r2 | 8 | 0 | `Pstore Byte r1 (reg r2) +8` | **reject**, class STX |
| 26 | `0x74` | r2 | r0 | 0 | 8 | `Palu RSH W32 r2 (imm 8)` | `alu32 rsh r2, 8` |
| 27 | `0x73` | r1 | r2 | 9 | 0 | `Pstore Byte r1 (reg r2) +9` | **reject**, class STX |
| 28 | `0xb4` | r0 | r0 | 0 | 2 | `Palu MOV W32 r0 (imm 2)` | `alu32 mov r0, 2` |
| 29 | `0x95` | r0 | r0 | 0 | 0 | `Pret` | `jmp exit` |

`decode_ebpf` fails on slot 1, the first instruction that is not ALU or JMP. The later ALU/JMP rows are what that decoder would return if it were given those slots alone. It never returns them for this object, because it throws first. `ebpf_test.cpp` requires opcode `0x61` to throw rather than act as a nop.

What the bytes do, as a straight reading of that list (the C source agrees; the object does not contain the dead `param = load_u32(data+4)` from `incr.c` lines 45):

1. Slot 0 writes `w0 = 0` before any exit. Both jump targets are the exit, so a failing check returns 0 only because this write happened.
2. Slot 1 reads 4 bytes at `r1+4` into `w2`. Slot 2 reads 4 bytes at `r1+0` into `w1`, which **replaces** the entry value of `r1`. Order matters: `data_end` is read before `data` overwrites `r1`.
3. Slot 3 copies that new `r1` into `r3` at full width. Slot 4 adds 8 at full width.
4. Slot 5 exits if `r3 > r2` unsigned, 64-bit (`0x2d` is JMP | JGT | X, not a signed compare).
5. Slot 6 subtracts at 32-bit width: low 32 of `r2` minus low 32 of `r3`, result zero-extended. Slot 7 exits if that 32-bit result `< 4` unsigned (`0xa6` is JMP32 | JLT | K).
6. Slots 8–17 rebuild one 32-bit value from four bytes at `r1+8`, `r1+9`, `r1+10`, `r1+11` as `b0 | (b1<<8) | (b2<<16) | (b3<<24)`. The address base is the post-slot-2 `r1`, not `r3`. `r3` is dead after slot 6 and is reused as a scratch byte.
7. Slot 18 adds 1 at 32-bit width.
8. Slots 19–27 write the four bytes back, low byte from the unshifted value, then shifts of 8, 16, and 24. This is not a `BPF_END` swap. The shift immediates 8, 16, 24 are all in `0 .. 31`.
9. Slot 28 writes `w0 = 2`. Slot 29 exits.

`r4`–`r10` are never written. `r10` is never read. There is no stack slot and no call, so caller-save clobber does not occur in this stream.

BTF.ext line records (26 of them, `rec_size` 16) tie the same bytes to `incr.c`: slot 1 is `ctx->data_end`, slot 2 is `ctx->data`, slots 3–5 are `if (data + 8 > end)`, slot 6 is `*avail = (end - *payload)`, slot 7 is `if (avail < 4)`, slots 8–17 are the byte-or expression in `load_u32`, slots 18–27 are `store_u32(payload, x + 1)`. That is source correspondence, not an extra ISA.

## Semantic rules actually read

ALU32 (`eval_alu32`, `ebpfBinSem.v` lines 332–353), for every 32-bit opcode in the table (`MOV`, `SUB`, `LSH`, `OR`, `ADD`, `RSH`): operate on `Val.loword` of the destination and the source, then `Val.longofintu` (zero-extend the 32-bit result into the register). `MOV` of an immediate uses `Vint i` as the source, so slots 0 and 28 write 0 and 2 with the high half cleared. The C++ lifter does the same shape when the bug flag is `None`: `trunc32`, the 32-bit op, `zext64` (`emit_alu`, lines 516–539).

ALU64 (`eval_alu64`, lines 355–375): `MOV` copies the source value with no truncation (slot 3). `ADD` uses `eval_val_int W64`, and an immediate becomes `int64_of_int`, which is `Int64.repr (Int.signed i)` (lines 81 and 108–115). Slot 4's immediate is `+8`, so sign-extend and zero-extend agree. The C++ lifter sign-extends W64 immediates unless `LiftBug::ImmNoSignExtend` (`imm64`, lines 196–200).

Shifts (`eval_shift_mask`, lines 236–243): W32 masks the amount with `Int.repr 31`. The comment above it quotes the kernel interpreter, which does **not** mask an immediate shift, and the verifier, which rejects an immediate outside `0 .. width-1`. These immediates are 8, 16, 24, so the mask does not change them. The C++ lifter also masks unless `LiftBug::ShiftWithoutMask` (`shift`, lines 553–558): `And` with `c32(31)` for a narrow shift, then `Shl` or `LShr` (not `AShr`). `exec_alu`'s same-register shortcut (lines 382–386) forces `SUB`/`XOR` of a register with itself to zero; slot 6 is `r2 -= r3`, so the shortcut does not apply.

Jumps (`eval_cmp64` / `eval_cmp32` / `exec_jmpcmp`, lines 412–498):

- Slot 5 is unsigned 64-bit `GT` of two registers (`Val.cmplu_bool ... Cgt`). Not signed. The immediate is 0 and is not the compared value; the offset is the `off` field.
- Slot 7 is unsigned 32-bit `LT` of `Val.loword r2` against `Vint` of the immediate 4. `eval_cmp_static` does not fold `LT unsigned` against 4 (it only folds 0 and all-ones).
- Taken branch: `PC := offset_ptr(PC, off)`, then `nextinstr` adds `Ptrofs.one`. Not-taken: `nextinstr` only. Same `index+1+off` rule as `jump_target`.
- `bpf_interpreter` only fetches when PC is a `Vptr`. A jump that makes PC `Vundef` (because `offset_ptr` was applied to a non-pointer) becomes `Stuck` on the next fetch. That is a statement about the interpreter's PC, which was read; this object's offsets themselves are the small integers above.

`exit` (`exec_ret`, line 819): on an empty call stack, `Next` with `PC := Vnullptr`, and `R0` is left as it is. The interpreter's next iteration then returns `Stuck` because PC is not a `Vptr` (`Validation.v` lines 32–42). There is no separate halt outcome in the code that was read. The non-empty-stack arm frees a frame and restores `r6`–`r10`; this program never calls, so that arm is not used. The C++ lifter's exit is `Return` of `regs[0]` (`emit`, lines 496–497), which is a different termination story.

Loads (`exec_load`, lines 575–588): if the base is `Vlong`, add the signed offset and `cast_i2p` through `addr_map`; if the base is `Vptr`, `offset_ptr`. Then `load` uses `Mint32` for `Word` and `Mint8unsigned` for `Byte` (`load`, lines 560–567). `load_value_casting` turns a `Vint` into `Vlong (Int64.repr (Int.unsigned i))` (lines 569–573). A successful word load of `xdp_md.data` / `data_end` is therefore a zero-extended integer, not a `Vptr`. CompCert's `decode_val` for those chunks was **not** read. `Extraction.v` forces `Archi.big_endian` false for the extracted interpreter; `eval_end` consults that flag, but this object has no END instruction. The packet integer is built by the shifts, not by a word load, so its byte order is in the instruction list even if `decode_val` is endian-dependent.

Stores (`exec_store`, lines 642–646): address is **only** `Val.offset_ptr` of the base. There is no `cast_i2p` on this path. The value is `eval_reg_immw (sizew Byte)`, and `sizew Byte = W32` (`ebpfSyntax.v` lines 110–114), so a `Vlong` source is reduced with `Int.repr (Int64.unsigned i)` and then stored as `Mint8unsigned`. `encode_val` was not read. If the base is `Vlong`, this function returns `Stuck` unless `offset_ptr` of a `Vlong` is a pointer, and that `offset_ptr` definition was not read. The load path's special case for `Vlong` is absent here. That is a concrete gap for the success path: slots 2 and 3 make `r1` the integer result of a word load, and slots 21, 24, 25, 27 store through that `r1`.

`exec_instr` (line 888) dispatches `Pload` to `exec_load` (with `addr_map`) and `Pstore` to `exec_store` (without `addr_map`). The final `| _ => Stuck` arm covers `Pcall` other than `CallInternal`. This object has no call.

## IR mapping against the existing C++ lifter only

`lift_ebpf` is only reachable after `decode_ebpf`. For this object that call throws at slot 1 (`unsupported class in opcode 0x61`). No `IR::Function` is produced. No `.alive` file is emitted here. The mapping below says what the lifter's code does with each opcode **if that opcode were already an `EbAlu` or `EbJmp`**. Memory opcodes have no IR case: `EbInsn::op` cannot represent them (`ebpf.h` lines 38–41).

If the memory slots were deleted and the ALU/JMP slots were lifted alone, `build_blocks` would mark leaders at 0, at each jump target, and at the instruction after each jump. On the real schedule the leaders are slots 0, 6, 8, and 29:

- block A, slots 0–5, conditional edge to slot 29 or slot 6
- block B, slots 6–7, conditional edge to slot 29 or slot 8
- block C, slots 8–28, fall-through edge to slot 29
- block D, slot 29, `exit`

`loop` would be false: both targets are greater than the jump index (`build_blocks`, lines 227–229). `execute_ebpf` would then `topSort` rather than unroll, and it would print memory `none` because `info.loop` is false (lines 71–74), even though this program stores.

Per-opcode IR, bug flag `None`:

| slots | lifter result |
| --- | --- |
| 0, 28 `alu32 mov imm` | `trunc32` of the old dst (ignored by the mov), source is `imm64` **zero-extended** then `trunc32`, then `zext64`. Immediates 0 and 2. |
| 3 `alu64 mov reg` | `bare_mov`: the value pointer is copied. No trunc, no zext. High bits of `r1` survive into `r3`. |
| 4 `alu64 add imm` | `i64` `BinOp::Add` of `r3` and sign-extended 8. |
| 6 `alu32 sub reg` | `trunc32` both, `i32` `BinOp::Sub`, `zext64`. |
| 9, 13, 16 `alu32 lsh imm` | `trunc32`, `And` with `c32(31)`, `i32` `Shl`, `zext64`. |
| 11, 14, 17 `alu32 or` | `trunc32` both, `i32` `BinOp::Or`, `zext64`. |
| 18 `alu32 add imm` | `trunc32`, `i32` `BinOp::Add` of 1, `zext64`. |
| 19, 22 `alu32 mov reg` | `trunc32` of the source, then `zext64`. High half of `r2` is cleared in `r3`. |
| 20, 23, 26 `alu32 rsh imm` | `trunc32`, mask 31, `i32` `LShr` (logical), `zext64`. |
| 5 `jmp jgt` | `ICmp::UGT` on the full `i64` registers, branch true = taken = slot 29. |
| 7 `jmp32 jlt` | `trunc32` of `r2`, `c32(4)`, `ICmp::ULT`, branch true = taken = slot 29. |
| 29 `exit` | `Return` of the `i64` in `r0`. |
| 1, 2, 8, 10, 12, 15 loads; 21, 24, 25, 27 stores | no constructor. Decoder throws. Not an IR `load` or `store`. |

`concrete()` inside the same file would not evaluate this program even after a decoder change. Its `BinOp` switch handles Add, Sub, And, UDiv, SDiv only (lines 879–885); `Or`, `Shl`, and `LShr` take the unsupported path. Its `ICmp` switch handles `EQ` and `UGT` only (lines 918–921); slot 7's `ULT` takes the unsupported path. A `MemInstr` sets `trace.memory = Changed` and then stops unsupported (lines 962–965). `make_alive_trace` also refuses an input register above `r9` and calls `decode_ebpf` on the raw bytes.

`configure_pure_alu` is the runner's memory story today: `does_int_load`, `does_int_store`, `does_ptr_load`, and `does_ptr_store` are set false before symbolic execution. That matches a lifter that cannot name a memory operation. It does not match this object.

## Memory, helper, map, loop

| requirement | this object |
| --- | --- |
| helper call | **no**. No `0x85`, no tail call, no BTF-id call. |
| map operation in the instruction stream | **no**. No LDDW, no map-index pseudo, no helper. |
| map object in the ELF | **yes, unused by code**. `.maps` / `workload`, 32 zero bytes, BTF DATASEC reloc only. `aot_addr` is not an operand. |
| loop | **no**. Two forward jumps, both to slot 29. |
| memory | **yes, the whole point of the function**. Two unsigned word loads from the entry pointer (`r1+0`, `r1+4`), then four unsigned byte loads and four unsigned byte stores through the integer that the second word load wrote into `r1`, at byte offsets 8, 9, 10, 11. |
| stack / r10 | **no**. |
| packet endianness | explicit little-endian shifts and byte stores. Not a word load and not `BPF_END`. |
| CO-RE | two field-offset records, kind integer 0, on slots 1 and 2 only. Offsets in the file already match `xdp_md` in this BTF. |
| XPOST | **no**. |

A later lifter has to keep three addresses apart: the entry value of `r1` (only slots 1 and 2 read it), the integer loaded from offset 0 (this is `r1` from slot 2 onward, and the base of every byte access), and `r3 = that integer + 8` (used only by the compare and the 32-bit subtract). After slot 2, storing through the original context pointer is a different program.

Bounds the instruction list actually implements: exit with `r0 = 0` and no store if `(r1_after_slot2 + 8) > r2` as 64-bit unsigned, or if the low 32 bits of `r2 - (r1_after_slot2 + 8)` are `< 4`. Otherwise add 1 modulo 2^32 to the little-endian u32 at `r1+8` and exit with `r0 = 2`. The first compare does not by itself prove that four bytes at `r1+8` are in range; the second compare is a separate instruction and is not redundant in the object.

## Conversion result

**NOT CONVERTED.**

`decode_ebpf` rejects slot 1. `lift_ebpf` is not run. No Alive2 function and no `.alive` text is produced for `incr`. Calling the missing memory model "unsupported" is not a successful conversion. The ALU and jump rows above are a classification of those opcodes against the lifter that already exists, not a translation of this object.

## Proof coverage

Nothing read proves this object. The Rocq tree has no theorem about `incr`, about these loads, or about these stores. `bpf_interpreter` is an executable interpreter, not a proof. `is_label_correct` is about `Plabel`, which is not in the syntax inductive that was read.

Gaps that a later proof would have to close, each from code that was read:

- The C++ decoder and the Rocq decoder disagree on classes LDX and STX. The C++ tests require the disagreement for opcode `0x61`.
- `exec_load` can turn a `Vlong` into a pointer via `cast_i2p`. `exec_store` cannot. The success path stores through the `Vlong` produced by the word load.
- C++ `Return r0` is not the same state as `exec_ret` setting PC to `Vnullptr` and the interpreter then returning `Stuck`.
- `concrete()` does not implement `Or`, `Shl`, `LShr`, or `ICmp::ULT`, which this program uses.
- `Extraction.v` fixes `Archi.big_endian` to false, but CompCert `decode_val` / `encode_val` were not read, so a proof that the two word loads are host-little-endian is not in the files read. The packet u32 does not need that fact: its byte order is the shifts.

## Counterexample idea

Do not treat a 64-bit add of `0xffffffff` as a distinguishing test by itself. The four byte stores only write the low 8 bits of the unshifted value and of the logical shifts by 8, 16, and 24. Splitting `0x100000000` that way stores the same `00 00 00 00` as a 32-bit wrap. A wrong model shows up if it stores more than those four bytes, or if it uses a different byte order.

Concrete cases, with entry `r1` a pointer to two little-endian u32 fields `data`, `data_end`, and the packet living at the integer `data`:

1. **Swapped compare.** `data = 0x1000`, `data_end = 0x100c`, bytes at `0x1008` are `01 00 00 00`. Slot 5 compares `(data+8) > data_end`. It is false. The program must store `02 00 00 00` and return `r0 = 2`. If the lifter emits `UGT` with the operands reversed, the branch is taken, `r0` stays 0, and the packet stays `01 00 00 00`.
2. **Dropped second check.** `data = 0x1000`, `data_end = 0x100b` (11 bytes). `data+8 = 0x1008` is not greater than `0x100b`, so slot 5 falls through. `avail = 3`, so slot 7 must exit with `r0 = 0` and must not write. The byte at `0x1008` stays whatever it was, and offset 11 (`0x100b`) is not written. Deleting slot 7 stores four bytes starting at `0x1008`, including one byte at `data_end`.
3. **`r1` still the context.** Same in-bounds packet as case 1, context object at `0x2000`, packet byte at `0x1008` equal to `05`. The program must change `0x1008` from `05` to `06` and must leave context bytes at `0x2008`..`0x200b` unchanged. A lifter that keeps the entry pointer in `r1` and applies `+8..+11` to the context does the opposite.
4. **Byte order.** Bytes at the payload `01 02 03 04`. The shifts compute `0x04030201 + 1 = 0x04030202` and store `02 02 03 04`. A big-endian word read of those bytes is `0x01020304 + 1 = 0x01020305`, which stores different bytes under either a big-endian or a little-endian word store (`01 02 03 05` or `05 03 02 01`).
5. **Map is not an input.** Same packet as case 1, but the 32 bytes of `workload` are nonzero. `r0` and the packet result must match case 1. An invented `bpf_map_lookup_elem` or an invented LDDW of `workload` fails this.
6. **Abort clears `r0`.** Entry `r0 = 7`, `data_end = data` (slot 5 taken). Exit `r0` must be 0, not 7. Slot 0 is the only reason.

Case 4 is also the check against "recognise the shift chain and emit one `load i32`". Case 2 is the check against deleting a jump that looks redundant next to slot 5.

ISSUES
