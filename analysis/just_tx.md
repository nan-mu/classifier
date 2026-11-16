# just_tx observation

Observation report for one BPF object, so a later implementer can compile it. This file does not define a shared ISA and it is not a conversion. Conversion result: **NOT CONVERTED**. No `.alive` file was emitted.

## Evidence

Computed sha256 of `/Volumes/SSD/bs/build/just_tx/bpf.o`:

`97d6033cd68d1d56b193dd303ce04a2ffcc1c607402ebb8fc7faa15f41317201`

That matches the hash given with the task. File size 12920 bytes. Notes file `/Volumes/SSD/bs/build/just_tx/bpf.toml` (2186 bytes) was read after the object, not instead of it.

Commands actually run:

- `shasum -a 256 /Volumes/SSD/bs/build/just_tx/bpf.o`
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -a /Volumes/SSD/bs/build/just_tx/bpf.o`
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r --section=xdp1 --section=.text --print-imm-hex /Volumes/SSD/bs/build/just_tx/bpf.o`
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -h` and `-t` on the same object
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -h -S -s /Volumes/SSD/bs/build/just_tx/just_tx.elf` (sibling container only, to separate it from this object)
- A local Python parse of ELF section bytes, the 58 instruction slots, `.relxdp1`, the `maps` `bpf_map_def`, `.BTF`, and `.BTF.ext` core relocations

`just_tx.c` was not read. CompCert `Val.offset_ptr` and `Archi.big_endian` were not read.

## Entries and executable sections

ELF64, `ELFDATA2LSB` (little endian), `ET_REL`, `EM_BPF`, `e_entry = 0`, no program headers. Endianness of the container and of every instruction word is little endian. Multi-byte immediates and offsets below are the little-endian fields of those words.

Executable sections (`SHF_EXECINSTR`, flags `0x6`):

| index | name | offset | size | notes |
| --- | --- | --- | --- | --- |
| 2 | `.text` | `0x40` | **0** | empty. Not the program. Same file offset as `xdp1` only because its size is 0. |
| 3 | `xdp1` | `0x40` | `0x1d0` (464) | the program |

No other section has the execute flag. `llvm-objdump -d` printed only `xdp1`.

Entry symbol: `xdp_prog1`, `GLOBAL FUNC`, section `xdp1`, value 0, size 464. BTF type id 7 `FUNC xdp_prog1` points at func proto id 5: one argument `ctx` of type `ptr` to `xdp_md` (id 2), return `int` (id 6). Because the file is `ET_REL`, `e_entry` is not the entry.

Slot count is 58 (464 / 8). One `LDDW` occupies slots 34 and 35, so a logical instruction count that pairs `LDDW` is 57. Jump displacements are in 8-byte slots, and the second `LDDW` word counts as a slot. `llvm-objdump` numbers the call as 36, not 35.

## Relocations, map, BTF

Program relocation section `.relxdp1` (one `Elf64_Rel`):

| r_offset | r_info type | symbol |
| --- | --- | --- |
| `0x110` (slot 34, the `LDDW`) | `1` (`R_BPF_64_64`) | sym 12 `rxcnt` |

That is a raw object reference: the relocation names the ELF symbol `rxcnt`. It is not an instruction-field map index, and it is not an XPOST relocation.

The `LDDW` word itself is `18 01 00 00 00 00 00 00` plus a second word of zeros. Destination `r1`, **source register field 0**, immediate 0. In `alive2/rocq/upstream/theories/ebpfSyntax.v` the source-register field of `LDDW` selects the pseudo kind: 0 constant, 1 `map_by_fd`, 2 `map_val(map_by_fd)`, 3 BTF id, 4 code address, 5 `map_by_idx`, 6 `map_val(map_by_idx)`. `ebpfDecoder.v` `decode_lddw_insn` maps `R0` to `PSEUDO_Constant` and `R5` to `PSEUDO_MAP_IDX`. This word is the constant 0 until a loader applies `R_BPF_64_64`. Do not treat imm 0 as a map index.

`bpf.o` has no `.xpost.meta` or `.xpost.image` section. The sibling `/Volumes/SSD/bs/build/just_tx/just_tx.elf` is a different file: ELF32, little endian, `EM_RISCV`, sections `.xpost.meta` (`SHT_LOUSER+1`) and `.xpost.image`. `bpf.toml` `aot_addr = 0x403802e8` is a note in that toml, not a relocation in `bpf.o`.

`maps` section, 20 bytes, symbol `rxcnt` size 20, not executable. Bytes `02 00 00 00 04 00 00 00 08 00 00 00 00 01 00 00 00 00 00 00`, read as five little-endian `u32`s:

| field | value |
| --- | --- |
| type | 2 (`BPF_MAP_TYPE_ARRAY` in the usual uapi numbering; the C++ lifter does not name it) |
| key_size | 4 |
| value_size | 8 |
| max_entries | 256 |
| map_flags | 0 |

BTF agrees: type id 23 `struct bpf_map_def`, id 24 `VAR rxcnt` linkage 1, id 29 `DATASEC maps` places that var at offset 0 size 20. `license` is the four bytes `GPL\0` (symbol `LICENSE`).

`.BTF.ext` core-reloc subsection: record size 16, section name `xdp1`, five records, all kind 0 (`byte_off`). These are CO-RE records, not ELF relocations. The instruction offset field already holds the local BTF byte offset; nothing in the C++ decoder applies CO-RE.

| insn byte | slot | type id | access | local layout checked in `.BTF` |
| --- | --- | --- | --- | --- |
| `0x008` | 1 | 2 `xdp_md` | `0:1` | `data_end` at bit 32, encoded offset 4 |
| `0x010` | 2 | 2 `xdp_md` | `0:0` | `data` at bit 0, encoded offset 0 |
| `0x030` | 6 | 8 `ethhdr` | `0:2` | `h_proto` at bit 96, encoded offset 12 |
| `0x070` | 14 | 15 `vlan_hdr` | `0:1` | `h_vlan_encapsulated_proto` at bit 16, encoded offset 2 |
| `0x0b8` | 23 | 16 `iphdr` | `0:7` | member `protocol` (`__u8`); encoded offset 9 |

`xdp_md` members in this BTF: `data`, `data_end`, `data_meta`, `ingress_ifindex`, `rx_queue_index`, `egress_ifindex`, each `__u32`. `iphdr` bitfields: `ihl` is 4 bits at bit 0, `version` is 4 bits at bit 4 (BTF member word `0x04000000` / `0x04000004`). The program never loads `ihl` or `version`. The IPv6 next-header load (slot 30, offset 6) and every Ethernet address halfword have **no** CO-RE record. They are raw offsets.

Other relocation sections (`.rel.debug_*`, `.rel.BTF`, `.rel.BTF.ext`) do not relocate `xdp1`. `.rel.BTF` has `R_BPF_64_NODYLD32` against `LICENSE` and `rxcnt`. That is BTF, not the program image.

## Real disassembly

`llvm-objdump -d -r --section=xdp1 --print-imm-hex`. The `.text` request produced no instructions.

```
0000000000000000 <xdp_prog1>:
       0:	b4 00 00 00 01 00 00 00	w0 = 0x1
       1:	61 12 04 00 00 00 00 00	w2 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [2] struct xdp_md::data_end (0:1)
       2:	61 16 00 00 00 00 00 00	w6 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [2] struct xdp_md::data (0:0)
       3:	bf 61 00 00 00 00 00 00	r1 = r6
       4:	07 01 00 00 0e 00 00 00	r1 += 0xe
       5:	2d 21 33 00 00 00 00 00	if r1 > r2 goto +0x33 <L5>
       6:	69 64 0c 00 00 00 00 00	w4 = *(u16 *)(r6 + 0xc)
		0000000000000030:  CO-RE <byte_off> [8] struct ethhdr::h_proto (0:2)
       7:	16 04 02 00 81 00 00 00	if w4 == 0x81 goto +0x2 <L0>
       8:	b7 03 00 00 0e 00 00 00	r3 = 0xe
       9:	56 04 05 00 88 a8 00 00	if w4 != 0xa888 goto +0x5 <L1>
<L0>:
      10:	bf 63 00 00 00 00 00 00	r3 = r6
      11:	07 03 00 00 12 00 00 00	r3 += 0x12
      12:	2d 23 2c 00 00 00 00 00	if r3 > r2 goto +0x2c <L5>
      13:	b7 03 00 00 12 00 00 00	r3 = 0x12
      14:	69 14 02 00 00 00 00 00	w4 = *(u16 *)(r1 + 0x2)
		0000000000000070:  CO-RE <byte_off> [15] struct vlan_hdr::h_vlan_encapsulated_proto (0:1)
<L1>:
      15:	b4 01 00 00 00 00 00 00	w1 = 0x0
      16:	16 04 08 00 86 dd 00 00	if w4 == 0xdd86 goto +0x8 <L2>
      17:	56 04 0d 00 08 00 00 00	if w4 != 0x8 goto +0xd <L3>
      18:	bf 64 00 00 00 00 00 00	r4 = r6
      19:	0f 34 00 00 00 00 00 00	r4 += r3
      20:	bf 43 00 00 00 00 00 00	r3 = r4
      21:	07 03 00 00 14 00 00 00	r3 += 0x14
      22:	2d 23 08 00 00 00 00 00	if r3 > r2 goto +0x8 <L3>
      23:	71 41 09 00 00 00 00 00	w1 = *(u8 *)(r4 + 0x9)
		00000000000000b8:  CO-RE <byte_off> [16] struct iphdr::protocol (0:7)
      24:	05 00 06 00 00 00 00 00	goto +0x6 <L3>
<L2>:
      25:	bf 64 00 00 00 00 00 00	r4 = r6
      26:	0f 34 00 00 00 00 00 00	r4 += r3
      27:	bf 43 00 00 00 00 00 00	r3 = r4
      28:	07 03 00 00 28 00 00 00	r3 += 0x28
      29:	2d 23 01 00 00 00 00 00	if r3 > r2 goto +0x1 <L3>
      30:	71 41 06 00 00 00 00 00	w1 = *(u8 *)(r4 + 0x6)
<L3>:
      31:	63 1a fc ff 00 00 00 00	*(u32 *)(r10 - 0x4) = w1
      32:	bf a2 00 00 00 00 00 00	r2 = r10
      33:	07 02 00 00 fc ff ff ff	r2 += -0x4
      34:	18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00	r1 = 0x0 ll
		0000000000000110:  R_BPF_64_64	rxcnt
      36:	85 00 00 00 01 00 00 00	call 0x1
      37:	15 00 03 00 00 00 00 00	if r0 == 0x0 goto +0x3 <L4>
      38:	79 01 00 00 00 00 00 00	r1 = *(u64 *)(r0 + 0x0)
      39:	07 01 00 00 01 00 00 00	r1 += 0x1
      40:	7b 10 00 00 00 00 00 00	*(u64 *)(r0 + 0x0) = r1
<L4>:
      41:	61 a1 fc ff 00 00 00 00	w1 = *(u32 *)(r10 - 0x4)
      42:	b4 00 00 00 01 00 00 00	w0 = 0x1
      43:	56 01 0d 00 11 00 00 00	if w1 != 0x11 goto +0xd <L5>
      44:	69 61 00 00 00 00 00 00	w1 = *(u16 *)(r6 + 0x0)
      45:	69 62 06 00 00 00 00 00	w2 = *(u16 *)(r6 + 0x6)
      46:	6b 26 00 00 00 00 00 00	*(u16 *)(r6 + 0x0) = w2
      47:	69 62 08 00 00 00 00 00	w2 = *(u16 *)(r6 + 0x8)
      48:	69 63 02 00 00 00 00 00	w3 = *(u16 *)(r6 + 0x2)
      49:	6b 36 08 00 00 00 00 00	*(u16 *)(r6 + 0x8) = w3
      50:	6b 26 02 00 00 00 00 00	*(u16 *)(r6 + 0x2) = w2
      51:	69 62 0a 00 00 00 00 00	w2 = *(u16 *)(r6 + 0xa)
      52:	69 63 04 00 00 00 00 00	w3 = *(u16 *)(r6 + 0x4)
      53:	6b 36 0a 00 00 00 00 00	*(u16 *)(r6 + 0xa) = w3
      54:	6b 16 06 00 00 00 00 00	*(u16 *)(r6 + 0x6) = w1
      55:	6b 26 04 00 00 00 00 00	*(u16 *)(r6 + 0x4) = w2
      56:	b4 00 00 00 03 00 00 00	w0 = 0x3
<L5>:
      57:	95 00 00 00 00 00 00 00	exit
```

Header immediates are the little-endian register values of big-endian header constants, already encoded in the words: `0x81` is `0x8100` swapped as a `u16`, `0xa888` is `0x88a8`, `0xdd86` is `0x86dd`, `0x8` is `0x0800`. `0x11` is a single byte (protocol), not a swapped multi-byte field. Return immediates are the numbers 1 and 3. The C++ lifter does not name them `XDP_DROP` or `XDP_TX`; it would only return `r0` if it could decode the function.

## Instruction list

`decode_ebpf` (`alive2/src/ebpf_decode.cpp`) walks one 8-byte slot at a time. It handles only classes `ALU` (`0x4`) and `ALU64` (`0x7`) and `JMP` (`0x5`) / `JMP32` (`0x6`). Every other class hits line 164–167, `unsupported class in opcode`. It does not pair `LDDW`. On this object it throws at **slot 1** and never builds an `EbInsn` vector. The rows below still classify every slot against that function and against `decode_insn` / `decode_lddw_insn` / `find_instr` in `alive2/rocq/upstream/theories/ebpfDecoder.v`, which were read in full.

Jump target formula used by the C++ decoder for a jump it accepts: `jump_target` = index + 1 + offset (`ebpf.h` / `ebpf_decode.cpp` `jump_target`). All of these offsets are forward. There is no back edge.

| slot | bytes (opcode dst/src off imm) | class | C++ `decode_ebpf` if this slot were reached | Rocq decoder | jump |
| --- | --- | --- | --- | --- | --- |
| 0 | `b4 r0, imm 1` | ALU MOV K | `EbAlu::Mov` W32 imm. Accepted. | `Palu MOV W32` | |
| 1 | `61 r2, r1, +4` | LDX W | **reject**, class `0x1`, opcode `0x61` | `Pload Word` | |
| 2 | `61 r6, r1, +0` | LDX W | reject, class `0x1` | `Pload Word` | |
| 3 | `bf r1, r6` | ALU64 MOV X | `EbAlu::Mov` W64 reg | `Palu MOV W64` | |
| 4 | `07 r1, +14` | ALU64 ADD K | `EbAlu::Add` W64 imm | `Palu ADD W64` | |
| 5 | `2d r1, r2, +51` | JMP JGT X | `EbJmp::Jgt` W64 | `Pjmpcmp (GT Unsigned) W64` | 57, else 6 |
| 6 | `69 r4, r6, +12` | LDX H | reject, class `0x1` | `Pload HalfWord` | |
| 7 | `16 r4, imm 0x81, +2` | JMP32 JEQ K | `EbJmp::Jeq` W32 | `Pjmpcmp EQ W32` | 10, else 8 |
| 8 | `b7 r3, imm 14` | ALU64 MOV K | `EbAlu::Mov` W64 imm | `Palu MOV W64` | |
| 9 | `56 r4, imm 0xa888, +5` | JMP32 JNE K | `EbJmp::Jne` W32 | `Pjmpcmp NE W32` | 15, else 10 |
| 10 | `bf r3, r6` | ALU64 MOV X | `EbAlu::Mov` W64 reg | `Palu MOV W64` | |
| 11 | `07 r3, +0x12` | ALU64 ADD K | `EbAlu::Add` W64 imm | `Palu ADD W64` | |
| 12 | `2d r3, r2, +44` | JMP JGT X | `EbJmp::Jgt` W64 | `Pjmpcmp (GT Unsigned) W64` | 57, else 13 |
| 13 | `b7 r3, imm 0x12` | ALU64 MOV K | `EbAlu::Mov` W64 imm | `Palu MOV W64` | |
| 14 | `69 r4, r1, +2` | LDX H | reject, class `0x1` | `Pload HalfWord` | |
| 15 | `b4 r1, imm 0` | ALU MOV K | `EbAlu::Mov` W32 imm | `Palu MOV W32` | |
| 16 | `16 r4, imm 0xdd86, +8` | JMP32 JEQ K | `EbJmp::Jeq` W32 | `Pjmpcmp EQ W32` | 25, else 17 |
| 17 | `56 r4, imm 8, +13` | JMP32 JNE K | `EbJmp::Jne` W32 | `Pjmpcmp NE W32` | 31, else 18 |
| 18 | `bf r4, r6` | ALU64 MOV X | `EbAlu::Mov` W64 reg | `Palu MOV W64` | |
| 19 | `0f r4, r3` | ALU64 ADD X | `EbAlu::Add` W64 reg | `Palu ADD W64` | |
| 20 | `bf r3, r4` | ALU64 MOV X | `EbAlu::Mov` W64 reg | `Palu MOV W64` | |
| 21 | `07 r3, +0x14` | ALU64 ADD K | `EbAlu::Add` W64 imm | `Palu ADD W64` | |
| 22 | `2d r3, r2, +8` | JMP JGT X | `EbJmp::Jgt` W64 | `Pjmpcmp (GT Unsigned) W64` | 31, else 23 |
| 23 | `71 r1, r4, +9` | LDX B | reject, class `0x1` | `Pload Byte` | |
| 24 | `05 +6` | JMP JA | `EbJmp::Ja` W64 off 6, imm 0 | `Pjmp64` | 31 |
| 25 | `bf r4, r6` | ALU64 MOV X | `EbAlu::Mov` W64 reg | `Palu MOV W64` | |
| 26 | `0f r4, r3` | ALU64 ADD X | `EbAlu::Add` W64 reg | `Palu ADD W64` | |
| 27 | `bf r3, r4` | ALU64 MOV X | `EbAlu::Mov` W64 reg | `Palu MOV W64` | |
| 28 | `07 r3, +0x28` | ALU64 ADD K | `EbAlu::Add` W64 imm | `Palu ADD W64` | |
| 29 | `2d r3, r2, +1` | JMP JGT X | `EbJmp::Jgt` W64 | `Pjmpcmp (GT Unsigned) W64` | 31, else 30 |
| 30 | `71 r1, r4, +6` | LDX B | reject, class `0x1` | `Pload Byte` | |
| 31 | `63 *(u32*)(r10-4) = r1` | STX W | reject, class `0x3` | `Pstore Word` reg, off -4 | |
| 32 | `bf r2, r10` | ALU64 MOV X | `EbAlu::Mov` W64 reg. `r10` is a legal register (`check_reg` allows 0..10). | `Palu MOV W64` | |
| 33 | `07 r2, imm -4` | ALU64 ADD K | `EbAlu::Add` W64 imm `-4` | `Palu ADD W64` | |
| 34 | `18 r1, src 0, imm 0` | LD DW IMM | reject, class `0x0`, opcode `0x18`. Not paired. | `find_instr` takes the next slot; `decode_lddw_insn` `R0` → `Plddw PSEUDO_Constant` lo 0 hi 0 | |
| 35 | `00` eight zero bytes | LD (second word) | if decoded alone: reject, class `0x0`, opcode `0x00`. Not an independent Rocq instruction. | consumed as `LDDW` high immediate; reserved low 32 bits are 0, so the pair is accepted | |
| 36 | `85 imm 1, src field 0, off 0` | JMP CALL | class JMP, code nibble `0x8`, not in the jump switch. **`unsupported jump opcode`** (line 157–158). | `Pcall CallByStaticID` imm 1 (`src_reg` `R0`, offset 0) | |
| 37 | `15 r0, imm 0, +3` | JMP JEQ K | `EbJmp::Jeq` W64 | `Pjmpcmp EQ W64` | 41, else 38 |
| 38 | `79 r1, r0, +0` | LDX DW | reject, class `0x1` | `Pload DBWord` | |
| 39 | `07 r1, +1` | ALU64 ADD K | `EbAlu::Add` W64 imm | `Palu ADD W64` | |
| 40 | `7b *(u64*)(r0+0) = r1` | STX DW | reject, class `0x3` | `Pstore DBWord` | |
| 41 | `61 r1, r10, -4` | LDX W | reject, class `0x1` | `Pload Word` | |
| 42 | `b4 r0, imm 1` | ALU MOV K | `EbAlu::Mov` W32 imm | `Palu MOV W32` | |
| 43 | `56 r1, imm 0x11, +13` | JMP32 JNE K | `EbJmp::Jne` W32 | `Pjmpcmp NE W32` | 57, else 44 |
| 44 | `69 r1, r6, +0` | LDX H | reject, class `0x1` | `Pload HalfWord` | |
| 45 | `69 r2, r6, +6` | LDX H | reject, class `0x1` | `Pload HalfWord` | |
| 46 | `6b *(u16*)(r6+0) = r2` | STX H | reject, class `0x3` | `Pstore HalfWord` | |
| 47 | `69 r2, r6, +8` | LDX H | reject, class `0x1` | `Pload HalfWord` | |
| 48 | `69 r3, r6, +2` | LDX H | reject, class `0x1` | `Pload HalfWord` | |
| 49 | `6b *(u16*)(r6+8) = r3` | STX H | reject, class `0x3` | `Pstore HalfWord` | |
| 50 | `6b *(u16*)(r6+2) = r2` | STX H | reject, class `0x3` | `Pstore HalfWord` | |
| 51 | `69 r2, r6, +10` | LDX H | reject, class `0x1` | `Pload HalfWord` | |
| 52 | `69 r3, r6, +4` | LDX H | reject, class `0x1` | `Pload HalfWord` | |
| 53 | `6b *(u16*)(r6+10) = r3` | STX H | reject, class `0x3` | `Pstore HalfWord` | |
| 54 | `6b *(u16*)(r6+6) = r1` | STX H | reject, class `0x3` | `Pstore HalfWord` | |
| 55 | `6b *(u16*)(r6+4) = r2` | STX H | reject, class `0x3` | `Pstore HalfWord` | |
| 56 | `b4 r0, imm 3` | ALU MOV K | `EbAlu::Mov` W32 imm | `Palu MOV W32` | |
| 57 | `95` | JMP EXIT | `EbJmp::Exit` if dst/src/off/imm are 0. They are. | `Pret` | exit |

What the bytes do, as a control-flow sketch for the implementer, not as a lifter result:

- `r1` starts as the context pointer. Slot 1 loads `data_end` into `w2`. Slot 2 loads `data` into `w6` as a 32-bit value.
- Slot 5 exits unless `data+14` is not strictly above `data_end` (unsigned `>`).
- Slot 6 loads the Ethernet type. `0x81` or `0xa888` takes the VLAN path: require `data+0x12` in range, set the L3 cursor to 18, reload the inner type from `(data+14)+2`. Otherwise the L3 cursor stays 14.
- Slot 15 clears `w1`. IPv4 (`0x8`) loads one byte at L3+9 if L3+20 is in range. IPv6 (`0xdd86`) loads one byte at L3+6 if L3+0x28 is in range. Anything else leaves `w1` as 0.
- Slot 31 spills that `u32` to `*(u32*)(r10-4)`. Slot 36 is `call 1` with `r1` = the relocated `rxcnt` word and `r2` = `r10-4`. If `r0` is non-zero, slots 38–40 increment the `u64` at `*(u64*)(r0)`.
- Slot 41 reloads the spilled `u32`. Slot 42 sets `w0 = 1`. If the low 32 bits are not `0x11`, slot 43 exits with that 1. Otherwise six halfword loads/stores rotate `h_dest` and `h_source`, slot 56 sets `w0 = 3`, and slot 57 exits.

Early exits at slots 5 and 12 do not touch the stack, the map, or the packet body. They return the `w0 = 1` from slot 0.

## Semantic rules actually read

Read in full:

- `alive2/src/ebpf_decode.cpp`
- `alive2/src/ebpf.h`
- `alive2/src/ebpf_lift.h`
- `alive2/src/ebpf_lift.cpp`
- `alive2/rocq/README.md`
- `alive2/rocq/upstream/theories/ebpfSyntax.v`
- `alive2/rocq/upstream/theories/ebpfDecoder.v`
- `alive2/rocq/upstream/theories/ebpfState.v` (the file ends at the `addr_region` record)

Read in `alive2/rocq/upstream/theories/ebpfBinSem.v` (not the whole 1292 lines): the `ebpf_call_function` variable (lines 60–61), `nextinstr` (66–67), `int64_of_int` and `eval_val_int` / `eval_reg_immw` (81–116), `eval_alu32` / `eval_alu64` / `exec_alu` (332–390), the jump block through `exec_jmpcmp` (392–498), `cast_i2p`, `load` / `exec_load`, `store` / `exec_store`, `exec_lddw` (512–659), `undef_caller_save_regs` (661–667), `exec_call_internal` and `exec_ret` (751–839), `exec_instr` (888–905), `step` including `exec_step_external` (969–991), `initial_lst_state` (993–1007). Also `alive2/src/ebpf_project.cpp` `supported_insn` (238–249), the per-instruction rule tags (494–557), and the pointer-use block (922–925). Also the coverage sentence in `alive2/src/ebpf_exhibit.cpp` (246–247).

Not read, so not used as rules: `CMemoryModel.v`, `Validation.v`, `SCLanguage.v`, `Nondeterminism.v`, `Extraction.v`, `GlobalSem.v`, `ebpf_check.cpp`, the rest of `ebpf_project.cpp`, the rest of `ebpfBinSem.v` after the initial-state block (atomics, the old interpreter tail).

Rules that match slots this object actually contains:

- ALU32 MOV (`eval_alu32` `MOV`): `Val.longofintu` of the source. Zero-extend the low 32 bits into the register. C++ `emit_alu` for W32 does `trunc32`, the narrow op, then `zext64` (`ebpf_lift.cpp` 532–539). For a W32 immediate, `imm64` is called with `sign_imm` false, so the immediate is zero-extended to i64 before the trunc.
- ALU64 MOV: the source value, unchanged (`eval_alu64` `MOV`; `emit_wide` returns `src`).
- ALU64 ADD immediate: `Val.addl` of `eval_val_int W64`, and `eval_val_int` sign-extends the 32-bit immediate (`int64_of_int` = `Int64.repr (Int.signed i)`). The C++ lifter does the same for W64 when `LiftBug::ImmNoSignExtend` is off (`imm64`, `sign_imm` true). Slot 33’s `-4` is that case.
- ALU64 ADD register: `Val.addl` of the two register values. No width truncation.
- JMP64 JGT: unsigned `>`. Taken target is PC + offset, then `nextinstr` adds one more (`exec_jmpcmp`). Same numeric target as C++ `jump_target`.
- JMP32 JEQ / JNE: compare `Val.loword` of the register to the 32-bit immediate (`eval_cmp32`). Not a 64-bit compare.
- JMP64 JEQ: `eval_cmp64` equality. Immediate becomes `Vlong (int64_of_int i)` (sign-extended). Imm 0 stays 0.
- JA: `exec_jmp64` adds the 16-bit offset via `Val.offset_ptr` on PC, then `nextinstr`.
- EXIT: `exec_ret` on an empty call stack sets PC to `Vnullptr` and leaves `r0`. It does not free a frame. `initial_lst_state` starts with an empty `cstk`, `R1 = Vptr ctx 0`, `R10 = Vptr stk (repr 512)`, other registers `Vundef`, stack bytes `0 .. 512` valid.
- LDX: `exec_load`. A `Vptr` address is `Val.offset_ptr`. A `Vlong` address is `cast_i2p` of `base + signed offset` through `addr_map`; no matching region means `Stuck`. The loaded `Vint` is zero-extended to `Vlong` by `load_value_casting`. Sizes: byte `Mint8unsigned`, half `Mint16unsigned`, word `Mint32`, dword `Mint64`, via `loadv_unaligned` (byte-wise `Mem.loadbytes`).
- STX: `exec_store` calls `Val.offset_ptr` on the destination register and `store`. It does **not** call `cast_i2p`. A `Vlong` packet pointer is outside the rule text that was read. `eval_reg_immw` for a W32 store truncates a `Vlong` source with `Int.repr (Int64.unsigned i)`.
- LDDW constant: `exec_lddw` for `PSEUDO_Constant` writes `Int64.ofwords hi lo` and advances PC twice (`nextinstr` twice). Any other pseudo kind uses `cast_i2p` and `Stuck` if the integer is not in `addr_map`. The ELF relocation is not an input to this rule.
- CALL static id: `exec_instr` does not handle `CallByStaticID`. The match ends in `Stuck` (line 904). The inductive `step` constructor `exec_step_external` does handle it, but only by applying the uninterpreted `Variable ebpf_call_function` (imm and r1..r5 in, optional `(val * mem)` out). On `Some (res, m')` it sets `r0` to `res`, `undef_caller_save_regs` (r1..r5 become `Vundef`), and PC + 1. There is no `bpf_map_lookup_elem` definition in the text that was read. Helper id 1 is `lookup` only in `src/Observation/Insn.lean`, which is not the Alive2 IR.

`exec_call_internal` allocates a fresh 512-byte stack and saves r6–r10. This object’s call is not `CallInternal` (source field is 0, not 1).

## IR mapping against the existing C++ lifter only

`lift_ebpf` (`ebpf_lift.cpp`) consumes `vector<EbInsn>`, which is only `EbAlu` or `EbJmp`. It has no load, store, `LDDW`, or call constructor. `make_alive_trace` calls `decode_ebpf` first, so this object never reaches `emit`.

If the ALU/JMP slots were presented alone, the lifter would emit:

| decoded op | IR |
| --- | --- |
| W32 MOV imm | `trunc` to i32, the truncated immediate, `zext` to i64 |
| W64 MOV reg or imm | the source value itself (`bare_mov` is true). No `BinOp`. |
| W64 ADD | `BinOp` `Add` on i64. Immediate is sign-extended. |
| JGT W64 | `ICmp` `UGT`, branch to the target block or the fall-through block |
| JEQ | `ICmp` `EQ`. W32 truncates both sides first. W32 immediate is the zero-extended 32-bit field (`c32`). W64 immediate is sign-extended (`c64(int64_t)`). |
| JNE | `ICmp` `NE`, same width rule |
| JA | unconditional `Branch` to the target block |
| EXIT | `Return` of `regs[0]` as i64 |

`build_blocks` sets `loop` when a jump target is `<=` the jump index. None of the jumps in this object do that. The concrete interpreter (`Lifter::concrete`) only evaluates `ICmp::EQ` and `ICmp::UGT`. `ICmp::NE` (slots 9, 17, 43) takes `stop_unsupported`. Any `MemInstr` also takes `stop_unsupported` and would mark `MemorySummary::Changed`; the lifter never creates a `MemInstr`.

Pointer rule the gate already has, relevant even to the ALU slots: `pointer_alu` / `pointer_jmp` are true when a source or destination value has `RegOrigin::Pointer`. In `LiftInit::Rocq`, r1 and r10 start as `PoisonValue` with that origin (`init_regs`). `ebpf_project.cpp` line 922 blocks the pc when either side reports `pointer_use`. Slots 3–5, 10–12, 18–22, 25–29, and 32–33 are pointer arithmetic or pointer compares if r6/r1/r10 are pointers. The lifter folds them with `BinOp Add` and `ICmp` on i64 anyway; the gate then refuses the proof. It does not emit a memory operand.

`r10` is register 10. `emit_alu` will read `regs[10]`. The Rocq init models it as a stack pointer. The zero init models it as the constant 0. Neither init allocates the 4-byte spill.

## Memory, helper, map, and loop requirements

Loop: **no**. Every jump offset is positive and lands inside `0 .. 57`. A lifter that uses the same `<=` test as `build_blocks` must report `loop = false`.

Memory:

- Context: `r1` on entry is a pointer to `xdp_md`. Two `u32` loads, offsets 0 and 4. Those offsets are CO-RE `byte_off` against the local `xdp_md`, and they already match that BTF.
- Packet: `w6` is that `u32` `data` pointer, zero-extended, not a fresh 64-bit pointer load. Later halfword and byte loads, and the six halfword stores, use `r6` plus a small constant. The inner VLAN type uses `r1` after `r1 = r6; r1 += 14`, plus 2. Bounds checks are unsigned `>` against `w2` (`data_end`), at `data+14`, `data+18`, `L3+20`, and `L3+40`. Equality is allowed (the compare is not `>=`).
- The six stores swap the six octets of `h_dest` with the six octets of `h_source` as three `u16` pairs. Order matters: slot 44’s value is stored at +6 only at slot 54, after +0 has already been overwritten. A later implementer has to keep that sequence or an equivalent permutation. There is no CO-RE record on these offsets.
- Stack: one `u32` slot at `r10-4`, stored at slot 31, read at slot 41. Both are on every path that reaches the call. The early exits do not read it. `bpf_stack_size` in the Rocq file is 512, and the initial `R10` offset is 512. The spill is 4 bytes at the top of that frame. No other stack slot is used.
- Map value: one `u64` load, add 1, `u64` store, only when the call result is not 0. Address is `(r0 + 0)`, not a CO-RE field.

Helper:

- One call, static id immediate **1**, source-register field 0, offset 0. Arguments in registers at the call: `r1` map, `r2` pointer to the spilled `u32` key. `r3`–`r5` are not meaningful arguments here.
- After the call the program uses `r0` and `r6` only, then reloads `r1` from the stack. That matches `undef_caller_save_regs` (r1–r5 die, r6–r9 and r10 stay) **if** a semantics for id 1 is supplied. The Rocq variable does not supply it. The C++ lifter has no call.
- Id 1 is `HelperKind.lookup` in `src/Observation/Insn.lean` (arity 2). That Lean inductive is not an Alive2 instruction and is not a compilation of this object.

Map:

- One map, ELF symbol `rxcnt`, array, key 4, value 8, 256 entries, flags 0.
- The reference is `R_BPF_64_64` at slot 34, not a `PSEUDO_MAP_IDX` immediate and not an `.xpost.*` record inside `bpf.o`.
- The key is the protocol `u32` (0 when the header was skipped or too short). A value of 0..255 is inside `max_entries`. The program still tests the call result for 0 and must not store when the result is 0.

Packet writes exist (six halfword stores). One map write exists (the `u64` increment). Both are absent from the C++ lifter.

## Conversion result

**NOT CONVERTED.**

`decode_ebpf` throws at slot 1: `eBPF insn 1: unsupported class in opcode 0x61`. `lift_ebpf` is never called. No Alive2 function and no `.alive` file were produced. Calling the missing load/store/call model `UNSUPPORTED` would not be a successful conversion, and this report does not do that.

Concrete gaps, all visible in code that was read:

1. The C++ decoder has no LD, LDX, ST, STX, or `LDDW` class, and its jump switch has no CALL (`0x85` would be `unsupported jump opcode` even if slot 1 were ignored).
2. The C++ lifter has no memory, stack, packet, map, or helper instruction. Its concrete evaluator rejects `ICmp::NE` and any `MemInstr`.
3. The Rocq load rule can turn a `Vlong` into a pointer through `addr_map`. The Rocq store rule that was read cannot; it only uses `Val.offset_ptr`. This program’s packet pointer is produced by a `u32` load.
4. The Rocq `LDDW` rule, given the unrelocated word, loads the constant 0 (`PSEUDO_Constant`). The map identity exists only in `R_BPF_64_64` / symbol `rxcnt`.
5. `exec_instr` returns `Stuck` for `CallByStaticID`. `step`’s external-call case calls an uninterpreted variable. There is no map-lookup or map-update axiom in the files that were read.
6. The symbolic projection’s `supported_insn` is ALU64 MOV, ADD, SUB, DIV, plus JA, EXIT, and JMP64 JGT only. ALU32, JMP32, JMP64 JEQ, and every memory op are outside it. Pointer uses are blocked at `ebpf_project.cpp:922` even when the opcode is in that set.

## Proof coverage

`alive2/rocq/README.md`: the concrete checker compares a few programs, one concrete input at a time, and does not prove the lifter. The symbolic checker projects `eval_alu64`, `eval_div_u64`, and `exec_jmpcmp` for MOV64, ADD64, SUB64, DIV64, JGT64, JA, and EXIT. Anything else is `UNSUPPORTED`, and the README says that is not a pass. `ebpf_exhibit.cpp` states that supported-scope equivalence does not cover loops, memory, maps, helpers, or pointer arithmetic.

This object uses memory, a map, a helper, and pointer arithmetic. It has no loop. The overlapping opcode names (ALU64 MOV/ADD, JGT, JA, EXIT) are not a proof of this program: they are not reached by `decode_ebpf`, and the JGT/ADD uses are pointer uses the gate blocks. No exhibit row for `just_tx` was run. No SMT result is claimed.

## Counterexample idea

Do not treat a failed decode as agreement.

Packet, 34 bytes, `data_end = data+34`, Ethernet type bytes at offset 12 equal to `08 00` (so the `u16` load is `0x8`), IPv4 protocol byte at Ethernet-offset 23 (L3 offset 14 + 9) equal to `0x11`, and `data_end` exactly at the IPv4 header end. No VLAN. Map `rxcnt` slot 0x11 holds `u64` 0, and the lookup returns that slot.

The instruction words require: the `>` at slot 22 is false (34 is not strictly above 34), `w1` becomes `0x11`, the `u64` becomes 1, the six halfword stores exchange the addresses, and `r0` at the exit is 3.

A lifter that implements that `JGT` as `>=` rejects this packet, does not write the map, does not write the packet, and returns 1. Same return-code split for a 14-byte non-IP frame if the first `JGT` (slot 5) is weakened to `>=`: both the right program and the wrong one return 1, but only the right one performs the map update at key 0. The map write is the observation that separates them.

A second split, for the width of slot 16: type bytes `dd 86` (register value `0xdd86`). `JMP32` compares the low 32 bits, so a zero-extended and a sign-extended halfword both equal immediate `0xdd86`. A lifter that decodes `0x16` as a 64-bit compare against sign-extended `0xdd86` sees `0xffffffffffffdd86 != 0xdd86`, leaves the protocol at 0, and returns 1 with no address swap. `eval_cmp32` and `emit_cmp` for `EbWidth::W32` both truncate; the counterexample is against dropping that truncation.

A third split, for the relocation: feeding the raw `LDDW` word to `exec_lddw` yields constant 0 (`PSEUDO_Constant`), not `rxcnt`. The lookup then misses or hits a different map, the `u64` store is skipped or hits the wrong object, and a UDP packet can still return 3. The return code does not catch this. The map identity does.

STATUS: ISSUES
