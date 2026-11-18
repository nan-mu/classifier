# memcpy observation

Observation of one BPF relocatable object so a later implementer can compile it. This file does not define a new ISA. It classifies the bytes against the decoder, lifter, and Rocq rules that were actually read. Conversion result: NOT CONVERTED. No `.alive` text is emitted.

## Evidence

- Object: `/Volumes/SSD/bs/build/memcpy/bpf.o`
- Expected sha256: `d6c2f0cce069229f473fb49983147e7ca351a9effad43c3ddda395b62f46a1fa`
- Computed: `shasum -a 256` on that path returned the same digest. The file was trusted only after that match.
- Notes: `/Volumes/SSD/bs/build/memcpy/bpf.toml` (source path, objdump paste, map note, three CO-RE rows). The toml is not a second encoding of the instruction bytes.
- Noted C source, read after the object: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/memcpy.c`. Used only to name the source-level copy. The instruction list below is from the object.
- Tools actually run: `/opt/homebrew/opt/llvm/bin/llvm-readelf -a` and `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r -s -t` on the object. A local field walk of the `xdp` bytes (opcode, dst, src, off, imm) was checked against those dumps. BTF and `.BTF.ext` were parsed from the section bytes, not from the toml alone.
- Rules read: `alive2/src/ebpf.h`, `alive2/src/ebpf_decode.cpp`, `alive2/src/ebpf_lift.cpp` (ALU/JMP emission and CFG), `alive2/src/ebpf_project.cpp` (`supported_insn`, `eval_alu`, `jgt_cond`, the gate join around lines 901–929), `alive2/rocq/upstream/theories/ebpfSyntax.v` (instruction forms through `instruction`), `alive2/rocq/upstream/theories/ebpfDecoder.v` (all of `decode_insn` / `decode_lddw_insn` / `find_instr`), `alive2/rocq/upstream/theories/ebpfBinSem.v` (`eval_reg_immw`, `eval_alu32`, `eval_alu64`, `exec_alu`, `eval_cmp32`, `eval_cmp64`, `exec_jmpcmp`, `eval_shift_mask`, `load` / `exec_load`, `store` / `exec_store`, `exec_lddw`, `exec_instr`, `nextinstr`, `step`, `initial_lst_state`, the live `exec_ret` at line 819).
- Not read, so not cited as rules: `alive2/rocq/upstream/validator/Validation.v` (a search found no `Pload` / `Pstore` hits; the file body was not read), `CMemoryModel.v`, `ebpfState.v` beyond what the decoder imports, the bodies of `alive2/tests/bpf/*.c`, and the kernel header that defines `XDP_ABORTED` / `XDP_PASS`.

## File shape

ELF64, `ELFDATA2LSB` (little endian), `ET_REL`, `EM_BPF`, 26 sections, no program headers. Instruction immediates and offsets are little-endian 8-byte slots.

Executable sections (`SHF_EXECINSTR`):

| section | type | file off | size | flags |
| --- | --- | --- | --- | --- |
| `.text` | PROGBITS | `0x40` | **0** | AX |
| `xdp` | PROGBITS | `0x40` | `0x248` (584) | AX |

`.text` is empty. It is not the program. `llvm-objdump -d` of `.text` produced no instructions. The program is `xdp`.

Symbol `memcpy_xdp`: `FUNC`, `GLOBAL`, section `xdp`, value 0, size 584. That is the only function. One entry: slot 0 of `xdp`.

Other non-code symbols: `LICENSE` (`OBJECT`, section `license`, 4 bytes, contents `GPL\0`), `workload` (`OBJECT`, section `.maps`, 32 bytes, all zero). File symbol name: `memcpy.c`.

Slots: 584 / 8 = **73**. No opcode `0x18`, so no LDDW and no second slot. Instruction count equals slot count. No backward jump. Every conditional target is slot 72. Slot 72 is `exit`.

## Relocations, CO-RE, maps

There is no `.rel.xdp` and no relocation whose `sh_info` is the `xdp` section. No instruction immediate is an ELF relocation addend.

Three different references, kept apart:

1. Raw object operands. Every `xdp` immediate and offset is already in the slot. ALU immediates are `0`, `8`, `32`, `-13`, `2`. Load/store offsets are the small constants in the instruction list. Jump displacements are the `off` fields below. None of these is a map file descriptor, a map index, or an external symbol.

2. CO-RE records in `.BTF.ext`, not ELF relocations on `xdp`. Parsed `bpf_core_relo` records (record size 16), section name `xdp`, kind numeric 0. `llvm-objdump -d` prints the same sites as `CO-RE <byte_off>`. The enum that names kind 0 was not read in this repo; the dump text is the evidence that objdump calls kind 0 a byte offset.

   | insn byte off | slot | type id | access | stored `off` |
   | --- | --- | --- | --- | --- |
   | `0x8` | 1 | 17 | `0:1` | `+4` |
   | `0x10` | 2 | 17 | `0:0` | `+0` |
   | `0x58` | 11 | 17 | `0:1` | `+4` |

   BTF type id 17 is `struct xdp_md`, size 24, members `data` at byte 0, `data_end` at byte 4, then `data_meta`, `ingress_ifindex`, `rx_queue_index`, `egress_ifindex` (all `__u32`). Access `0:0` is `data`. Access `0:1` is `data_end`. The stored offsets already match this BTF. A loader that applies CO-RE can still rewrite those `off` fields if a target layout differs. The C++ decoder never reads `.BTF.ext`.

   `.rel.BTF.ext` has 55 `R_BPF_64_NODYLD32` entries against symbol `xdp` (value 0). They fix up BTF.ext instruction/line offsets so they stay section-relative. They do not patch `xdp` itself.

3. BTF datasec offsets, not a map-index reference and not an instruction patch. `.rel.BTF` has two `R_BPF_64_NODYLD32` entries. Both current u32 values are 0.

   | section off | symbol | field |
   | --- | --- | --- |
   | `0x250` | `workload` | offset field of the `.maps` `btf_var_secinfo` (type 15, size 32) |
   | `0x268` | `LICENSE` | offset field of the `license` `btf_var_secinfo` (size 4) |

   There is no `R_BPF_64_64`, no LDDW, and no `src_reg` in `{1,2,5,6}` that would be `PSEUDO_MAP_FD`, `PSEUDO_MAP_VALUE`, `PSEUDO_MAP_IDX`, or `PSEUDO_MAP_IDX_VALUE` (`ebpfDecoder.v` `decode_lddw_insn`). The toml key `aot_addr = 0x403802fc` is not an ELF field and is not an operand.

`.maps` / BTF: `workload` is `BPF_MAP_TYPE_HASH` in the toml, `max_entries = 2`, key `__u8`, value `struct exec_val` (8 × `__u32`). The section bytes are zeros. The `xdp` text never mentions the map.

## Real disassembly

`llvm-objdump -d --section=xdp` (CO-RE notes kept). `.text` contributed nothing.

```
0000000000000000 <memcpy_xdp>:
       0:	w0 = 0x0
       1:	w8 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)
       2:	w2 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [17] struct xdp_md::data (0:0)
       3:	r3 = r2
       4:	r3 += 0x8
       5:	if r3 > r8 goto +0x42 <L0>
       6:	w7 = *(u8 *)(r2 + 0x4)
       7:	w5 = *(u8 *)(r2 + 0x5)
       8:	w6 = *(u8 *)(r2 + 0x6)
       9:	w4 = *(u8 *)(r2 + 0x7)
      10:	w8 -= w3
      11:	w1 = *(u32 *)(r1 + 0x4)
		0000000000000058:  CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)
      12:	if w8 < 0x18 goto +0x3b <L0>
      13:	r8 = r2
      14:	r8 += 0x20
      15:	if r8 > r1 goto +0x38 <L0>
      16:	r5 <<= 0x8
      17:	r5 |= r7
      18:	r6 <<= 0x10
      19:	r4 <<= 0x18
      20:	r4 |= r6
      21:	r4 |= r5
      22:	w1 = w4
      23:	w1 += -0xd
      24:	if w1 < -0xc goto +0x2f <L0>
      25:	r1 = r3
      26:	r1 += r4
      27:	w5 = *(u8 *)(r3 + 0x0)
      28:	*(u8 *)(r1 + 0x0) = w5
      29:	w0 = 0x2
      30:	if w4 < 0x2 goto +0x29 <L0>
      31:	w5 = *(u8 *)(r2 + 0x9)
      32:	*(u8 *)(r1 + 0x1) = w5
      33:	if w4 == 0x2 goto +0x26 <L0>
      34:	r1 = r3
      35:	r1 += r4
      36:	w5 = *(u8 *)(r2 + 0xa)
      37:	*(u8 *)(r1 + 0x2) = w5
      38:	if w4 < 0x4 goto +0x21 <L0>
      39:	w5 = *(u8 *)(r2 + 0xb)
      40:	*(u8 *)(r1 + 0x3) = w5
      41:	if w4 == 0x4 goto +0x1e <L0>
      42:	r1 = r3
      43:	r1 += r4
      44:	w5 = *(u8 *)(r2 + 0xc)
      45:	*(u8 *)(r1 + 0x4) = w5
      46:	if w4 < 0x6 goto +0x19 <L0>
      47:	w5 = *(u8 *)(r2 + 0xd)
      48:	*(u8 *)(r1 + 0x5) = w5
      49:	if w4 == 0x6 goto +0x16 <L0>
      50:	r1 = r3
      51:	r1 += r4
      52:	w5 = *(u8 *)(r2 + 0xe)
      53:	*(u8 *)(r1 + 0x6) = w5
      54:	if w4 < 0x8 goto +0x11 <L0>
      55:	w5 = *(u8 *)(r2 + 0xf)
      56:	*(u8 *)(r1 + 0x7) = w5
      57:	if w4 == 0x8 goto +0xe <L0>
      58:	r1 = r3
      59:	r1 += r4
      60:	w5 = *(u8 *)(r2 + 0x10)
      61:	*(u8 *)(r1 + 0x8) = w5
      62:	if w4 < 0xa goto +0x9 <L0>
      63:	w5 = *(u8 *)(r2 + 0x11)
      64:	*(u8 *)(r1 + 0x9) = w5
      65:	if w4 == 0xa goto +0x6 <L0>
      66:	r3 += r4
      67:	w1 = *(u8 *)(r2 + 0x12)
      68:	*(u8 *)(r3 + 0xa) = w1
      69:	if w4 < 0xc goto +0x2 <L0>
      70:	w1 = *(u8 *)(r2 + 0x13)
      71:	*(u8 *)(r3 + 0xb) = w1
<L0>:
      72:	exit
```

`+N` in that listing is the raw `off` field, not the destination slot. Destination slot is `pc + 1 + off` (`jump_target` in `ebpf_decode.cpp`). All fifteen conditional offsets land on slot 72. `exit` has `off = 0` and `imm = 0`; it is not a jump to slot 73.

## Instruction list

Class numbers are `opcode & 7`, matching `ebpf_decode.cpp` (`kAlu = 0x04`, `kJmp = 0x05`, `kJmp32 = 0x06`, `kAlu64 = 0x07`) and `ebpfDecoder.v` `BPF_CLASS` (`LDX = 1`, `STX = 3`). Memory size is `(opcode >> 3) & 3` and mode is `opcode >> 5`, as in `decode_insn`: mode `0x3` is the `0x60` MEM mode, size `0` Word, size `2` Byte. Every memory instruction in this object has `imm = 0`, which is what that decoder requires.

C++ column is what `decode_ebpf` does with that opcode. It has no load/store alternative: classes other than ALU and JMP hit `ebpf_decode.cpp` lines 164–167 and throw `unsupported class in opcode 0xNN`. The first such slot is 1 (`0x61`). Slots after that are still classified from the same code; the function would not reach them.

Rocq column is `decode_insn` on the same fields. `imm0` means the `check_imm_0` test that MEM loads and stores require.

| pc | bytes | what | C++ `decode_ebpf` | Rocq `decode_insn` | jump |
| --- | --- | --- | --- | --- | --- |
| 0 | `b4 00 0000 00000000` | ALU32 MOV K r0, 0 | `EbAlu::Mov` W32 | `Palu MOV W32` | |
| 1 | `61 18 0004 00000000` | LDX W r8, [r1+4] | reject class LDX | `Pload Word` r8, r1, +4 | |
| 2 | `61 12 0000 00000000` | LDX W r2, [r1+0] | reject class LDX | `Pload Word` r2, r1, +0 | |
| 3 | `bf 23 0000 00000000` | ALU64 MOV X r3, r2 | `EbAlu::Mov` W64 | `Palu MOV W64` | |
| 4 | `07 03 0000 08000000` | ALU64 ADD K r3, 8 | `EbAlu::Add` W64 | `Palu ADD W64` | |
| 5 | `2d 83 0042 00000000` | JMP JGT X r3, r8, +66 | `EbJmp::Jgt` W64 | `Pjmpcmp (GT Unsigned) W64` | 72 |
| 6 | `71 27 0004 00000000` | LDX B r7, [r2+4] | reject class LDX | `Pload Byte` | |
| 7 | `71 25 0005 00000000` | LDX B r5, [r2+5] | reject class LDX | `Pload Byte` | |
| 8 | `71 26 0006 00000000` | LDX B r6, [r2+6] | reject class LDX | `Pload Byte` | |
| 9 | `71 24 0007 00000000` | LDX B r4, [r2+7] | reject class LDX | `Pload Byte` | |
| 10 | `1c 38 0000 00000000` | ALU32 SUB X r8, r3 | `EbAlu::Sub` W32 | `Palu SUB W32` | |
| 11 | `61 11 0004 00000000` | LDX W r1, [r1+4] | reject class LDX | `Pload Word` | |
| 12 | `a6 08 003b 18000000` | JMP32 JLT K r8, 24, +59 | `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` | 72 |
| 13 | `bf 28 0000 00000000` | ALU64 MOV X r8, r2 | `EbAlu::Mov` W64 | `Palu MOV W64` | |
| 14 | `07 08 0000 20000000` | ALU64 ADD K r8, 32 | `EbAlu::Add` W64 | `Palu ADD W64` | |
| 15 | `2d 18 0038 00000000` | JMP JGT X r8, r1, +56 | `EbJmp::Jgt` W64 | `Pjmpcmp (GT Unsigned) W64` | 72 |
| 16 | `67 05 0000 08000000` | ALU64 LSH K r5, 8 | `EbAlu::Lsh` W64 | `Palu LSH W64` | |
| 17 | `4f 75 0000 00000000` | ALU64 OR X r5, r7 | `EbAlu::Or` W64 | `Palu OR W64` | |
| 18 | `67 06 0000 10000000` | ALU64 LSH K r6, 16 | `EbAlu::Lsh` W64 | `Palu LSH W64` | |
| 19 | `67 04 0000 18000000` | ALU64 LSH K r4, 24 | `EbAlu::Lsh` W64 | `Palu LSH W64` | |
| 20 | `4f 64 0000 00000000` | ALU64 OR X r4, r6 | `EbAlu::Or` W64 | `Palu OR W64` | |
| 21 | `4f 54 0000 00000000` | ALU64 OR X r4, r5 | `EbAlu::Or` W64 | `Palu OR W64` | |
| 22 | `bc 41 0000 00000000` | ALU32 MOV X r1, r4 | `EbAlu::Mov` W32 | `Palu MOV W32` | |
| 23 | `04 01 0000 f3ffffff` | ALU32 ADD K r1, -13 | `EbAlu::Add` W32 | `Palu ADD W32` | |
| 24 | `a6 01 002f f4ffffff` | JMP32 JLT K r1, -12, +47 | `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` | 72 |
| 25 | `bf 31 0000 00000000` | ALU64 MOV X r1, r3 | `EbAlu::Mov` W64 | `Palu MOV W64` | |
| 26 | `0f 41 0000 00000000` | ALU64 ADD X r1, r4 | `EbAlu::Add` W64 | `Palu ADD W64` | |
| 27 | `71 35 0000 00000000` | LDX B r5, [r3+0] | reject class LDX | `Pload Byte` | |
| 28 | `73 51 0000 00000000` | STX B [r1+0], r5 | reject class STX | `Pstore Byte` (reg) | |
| 29 | `b4 00 0000 02000000` | ALU32 MOV K r0, 2 | `EbAlu::Mov` W32 | `Palu MOV W32` | |
| 30 | `a6 04 0029 02000000` | JMP32 JLT K r4, 2, +41 | `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` | 72 |
| 31 | `71 25 0009 00000000` | LDX B r5, [r2+9] | reject class LDX | `Pload Byte` | |
| 32 | `73 51 0001 00000000` | STX B [r1+1], r5 | reject class STX | `Pstore Byte` | |
| 33 | `16 04 0026 02000000` | JMP32 JEQ K r4, 2, +38 | `EbJmp::Jeq` W32 | `Pjmpcmp EQ W32` | 72 |
| 34 | `bf 31 0000 00000000` | ALU64 MOV X r1, r3 | `EbAlu::Mov` W64 | `Palu MOV W64` | |
| 35 | `0f 41 0000 00000000` | ALU64 ADD X r1, r4 | `EbAlu::Add` W64 | `Palu ADD W64` | |
| 36 | `71 25 000a 00000000` | LDX B r5, [r2+10] | reject class LDX | `Pload Byte` | |
| 37 | `73 51 0002 00000000` | STX B [r1+2], r5 | reject class STX | `Pstore Byte` | |
| 38 | `a6 04 0021 04000000` | JMP32 JLT K r4, 4, +33 | `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` | 72 |
| 39 | `71 25 000b 00000000` | LDX B r5, [r2+11] | reject class LDX | `Pload Byte` | |
| 40 | `73 51 0003 00000000` | STX B [r1+3], r5 | reject class STX | `Pstore Byte` | |
| 41 | `16 04 001e 04000000` | JMP32 JEQ K r4, 4, +30 | `EbJmp::Jeq` W32 | `Pjmpcmp EQ W32` | 72 |
| 42 | `bf 31 0000 00000000` | ALU64 MOV X r1, r3 | `EbAlu::Mov` W64 | `Palu MOV W64` | |
| 43 | `0f 41 0000 00000000` | ALU64 ADD X r1, r4 | `EbAlu::Add` W64 | `Palu ADD W64` | |
| 44 | `71 25 000c 00000000` | LDX B r5, [r2+12] | reject class LDX | `Pload Byte` | |
| 45 | `73 51 0004 00000000` | STX B [r1+4], r5 | reject class STX | `Pstore Byte` | |
| 46 | `a6 04 0019 06000000` | JMP32 JLT K r4, 6, +25 | `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` | 72 |
| 47 | `71 25 000d 00000000` | LDX B r5, [r2+13] | reject class LDX | `Pload Byte` | |
| 48 | `73 51 0005 00000000` | STX B [r1+5], r5 | reject class STX | `Pstore Byte` | |
| 49 | `16 04 0016 06000000` | JMP32 JEQ K r4, 6, +22 | `EbJmp::Jeq` W32 | `Pjmpcmp EQ W32` | 72 |
| 50 | `bf 31 0000 00000000` | ALU64 MOV X r1, r3 | `EbAlu::Mov` W64 | `Palu MOV W64` | |
| 51 | `0f 41 0000 00000000` | ALU64 ADD X r1, r4 | `EbAlu::Add` W64 | `Palu ADD W64` | |
| 52 | `71 25 000e 00000000` | LDX B r5, [r2+14] | reject class LDX | `Pload Byte` | |
| 53 | `73 51 0006 00000000` | STX B [r1+6], r5 | reject class STX | `Pstore Byte` | |
| 54 | `a6 04 0011 08000000` | JMP32 JLT K r4, 8, +17 | `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` | 72 |
| 55 | `71 25 000f 00000000` | LDX B r5, [r2+15] | reject class LDX | `Pload Byte` | |
| 56 | `73 51 0007 00000000` | STX B [r1+7], r5 | reject class STX | `Pstore Byte` | |
| 57 | `16 04 000e 08000000` | JMP32 JEQ K r4, 8, +14 | `EbJmp::Jeq` W32 | `Pjmpcmp EQ W32` | 72 |
| 58 | `bf 31 0000 00000000` | ALU64 MOV X r1, r3 | `EbAlu::Mov` W64 | `Palu MOV W64` | |
| 59 | `0f 41 0000 00000000` | ALU64 ADD X r1, r4 | `EbAlu::Add` W64 | `Palu ADD W64` | |
| 60 | `71 25 0010 00000000` | LDX B r5, [r2+16] | reject class LDX | `Pload Byte` | |
| 61 | `73 51 0008 00000000` | STX B [r1+8], r5 | reject class STX | `Pstore Byte` | |
| 62 | `a6 04 0009 0a000000` | JMP32 JLT K r4, 10, +9 | `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` | 72 |
| 63 | `71 25 0011 00000000` | LDX B r5, [r2+17] | reject class LDX | `Pload Byte` | |
| 64 | `73 51 0009 00000000` | STX B [r1+9], r5 | reject class STX | `Pstore Byte` | |
| 65 | `16 04 0006 0a000000` | JMP32 JEQ K r4, 10, +6 | `EbJmp::Jeq` W32 | `Pjmpcmp EQ W32` | 72 |
| 66 | `0f 43 0000 00000000` | ALU64 ADD X r3, r4 | `EbAlu::Add` W64 | `Palu ADD W64` | |
| 67 | `71 21 0012 00000000` | LDX B r1, [r2+18] | reject class LDX | `Pload Byte` | |
| 68 | `73 13 000a 00000000` | STX B [r3+10], r1 | reject class STX | `Pstore Byte` | |
| 69 | `a6 04 0002 0c000000` | JMP32 JLT K r4, 12, +2 | `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` | 72 |
| 70 | `71 21 0013 00000000` | LDX B r1, [r2+19] | reject class LDX | `Pload Byte` | |
| 71 | `73 13 000b 00000000` | STX B [r3+11], r1 | reject class STX | `Pstore Byte` | |
| 72 | `95 00 0000 00000000` | JMP EXIT | `EbJmp::Exit` | `Pret` | exit |

Counts: ALU32 5, ALU64 21, JMP64 3 (two `JGT` and `EXIT`), JMP32 13 (eight `JLT`, five `JEQ`), LDX 19 (three word, sixteen byte), STX 12 (all byte). 5+21+3+13+19+12 = 73.

Immediate ALU and immediate jumps all have `src_reg = 0`, which both decoders require. Register jumps have `imm = 0`, which Rocq requires (`valid_args`). ALU offsets are 0, so none of these is `MOVSX`, `SDIV`, or `END`. No `CALL` (`code 0x8`), no `JA`, no atomic mode.

Jump slots and targets: 5→72, 12→72, 15→72, 24→72, 30→72, 33→72, 38→72, 41→72, 46→72, 49→72, 54→72, 57→72, 62→72, 65→72, 69→72, and 72 exits. Leaders if the C++ CFG builder were reached: 0, 6, 13, 16, 25, 31, 34, 39, 42, 47, 50, 55, 58, 63, 66, 70, 72. Block 70–71 falls through to 72. `build_blocks` sets `loop` only when a target is `<=` the jump index. None is. Loop flag for this CFG: false.

## What the bytes do

This is a reading of the classified slots plus the C body, not a new semantics.

`memcpy.c` `memcpy_xdp` returns early on a failed bounds/length check and otherwise does `payload[param + i] = payload[i]` for `i` in `0 .. param-1`, with `param` in 1..12, then returns the pass code. The file comment about copying map keys is not what the function or the object does. The map is unused by the text.

On the object, with r1 the context pointer the C signature names (the ELF does not itself mark r1; Rocq `initial_lst_state` does set R1 to the context block):

- Slots 1–2 load `xdp_md.data_end` and `xdp_md.data` as **u32**, zero-extended into r8 and r2. They are not 64-bit loads in the object. Kernel context rewriting, if any, is not in the file.
- Slots 3–5 require `data+8 <= data_end` with a 64-bit unsigned `>`.
- Slots 6–9 load four packet bytes at `data+4 .. data+7`.
- Slot 10 is a **32-bit** subtract `w8 -= w3` (`data_end - (data+8)`), then zero-extend.
- Slot 11 reloads `data_end` into r1, which drops the context pointer.
- Slot 12 exits unless that 32-bit difference is `>= 24`.
- Slots 13–15 exit unless `data+32 <= data_end` (64-bit unsigned).
- Slots 16–21 assemble r4 = `b0 | (b1<<8) | (b2<<16) | (b3<<24)` from those four bytes (little-endian u32). The shifts are 8, 16, and 24, all in range for a 64-bit shift.
- Slots 22–24 are the length gate. `w1 = w4; w1 += -13; if w1 u< 0xfffffff4 goto exit`. For a 32-bit unsigned value `n`, `n-13` is in `{0xfffffff4 .. 0xffffffff}` exactly when `n` is in `{1 .. 12}`. Outside that range the jump is taken and r0 is still 0. This is unsigned. It is not a signed `< -12`.
- Slots 25–71 are the unrolled copy of `n` bytes from `data+8` to `data+8+n`. The first byte is stored, then r0 is set to 2, then a `JLT`/`JEQ` pair stops at the remaining length. The regions `[data+8, data+8+n)` and `[data+8+n, data+8+2n)` only meet at an endpoint, so a later store does not clobber a byte this copy still has to read.
- Slot 72 exits with r0. r0 is written only at slot 0 (0) and slot 29 (2).

`memcpy.c` names the two returns `XDP_ABORTED` and `XDP_PASS`. The object immediates are 0 and 2. The header that defines the macros was not read.

## Semantic rules that were read

ALU32, from `eval_alu32`: take `Val.loword` of the destination, the source register's low word or the 32-bit immediate, operate, then `Val.longofintu` (zero-extend into the 64-bit register). Covers the slots here: `ADD`, `SUB`, `MOV`. `eval_alu64` operates on the full register; a K immediate is `int64_of_int`, which sign-extends (`eval_val_int`). The ALU64 immediates in this object are `+8` and `+32`, so sign-extend and zero-extend match. `LSH` shifts by `eval_shift_mask` (AND 63 on W64, AND 31 on W32). `OR` is `Val.orl` / `Val.or`. `exec_alu` writes the result and `nextinstr` (PC + 1). Same-register `SUB` is special-cased to zero; this object has no same-register subtract.

Jumps, from `exec_jmpcmp`: compare, and on true set PC to `offset_ptr(PC, off)` before `nextinstr` adds one. `step` looks up `find_instr (Ptrofs.unsigned ofs)`, and the initial PC is `Vptr blk 0`, so the offset unit in this semantics is one instruction slot. That matches C++ `jump_target` = `index + 1 + off`. `JGT` is unsigned (`GT Unsigned`). `JLT` is unsigned (`LT Unsigned`). `JEQ` is `EQ`. A W32 compare uses `Val.loword` and the immediate as `Vint`, so the bit pattern of `-12` is `0xfffffff4`, compared unsigned. `eval_cmp_static` does not fire for these immediates (the W32 unsigned `<` static case is only immediate 0). `exec_ret` on an empty call stack sets PC to `Vnullptr` and leaves R0.

Loads and stores, from `exec_load` / `exec_store`. A `Vptr` address is `offset_ptr` by the instruction `off`. A `Vlong` address is `cast_i2p` after adding the signed offset, and fails (`Stuck`) if it is not in `addr_map`. `Pload Byte` uses `Mint8unsigned`; `Pload Word` uses `Mint32`. `load_value_casting` zero-extends a `Vint` to `Vlong`. `Pstore Byte` stores `eval_reg_immw W32` through `Mint8unsigned` (the low byte). A failed pointer or a failed `Mem.load`/`store` is `Stuck`, not a zero result. `exec_load_probe` is a different opcode (mode field `0x1`); this object does not use it. `exec_instr` dispatches `Pload` to `exec_load` and `Pstore` to `exec_store`. `exec_instr_event` records `eBPF_vload` / `eBPF_vstore`.

`initial_lst_state` sets R1 to the context pointer and R10 to the stack pointer. This object never reads or writes r9 or r10. R1 stops being the context at slot 11.

C++ decoder rules used for the non-memory slots are the ALU switch (`0x00` add, `0x10` sub, `0x40` or, `0x60` lsh, `0xb0` mov with offset 0) and the jump switch (`0x10` jeq, `0x20` jgt, `0xa0` jlt, `0x90` exit). Width is the class: ALU32 vs ALU64, JMP vs JMP32.

## IR mapping against the existing C++ lifter only

`EbInsn` is only `EbAlu` or `EbJmp` (`ebpf.h`). `lift_ebpf` never sees a load or a store. There is no existing IR opcode in this lifter for `Pload` or `Pstore`. Mapping those 31 slots onto `BinOp` would be a new encoding; it is not done here.

If the memory slots were absent, the lifter would map the rest as follows (`emit_alu`, `emit_wide`, `emit_narrow`, `emit_cmp`). This is a correspondence, not a conversion of this object.

| object form | existing IR |
| --- | --- |
| ALU64 MOV | the source value, no extra op (`emit_wide` `Mov`) |
| ALU64 ADD | `BinOp::Add` on `i64` |
| ALU64 OR | `BinOp::Or` on `i64` |
| ALU64 LSH | `BinOp::And` with 63, then `BinOp::Shl` (`shift`; mask omitted only for `LiftBug::ShiftWithoutMask`) |
| ALU32 MOV / ADD / SUB | `Trunc` to `i32`, the same op on `i32`, `ZExt` to `i64`. ALU32 immediates are zero-extended into the i64 constant (`sign_imm` is false unless width is W64) and then truncated |
| JMP64 JGT | `ICmp::UGT` on i64, branch to the target block or the fall-through block |
| JMP32 JLT | `Trunc` both sides to i32, immediate via `c32(uint32_t(imm))` so `-12` is `0xfffffff4`, `ICmp::ULT` |
| JMP32 JEQ | same truncation, `ICmp::EQ` |
| EXIT | `Return` of the i64 in r0 |

`pointer_alu` / `pointer_jmp` only set `EbSite::pointer_use`. They still emit integer ops. In `LiftInit::Rocq`, r1 and r10 start as `PoisonValue` tagged `RegOrigin::Pointer`. Any ALU or compare that still sees that tag is a bitvector use of a pointer. Slot 4 would be one (`r3 = r2` after r2 was loaded, but the load is not modeled, so r2 would still be undef/poison depending on init). The lifter has no packet memory, so the copy cannot be an IR side effect today.

`LiftBug` variants (`AddAsSub`, `Alu32AsAlu64`, `ImmNoSignExtend`, `JumpPlusOne`, `ShiftWithoutMask`) are injection switches. They are not the semantics of this object.

## Memory, helper, map, loop

- Memory: required. 19 zero-extending loads (3 × u32 from the context, 16 × u8 from the packet) and 12 u8 stores into the packet. Addresses are computed by ALU64 add from the zero-extended u32 context fields. Rocq `exec_load` of a `Vlong` needs an `addr_map` hit; a plain integer lifter does not have that map. CO-RE may rewrite the three context offsets; the packet offsets (`+4..+7`, `+0`, `+9..+19`) are raw and not CO-RE.
- Helper: not used. No `CALL` opcode. `exec_step_external` is not involved.
- Map: declared (`workload`, hash, 2 entries, key 1, value 32) and present in BTF datasec. Not referenced by any instruction. No map fd, no map index, no `bpf_map_*` call. Do not treat toml `aot_addr` as a load.
- Loop: none in the object. Fifteen forward edges, all to `exit`. The C `for` is unrolled (`#pragma unroll`, bound 12). The C++ `loop` flag would be false. The projection still refuses the program for other reasons below.

## Conversion result

NOT CONVERTED.

`decode_ebpf` throws at slot 1, opcode `0x61`, before any IR or proof obligation is built. The failure is the missing LDX/STX class in `ebpf_decode.cpp`, not a bad length, a bad register, or a split LDDW. Calling that a successful `UNSUPPORTED` verdict would hide the throw. No `.alive` file is produced.

## Proof coverage

The projection that the gate can discharge does not include this program, even ignoring the decode throw.

`supported_insn` in `ebpf_project.cpp` returns true only for ALU64 `Mov`, `Add`, `Sub`, `Div`; `Exit`; `Ja`; and JMP64 `Jgt`. Against that filter:

- Inside the filter, if they were reached: slots 3, 4, 5, 13, 14, 15, 25, 26, 34, 35, 42, 43, 50, 51, 58, 59, 66, 72. Several of those ADD/MOV/JGT operands are values produced by loads or by shifts, which the projection never constructs. `entry_regs` tags r1 as a pointer, and `eval_alu` then sets `pointer_use` and the reason `bitvector use of a pointer register`. The gate treats `pointer_use` as blocked (`ebpf_project.cpp` around 922–927) and records `Verdict::Unsupported` rather than a proof.
- Outside the filter: every ALU32 slot (0, 10, 22, 23, 29), every LSH and OR (16–21), every JMP32 (12, 24, 30, 33, 38, 41, 46, 49, 54, 57, 62, 65, 69). `supported_insn` false means rule list `{"unsupported"}` and reason `opcode is outside the projection`. That is a gap in the projection, not a completed proof.
- Not representable: all 31 memory slots. The projection's `std::variant` has nowhere to put them. `exec_load` / `exec_store` exist in `ebpfBinSem.v` and were read; they are not in `supported_insn` and were not found in `Validation.v` by search. `Validation.v` itself was not read.

`alive2/tests/bpf/` contains `add64.c`, `alu32.c`, `arith.c`, `branch.c`, `shift.c`, `udiv.c`. Those bodies were not read, so this report does not claim they cover memcpy, loads, or stores.

No check was run on this object. The gate was not executed, because that would require a decoder this tree does not have for these bytes.

## Counterexample idea

Do not accept a translation that drops the stores and returns the initial r0, and do not accept a signed reading of slot 24.

1. Dropped memory. Let the u32 at `xdp_md.data` be `P` and `data_end` be `P+32`. Packet bytes: offset 4 holds `01 00 00 00`, offset 8 holds `0xAB`, offset 9 holds `0x00`. The object stores the first byte, sets r0 to 2 at slot 29, then slot 30 (`w4 u< 2`) exits. Result: r0 = 2 and the byte at `P+9` is `0xAB`. A translation with no store and r0 left at 0 yields r0 = 0 and `P+9` still `0x00`.

2. Signed `JLT` at slot 24. Same setup but the length bytes are `0d 00 00 00` (`n = 13`). Early checks pass (`data+32 == data_end`, difference `24`). Unsigned `0 u< 0xfffffff4` is true, so the object exits with r0 = 0 and no store. Signed `0 < -12` is false, so a signed model falls through, writes, and sets r0 to 2. One input, two different r0 values.

A 64-bit subtract in place of slot 10 does not separate these inputs: the preceding 64-bit `JGT` already forced `data+8 <= data_end` on zero-extended u32s, so the 32-bit subtract does not wrap on the paths that reach it.

## Gaps a later implementer has to close

- Teach `decode_ebpf` the MEM LDX/STX forms Rocq already accepts (`0x61`, `0x71`, `0x73` here), without inventing a second opcode map.
- Give the lifter a memory effect for zero-extending u32/u8 loads and u8 stores. Integer `BinOp` cannot stand in for that.
- Keep CO-RE byte-offset records on slots 1, 2, and 11 distinct from raw immediates. For this BTF the stored offsets already match `data` / `data_end`.
- Extend the projection past ALU64 `{mov,add,sub,div}` and JMP64 `jgt`. This object needs ALU32 add/sub/mov (zero-extend), ALU64 lsh/or, JMP32 unsigned `jlt` (including a negative immediate), and JMP32 `jeq`.
- Leave the unused map and `aot_addr` out of the instruction semantics.

STATUS: ISSUES
