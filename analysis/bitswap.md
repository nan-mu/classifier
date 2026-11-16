# bitswap observation

Observation report for a later implementer. It does not define a new ISA. Conversion result: **NOT CONVERTED**. No `.alive` file was emitted.

## Evidence

- Computed sha256 of `/Volumes/SSD/bs/build/bitswap/bpf.o`: `775dc8cf4a221765493bf915d79d54905e5f456c013943718d9237e20582a980` (8880 bytes). Matches the expected digest.
- ELF class ELF64, `EI_DATA` = 1 (little endian), `e_type` = REL, `e_machine` = EM_BPF, `e_entry` = 0. A relocatable file has no program headers; the entry is the function symbol, not `e_entry`.
- Commands: `/opt/homebrew/opt/llvm/bin/llvm-readelf -a` and `/opt/homebrew/opt/llvm/bin/llvm-objdump -h -r -t -d` on that path, plus a byte walk of the same file (section table, 8-byte slots, BTF, `.BTF.ext` core records).
- Notes: `/Volumes/SSD/bs/build/bitswap/bpf.toml` (`source` = `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/bitswap.c`, `[xdp].size` = 544). The C source and `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/exec_common.h` were read. `XDP_ABORTED` / `XDP_PASS` numeric macros were not found in that tree; the object immediates are 0 and 2.

## Executable sections

| section | shndx | flags | file off | size | role |
|---|---|---|---|---|---|
| `.text` | 2 | AX (0x6) | 0x40 | 0 | empty. Not the program. |
| `xdp` | 3 | AX (0x6) | 0x40 | 0x220 = 544 | the program |

`.text` and `xdp` share file offset 0x40 because `.text` has size 0. Symbol `bitswap` is GLOBAL FUNC, section `xdp`, value 0, size 544. One entry: `bitswap` at slot 0.

## Endianness, slots, LDDW

Instruction bytes are little-endian 64-bit slots: `opcode, regs, off:i16, imm:i32`. 544 / 8 = **68 slots, 68 instructions**. No opcode `0x18`. No LDDW. No second slot. Jump offsets below are the signed `off` field. Target = slot + 1 + off.

## Relocations, maps, BTF

There is **no** `.rel.xdp` and **no** `.rel.text`. Nothing in the 68 slots is an ELF relocation, an XPOST relocation, or a map-index reference.

Raw object symbols (`.symtab`):

- `bitswap` — function, section `xdp`, size 544
- `LICENSE` — object, section `license`, size 4, bytes `GPL\0` at file offset 0x260
- `workload` — object, section `.maps`, size 32, file offset 0x268, **32 zero bytes**

Those symbols are named only from debug/BTF relocations, not from instruction operands:

- `.rel.BTF`: `R_BPF_64_NODYLD32` at BTF offset 0x250 → `workload`; at 0x268 → `LICENSE`. These patch BTF datasec variable records (types t23 `.maps` and t24 `license`), not the program.
- `.rel.debug_addr`: `R_BPF_64_ABS64` to `xdp` (five), `LICENSE`, `workload`. DWARF addresses.
- `.rel.debug_info`, `.rel.debug_str_offsets`, `.rel.debug_frame`, `.rel.debug_line`: `R_BPF_64_ABS32` / `R_BPF_64_ABS64` to debug sections or `xdp`.
- `.rel.BTF.ext`: 27× `R_BPF_64_NODYLD32` to section symbol `xdp`.

CO-RE is not an ELF relocation on `xdp` and not an XPOST record. `.BTF.ext` core-relo (record size 16, section name off 221 = `xdp`, two records), also printed by llvm-objdump:

| insn file off | slot | type id | access string | kind | objdump |
|---|---|---|---|---|---|
| 0x8 | 1 | 17 `xdp_md` | `0:1` | 0 | `CO-RE <byte_off> struct xdp_md::data_end` |
| 0x10 | 2 | 17 `xdp_md` | `0:0` | 0 | `CO-RE <byte_off> struct xdp_md::data` |

Both instruction immediates are already 0. The `off` fields are already 4 and 0, matching BTF `xdp_md` members `data` at bit 0 and `data_end` at bit 32. This is a byte-offset annotation of a field load, not a map fd/index.

BTF map (not an instruction operand): var `workload` (t15) type t14 `{type, max_entries, key, value}`, datasec `.maps` size 0 in the type header, section bytes all zero. `bpf.toml` says `BPF_MAP_TYPE_HASH`, `max_entries` 2, key 1, value 32, `aot_addr` 0x40380314. `exec_common.h` says key 0 is input and key 1 is output for the harness. **No slot loads that map.** No `Plddw` with `PSEUDO_MAP_FD` / `PSEUDO_MAP_IDX` / `PSEUDO_MAP_VALUE` / `PSEUDO_MAP_IDX_VALUE`. Do not invent a lookup.

XPOST: this file is `elf64-bpf`, not Compact ELF V0. No `.xpost.meta`, `.xpost.image`, or `.xpost.mem`. No XPOST relocation. (`tooling/vendor/xpost-elf` was not applied to this object.)

## Real disassembly

`llvm-objdump -d` of section `xdp` (empty `.text` produced no instructions):

```
0000000000000000 <bitswap>:
       0:	b4 00 00 00 00 00 00 00	w0 = 0x0
       1:	61 14 04 00 00 00 00 00	w4 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [17] struct xdp_md::data_end (0:1)
       2:	61 11 00 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [17] struct xdp_md::data (0:0)
       3:	bf 17 00 00 00 00 00 00	r7 = r1
       4:	07 07 00 00 08 00 00 00	r7 += 0x8
       5:	2d 47 3d 00 00 00 00 00	if r7 > r4 goto +0x3d <L1>
       6:	71 13 05 00 00 00 00 00	w3 = *(u8 *)(r1 + 0x5)
       7:	71 16 04 00 00 00 00 00	w6 = *(u8 *)(r1 + 0x4)
       8:	71 15 06 00 00 00 00 00	w5 = *(u8 *)(r1 + 0x6)
       9:	71 12 07 00 00 00 00 00	w2 = *(u8 *)(r1 + 0x7)
      10:	1c 74 00 00 00 00 00 00	w4 -= w7
      11:	a6 04 37 00 18 00 00 00	if w4 < 0x18 goto +0x37 <L1>
      12:	64 03 00 00 08 00 00 00	w3 <<= 0x8
      13:	4c 63 00 00 00 00 00 00	w3 |= w6
      14:	64 05 00 00 10 00 00 00	w5 <<= 0x10
      15:	64 02 00 00 18 00 00 00	w2 <<= 0x18
      16:	4c 52 00 00 00 00 00 00	w2 |= w5
      17:	4c 32 00 00 00 00 00 00	w2 |= w3
      18:	16 02 30 00 00 00 00 00	if w2 == 0x0 goto +0x30 <L1>
      19:	b4 03 00 00 00 00 00 00	w3 = 0x0
      20:	71 15 0b 00 00 00 00 00	w5 = *(u8 *)(r1 + 0xb)
      21:	71 10 0a 00 00 00 00 00	w0 = *(u8 *)(r1 + 0xa)
      22:	71 14 09 00 00 00 00 00	w4 = *(u8 *)(r1 + 0x9)
      23:	71 16 08 00 00 00 00 00	w6 = *(u8 *)(r1 + 0x8)
<L0>:
      24:	54 06 00 00 ff 00 00 00	w6 &= 0xff
      25:	54 04 00 00 ff 00 00 00	w4 &= 0xff
      26:	64 04 00 00 08 00 00 00	w4 <<= 0x8
      27:	4c 64 00 00 00 00 00 00	w4 |= w6
      28:	54 00 00 00 ff 00 00 00	w0 &= 0xff
      29:	64 00 00 00 10 00 00 00	w0 <<= 0x10
      30:	4c 04 00 00 00 00 00 00	w4 |= w0
      31:	64 05 00 00 18 00 00 00	w5 <<= 0x18
      32:	4c 54 00 00 00 00 00 00	w4 |= w5
      33:	bf 45 00 00 00 00 00 00	r5 = r4
      34:	dc 05 00 00 20 00 00 00	r5 = be32 r5
      35:	54 05 00 00 0f 0f 0f 0f	w5 &= 0xf0f0f0f
      36:	64 05 00 00 04 00 00 00	w5 <<= 0x4
      37:	dc 04 00 00 40 00 00 00	r4 = be64 r4
      38:	77 04 00 00 24 00 00 00	r4 >>= 0x24
      39:	54 04 00 00 0f 0f 0f 0f	w4 &= 0xf0f0f0f
      40:	4c 54 00 00 00 00 00 00	w4 |= w5
      41:	bc 45 00 00 00 00 00 00	w5 = w4
      42:	54 05 00 00 33 33 33 33	w5 &= 0x33333333
      43:	64 05 00 00 02 00 00 00	w5 <<= 0x2
      44:	74 04 00 00 02 00 00 00	w4 >>= 0x2
      45:	54 04 00 00 33 33 33 33	w4 &= 0x33333333
      46:	4c 54 00 00 00 00 00 00	w4 |= w5
      47:	bc 45 00 00 00 00 00 00	w5 = w4
      48:	54 05 00 00 55 55 55 55	w5 &= 0x55555555
      49:	64 05 00 00 01 00 00 00	w5 <<= 0x1
      50:	74 04 00 00 01 00 00 00	w4 >>= 0x1
      51:	54 04 00 00 55 55 55 55	w4 &= 0x55555555
      52:	bc 46 00 00 00 00 00 00	w6 = w4
      53:	4c 56 00 00 00 00 00 00	w6 |= w5
      54:	bc 65 00 00 00 00 00 00	w5 = w6
      55:	74 05 00 00 18 00 00 00	w5 >>= 0x18
      56:	bc 60 00 00 00 00 00 00	w0 = w6
      57:	74 00 00 00 10 00 00 00	w0 >>= 0x10
      58:	bc 64 00 00 00 00 00 00	w4 = w6
      59:	74 04 00 00 08 00 00 00	w4 >>= 0x8
      60:	04 03 00 00 01 00 00 00	w3 += 0x1
      61:	ae 23 da ff 00 00 00 00	if w3 < w2 goto -0x26 <L0>
      62:	73 51 0b 00 00 00 00 00	*(u8 *)(r1 + 0xb) = w5
      63:	73 01 0a 00 00 00 00 00	*(u8 *)(r1 + 0xa) = w0
      64:	73 41 09 00 00 00 00 00	*(u8 *)(r1 + 0x9) = w4
      65:	73 61 08 00 00 00 00 00	*(u8 *)(r1 + 0x8) = w6
      66:	b4 00 00 00 02 00 00 00	w0 = 0x2
<L1>:
      67:	95 00 00 00 00 00 00 00	exit
```

Slot 61 `off` bytes `da ff` are −38, not 65498. Target 61+1−38 = 24.

## Instruction list

Jump slots and targets:

| slot | op | off | target | taken when | edge |
|---|---|---|---|---|---|
| 5 | jmp64 `jgt` r7, r4 | +61 | 67 | unsigned r7 > r4 | forward, to exit |
| 11 | jmp32 `jlt` w4, 0x18 | +55 | 67 | unsigned w4 < 24 | forward, to exit |
| 18 | jmp32 `jeq` w2, 0 | +48 | 67 | w2 == 0 | forward, to exit |
| 61 | jmp32 `jlt` w3, w2 | −38 | 24 | unsigned w3 < w2 | **back edge** |

Other slots fall through. Exit is only slot 67.

CFG leaders: 0, 6, 12, 19, 24, 62, 67.

| block | slots | successor |
|---|---|---|
| entry | 0–5 | 67 or 6 |
| header check | 6–11 | 67 or 12 |
| param assemble | 12–18 | 67 or 19 |
| prelude | 19–23 | 24 |
| loop | 24–61 | 24 or 62 |
| store | 62–66 | 67 |
| exit | 67 | return r0 |

What the object does, from the bytes plus `bitswap.c` / `exec_common.h` (not a new ISA):

- Slot 0 sets w0 = 0. Failure paths leave that and exit.
- Slots 1–2 load `xdp_md.data_end` and `xdp_md.data` as zero-extending u32. Slot 2 **overwrites r1**. The ctx pointer is dead after that. Later packet accesses use the integer `data` pointer in r1.
- Slots 3–5: r7 = data+8; 64-bit unsigned compare against data_end. Taken → exit, r0 = 0, no store.
- Slots 6–9 and 12–17 assemble a little-endian u32 from data[4..7] into w2 (`param`).
- Slot 10 is 32-bit `w4 -= w7` (low 32 bits of data_end − (data+8)). Slot 11 rejects that difference if it is < 24. So a passing frame needs `data_end - data >= 32`.
- Slot 18 rejects `param == 0` before any payload load.
- Slots 20–23 load payload bytes data[8..11] **once**, before the loop header. They are not inside the back edge.
- Slots 24–53 are `__builtin_bitreverse32` of that word (nibble swap via `be32`/`be64`, then 2-bit and 1-bit swaps). w6 holds the reversed u32.
- Slots 54–59 split w6 into bytes but do not store yet. Slot 60 increments the counter in w3.
- Slot 61 branches to **24**, not to 20. Later iterations reassemble the previous w6 from w6/w4/w0/w5. They do not reload the packet. The four stores (slots 62–65) run once, after the loop, little-endian at data[8..11]. Slot 66 sets w0 = 2.

The source loop is `load_u32` / `store_u32` each iteration. This object forwarded the store: one load, `param` reversals in registers, one store. An implementer who re-reads memory on the back edge, or who stores on every iteration, is not following this object.

Registers touched: r0, r1, r2, r3, r4, r5, r6, r7. r8, r9, r10 unused. No call.

## Classification against code that was read

C++ decoder (`alive2/src/ebpf_decode.cpp`): classes are `kAlu=0x04`, `kJmp=0x05`, `kJmp32=0x06`, `kAlu64=0x07`. Anything else hits `unsupported class` (`ebpf_decode.cpp` lines 164–167). `decode_ebpf` throws at the first such slot, so a run stops at **slot 1, opcode 0x61**. The table below is the opcode switch that was read, not a successful `decode_ebpf` of this file.

`EbAlu::Op` (`alive2/src/ebpf.h` lines 14–16) is Add, Sub, Mul, Div, Mod, Or, And, Lsh, Rsh, Neg, Xor, Mov, Arsh, Sdiv, Smod, Movsx. There is no End. Opcode `0xdc` has class ALU, code `0xd0`, and the `0x08` bit set. The ALU switch's default (`ebpf_decode.cpp` lines 99–115) rejects it as an unsupported ALU opcode. The `0x08` bit is `BPF_TO_BE`, not a register source; the C++ decoder treats that bit as `kSrc` for every ALU op.

Rocq decoder that was read: `alive2/rocq/upstream/theories/ebpfDecoder.v` `decode_insn` / `find_instr`. `find_instr` only consumes two slots for opcode `0x18` (`ebpfDecoder.v` lines 268–276). That path is unused here.

| slots | bytes | C++ `decode_ebpf` | Rocq `decode_insn` (read) |
|---|---|---|---|
| 0, 19, 66 | `0xb4` ALU32 MOV K | `EbAlu::Mov` W32 imm. Imms 0, 0, 2. src nibble is 0. | `Palu MOV W32 (inr imm)` |
| 1, 2 | `0x61` LDX MEM W | **reject**, class 0x1 | `Pload Word dst src off`. Offsets 4 and 0, imm 0. |
| 6–9, 20–23 | `0x71` LDX MEM B | **reject**, class 0x1 | `Pload Byte`. Offsets 5,4,6,7 then 11,10,9,8. All base r1. |
| 3, 33 | `0xbf` ALU64 MOV X | `EbAlu::Mov` W64 reg | `Palu MOV W64 (inl src)` |
| 4 | `0x07` ALU64 ADD K | `EbAlu::Add` W64 imm 8 | `Palu ADD W64` |
| 10 | `0x1c` ALU32 SUB X | `EbAlu::Sub` W32 r4, r7 | `Palu SUB W32` |
| 12, 14, 15, 26, 29, 31, 36, 43, 49 | `0x64` ALU32 LSH K | `EbAlu::Lsh` W32. Imms 8, 16, 24, 8, 16, 24, 4, 2, 1. | `Palu LSH W32` |
| 13, 16, 17, 27, 30, 32, 40, 46, 53 | `0x4c` ALU32 OR X | `EbAlu::Or` W32 | `Palu OR W32` |
| 24, 25, 28, 35, 39, 42, 45, 48, 51 | `0x54` ALU32 AND K | `EbAlu::And` W32. Imms `0xff`, `0x0f0f0f0f`, `0x33333333`, `0x55555555`. | `Palu AND W32` |
| 34 | `0xdc` imm `0x20` | **reject**, ALU code 0xd | class ALU32, src bit set, src reg R0, imm 32 → `Palu (END BE32 S32) W32` (`ebpfDecoder.v` lines 91–105) |
| 37 | `0xdc` imm `0x40` | **reject**, same | same opcode, imm 64 → `Palu (END BE32 S64) W64`. There is no `BE64` constructor (`ebpfSyntax.v` lines 122–126). ALU64+TO_BE is `None` in that match; this object does not use that encoding. |
| 38 | `0x77` ALU64 RSH K | `EbAlu::Rsh` W64 imm `0x24` | `Palu RSH W64` |
| 41, 47, 52, 54, 56, 58 | `0xbc` ALU32 MOV X | `EbAlu::Mov` W32 reg | `Palu MOV W32` |
| 44, 50, 55, 57, 59 | `0x74` ALU32 RSH K | `EbAlu::Rsh` W32. Imms 2, 1, 24, 16, 8. | `Palu RSH W32` |
| 60 | `0x04` ALU32 ADD K | `EbAlu::Add` W32 imm 1 | `Palu ADD W32` |
| 5 | `0x2d` JMP64 JGT X | `EbJmp::Jgt` W64 | `Pjmpcmp (GT Unsigned) W64` off +61 |
| 11 | `0xa6` JMP32 JLT K | `EbJmp::Jlt` W32 imm `0x18` | `Pjmpcmp (LT Unsigned) W32` |
| 18 | `0x16` JMP32 JEQ K | `EbJmp::Jeq` W32 imm 0 | `Pjmpcmp EQ W32` |
| 61 | `0xae` JMP32 JLT X | `EbJmp::Jlt` W32 | `Pjmpcmp (LT Unsigned) W32` off −38 |
| 62–65 | `0x73` STX MEM B | **reject**, class 0x3 | `Pstore Byte dst (inl src) off`. Bases r1; src regs r5, r0, r4, r6; offsets 11, 10, 9, 8. |
| 67 | `0x95` | `EbJmp::Exit` (class JMP, code 0x90, dst=src=off=imm=0) | `Pret` |

Every slot is in that table. None is a helper call (`0x85` / `Pcall` absent). None is atomic, JA, DIV, or LDDW.

## Semantic rules actually read

Upstream theories, unmodified per `alive2/rocq/README.md`. Commit pin in `alive2/rocq/PIN` was not re-hashed here.

Read:

- `ebpfSyntax.v` lines 99–245: `sizeOp`, `endOp` (LE32, BE32, LE64 only), `endSize`, `aluOp` including `END`, `cmpOp`, `pseudo_ptr_ty`, `Pload` / `Pstore` / `Palu` / `Pjmpcmp` / `Pret`. `Plddw` src-reg meanings for map fd vs map index are in the comment at lines 204–221 and `decode_lddw_insn` (`ebpfDecoder.v` lines 235–246). Unused by this object.
- `ebpfDecoder.v` `decode_insn` lines 29–233 and `find_instr` lines 257–285, as cited above.
- `ebpfBinSem.v`:
  - `swab16` / `swab32` / `swab64` / `swapn` / `eval_end_trunction` / `eval_end` lines 255–329. `BE32` swaps with `swapn` only when `Archi.big_endian` is false; otherwise it zero-extends (`S16`/`S32`) or returns the value (`S64`). `LE64` always calls `swapn`. **`Archi.big_endian` was not read** (CompCert, not in this tree). The ELF being little-endian does not set that flag.
  - `eval_alu32` / `eval_alu64` / `exec_alu` lines 331–390. ALU32 results go through `Val.longofintu` (zero-extend to 64), except `END`, which returns `eval_end` directly. Shifts use `eval_shift_mask`. Same-register `SUB`/`XOR` are forced to 0; this object has no same-register SUB/XOR.
  - `eval_cmp32` / `eval_cmp64` / `exec_jmpcmp` lines 392–498. Unsigned `GT`/`LT`/`EQ`. Imm on the 64-bit compare is `int64_of_int` (sign-extend). The only 64-bit compare here is register/register. `eval_cmp_static` makes `LT Unsigned` of immediate 0 constantly false; slot 11's immediate is 24, so it does not hit that shortcut.
  - `exec_load` lines 575–589: a `Vlong` base is `cast_i2p` of base+signed offset (`cast_i2p` lines 512–522, Stuck if no region contains the address); a `Vptr` base is `Val.offset_ptr`. Loads are `Mint8unsigned` / `Mint32`, then `load_value_casting` zero-extends a `Vint` to `Vlong`.
  - `exec_store` lines 633–646: `Val.offset_ptr` on the base, then `storev_unaligned` of `Mint8unsigned`. **No `cast_i2p` branch.** `Val.offset_ptr` itself was not read. After slot 2, r1 is the integer data pointer, so both the later loads and the stores are in the integer-address case. Loads need an `addr_map` hit or they are `Stuck`. Stores do not consult `addr_map` in the code that was read.
  - `exec_instr` lines 888–905. `Pcall` is the `_ => Stuck` case. No call in this object.
- C++ lifter rules: `alive2/src/ebpf_lift.cpp` `build_blocks` (loop if a jump target is `<=` the jump slot, lines 228–229), `emit_alu` / `emit_wide` / `emit_narrow` / `shift` / `emit_cmp` / `icmp_cond` (lines 516–694). ALU32 is trunc to i32, op, `zext` to i64. Shifts mask the amount with 31 or 63 unless `LiftBug::ShiftWithoutMask`. W64 immediates are sign-extended unless `LiftBug::ImmNoSignExtend`. W32 immediates are zero-extended. `init_regs` marks an unseeded r1 and r10 as poison with origin Pointer (lines 315–321).
- Gate: `alive2/src/ebpf_gate.cpp` only sees `EbAlu` / `EbJmp`. It rejects r10 use. It does not know memory. It is never reached if `decode_ebpf` throws (`ebpf_project.cpp` lines 851–856).
- Exhibit/project loop refusal: `ebpf_project.cpp` lines 872–879 and `ebpf_exhibit.cpp` lines 246–267. A back edge is symbolic `UNSUPPORTED` and is not unrolled on that path. `supported-scope-equivalent` does not cover loops, memory, maps, helpers, or pointer arithmetic. `ebpf_run.cpp` lines 52–55 can unroll only after a successful decode, and only when the caller passes a non-zero bound.
- `alive2/rocq/README.md`: the symbolic check projects `eval_alu64`, `eval_div_u64`, and `exec_jmpcmp` for **MOV64, ADD64, SUB64, DIV64, JGT64, JA, EXIT only**. Anything else is `UNSUPPORTED`, and that is not a pass. The concrete suite compares registers on programs whose memory stays empty. This object is outside both.
- `doc/观察.md`: observation forms are Helper, Branch, Return, MapWrite, PacketWrite. That is the eBPF/RV32 matcher vocabulary. The C++ lifter does not build those forms.
- `doc/局限.md` section 循环: a loop is at most a weak match; first-iteration observations do not imply later iterations. It names `bitswap` only for a 32-bit reading of branches in that matcher. That is not an Alive2 proof and not a conversion.

Not read, so not used as rules: `ebpfState.v`, `CMemoryModel.v`, `GlobalSem.v`, `SCLanguage.v`, `Validation.v`, `eval_shift_mask`'s definition (it is called, the body was not opened), CompCert `Archi.big_endian`, `Val.offset_ptr`, `Val.longofintu`.

## IR mapping (existing C++ lifter only)

`decode_ebpf` throws at slot 1. `lift_ebpf` is not reachable. No Alive2 `Function` exists for this object. Do not pretend the rows below were produced.

If the memory and `0xdc` slots were absent, the lifter that was read would emit:

| op | IR in `ebpf_lift.cpp` |
|---|---|
| ALU32 MOV imm | i32 const, `zext` to i64 |
| ALU32 MOV reg | trunc src to i32, `zext` to i64 |
| ALU32 ADD/SUB/OR/AND | trunc both sides, i32 `BinOp`, `zext` to i64 |
| ALU32 LSH/RSH | same, shift amount `And` 31, `Shl` or `LShr` |
| ALU64 MOV reg | the source value itself (`bare_mov`) |
| ALU64 ADD imm 8 | i64 `Add`, immediate sign-extended |
| ALU64 RSH imm 0x24 | i64 `LShr`, amount masked with 63 |
| jmp64 JGT | `ICmp` `UGT` on i64, branch to the jump target then the fall-through block |
| jmp32 JLT/JEQ | trunc to i32, `ICmp` `ULT` or `EQ`, imm via `c32` of the zero-extended immediate |
| EXIT | `Return` of r0 as i64 |

There is no load, store, packet memory, bswap, or `END` constructor in `EbInsn` or in `emit_alu`. Mapping `0xdc` onto `Rsh` or onto a 32-bit `And` would be a new invented op, and it is the wrong width for slot 37 (see the counterexample).

The back edge at slot 61 sets `LiftInfo.loop`. `build_blocks` would place phis on the header because the target is `<=` the jump. The project/exhibit path still stops with reason `back edge` and does not unroll. That refusal is not a successful conversion.

r1 starts as a pointer-origin poison if the symbolic init is used (`init_regs`). This object replaces r1 with a loaded u32 at slot 2 before any ALU on it. The lifter cannot see that replacement. Treating slots 3–5 as pointer arithmetic on the original ctx is a mis-read of this object: slot 5 compares the loaded data pointer plus 8 with the loaded data_end, both zero-extended u32 values. Slot 10 then subtracts them at 32-bit width.

## Memory, helper, map, loop

- **Memory: required.** 2× u32 load from ctx (slots 1–2), 8× u8 load from the data pointer (slots 6–9 and 20–23), 4× u8 store (slots 62–65). No stack slot, no r10.
- **Helper: no.** No call. `bpf_helpers.h` is included by the C file; this function does not call a helper.
- **Map: object present, instruction absent.** `workload` is a BTF hash map for the harness. The 68 slots do not reference it. `aot_addr` is notes metadata, not an operand. Not a map-index LDDW.
- **Loop: yes.** One back edge, slot 61 → slot 24. Carried in registers: w3 (counter), w2 (bound, invariant), and w6/w4/w0/w5 (the previous reversed word, split and reassembled). Packet memory is not carried. Bound is the packet u32 `param`. `param == 0` is a separate exit at slot 18; the back-edge test `w3 < w2` is not reached with w2 = 0.

## Conversion result

**NOT CONVERTED.**

`decode_ebpf` rejects slot 1 (`unsupported class in opcode 0x61`) and, independently, would reject slots 6–9, 20–23, 34, 37, and 62–65. The lifter, the symbolic gate, and `ebpf-exhibit --check` never see a program. Calling the missing memory/`END` model `UNSUPPORTED` and then a success would contradict `alive2/rocq/README.md` and `ebpf_exhibit.cpp` line 245: `UNSUPPORTED` is not a pass.

## Proof coverage

No proof in the files that were read covers this object.

- Symbolic equivalence is limited to MOV64, ADD64, SUB64, DIV64, JGT64, JA, and EXIT. This program's ALU32 ops, OR/AND/LSH/RSH, JLT, JEQ, `END`, loads, stores, and the back edge are outside that list.
- Concrete Rocq-vs-lifter rows keep memory empty and do not prove the lifter (`alive2/rocq/README.md`).
- A back edge is recorded as `UNSUPPORTED`, not checked (`ebpf_project.cpp`, `ebpf_exhibit.cpp`).
- `eval_end` for `BE32`/`S64` was read, but not a theorem that slot 37 plus slot 38 implements the high half of `bitreverse32`, and not the value of `Archi.big_endian`.
- `exec_load` / `exec_store` were read. They are not connected to this ELF, and store does not share load's integer-address path.
- `doc/局限.md`'s remark that `bitswap` branches matched in the classifier is a different system. It is not a proof of this loop and it does not convert the object.

## Counterexample idea

Not run on the lifter. The lifter cannot decode the file. The numbers are a replay of the ALU/END sequence under the `swab32` / `swab64` definitions in `ebpfBinSem.v` lines 268–297, assuming `Archi.big_endian = false` so `BE32` takes `swapn`. If that flag is true, `eval_end` does not swap and both results below are wrong for a different reason.

Frame of at least 32 bytes. Bytes 0–3 ignored. Bytes 4–7 are `param` little-endian. Bytes 8–11 are the payload word little-endian. r0 on entry is cleared by slot 0.

1. **`be64` is not `be32`.** `param = 1`, payload bytes `80 00 00 00` (word `0x80`). One reversal. Slot 66 sets r0 = 2. Stored bytes must be `00 00 00 01` (word `0x01000000`). Executing slot 37 as a 32-bit swap (the imm-64 size ignored) yields stored word 0. Same split on word `0xffffffff`: swapped-as-64 stores `ff ff ff ff`; swapped-as-32 stores `f0 f0 f0 f0`.

2. **The back edge matters, and it does not reload.** `param = 2`, same payload `80 00 00 00`. Two reversals restore `80 00 00 00`, r0 = 2. Taking the body once and falling out of slot 61 stores `00 00 00 01`. Jumping the back edge to slot 20 instead of slot 24 is also wrong: the object does not reload, and the stores are only slots 62–65.

3. **`param = 0` must not store.** Bytes 4–7 are 0. Slot 18 jumps to 67 with r0 still 0 and bytes 8–11 unchanged. Entering slot 19 anyway would load, reverse once, fail `w3 < w2`, and store. The early exit is load-bearing because the loop test is after the first body.

A short frame (`data+8 > data_end`, or the 32-bit difference < 24) also exits with r0 = 0 and no store. Those compares are 64-bit then 32-bit on zero-extended u32 loads; collapsing both to the same width is a separate bug, not demonstrated numerically here.

## Status

ISSUES
