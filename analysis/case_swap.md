# case_swap observation

Produce an observation report for `case_swap` so a later implementer can compile it, without inventing a shared ISA. This file records the ELF that was disassembled, the rules that were actually read, and why the existing C++ lifter does not convert the program. It is not a translation and it is not a proof.

Conversion result: **NOT CONVERTED**. No `.alive` file is emitted.

## Evidence

Commands actually run:

- `shasum -a 256 /Volumes/SSD/bs/build/case_swap/bpf.o`
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -a`, `-S -W`, `-r -W`, `-s -W` on that file
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r --section-headers --syms -s` and `-d --no-show-raw-insn -r --symbolize-operands --section=xdp1`
- A local byte walk of section `xdp1` (file offset `0x40`, size `0x348`) that classifies each opcode with the class/code masks from `alive2/src/ebpf_decode.cpp` and `alive2/rocq/upstream/theories/ebpfDecoder.v`. That walk is a check of those rules, not a lifter.

SHA256 computed: `2c93af665233795f5a7df5db2d301736469ef71e6a7cc355a27c96e7702c87b2`. It matches the expected digest. The file was read only after that check.

Notes read: `/Volumes/SSD/bs/build/case_swap/bpf.toml` (source path, the same assembly, map `rxcnt`, and eight CO-RE rows). C source read for intent only: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/case_swap.c`. The bytes below are from the ELF, not from the `.c` file. Where the two differ, the ELF wins.

## ELF

`ET_REL`, `ELF64`, `EM_BPF`, little endian (`EI_DATA` = 2's complement, little endian). Entry point `0`. No program headers. 27 section headers at file offset `0x3360`. Section-name strings are in `.strtab` (index 1).

Executable sections (`SHF_ALLOC|SHF_EXECINSTR`):

| Index | Name | Type | File off | Size | Align | Flags |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | `.text` | PROGBITS | `0x40` | **0** | 4 | AX |
| 3 | `xdp1` | PROGBITS | `0x40` | **0x348** | 8 | AX |

`.text` is empty. It is not the program. The only nonzero executable section is `xdp1`. Both share file offset `0x40` because `.text` contributes no bytes.

Symbol: `xdp_prog1`, `FUNC`, global, section `xdp1`, value `0`, size `840` (`0x348`). One entry. No other function symbol.

`0x348` bytes = **105** eight-byte slots, indices `0` through `104`. Slot `20` is `LDDW` and consumes slot `21` (second word is eight zero bytes). Logical instructions: **104**. `llvm-objdump` numbers slots and skips index `21`.

Other non-debug sections used below: `maps` (20 bytes, `WA`), `license` (`GPL\0`, 4 bytes), `.BTF` (`0x969` bytes at file `0x1004`), `.BTF.ext` (`0x66c` bytes at file `0x1970`), `.relxdp1` (one relocation).

## Relocations, map, BTF, endianness

Program relocation, and only that one (`.relxdp1`, `SHT_REL`, info = section `xdp1`):

| Offset | Type | Symbol | Addend field |
| --- | --- | --- | --- |
| `0xa0` | `R_BPF_64_64` (type 1) | `rxcnt` (object, section `maps`, size 20, value 0) | none (`SHT_REL`) |

That offset is slot `20`, the `LDDW`. Raw encoding: opcode `0x18`, regs byte `0x01` so `dst=r1`, `src=r0`, offset `0`, both immediates `0`, second-slot reserved word `0`. In the Rocq decoder this src nibble is `PSEUDO_Constant`, not `PSEUDO_MAP_FD` (src 1), not `PSEUDO_MAP_IDX` (src 5), not `PSEUDO_MAP_VALUE` (src 2), not `PSEUDO_MAP_IDX_VALUE` (src 6). The map identity is the ELF relocation, not a map-index immediate. The file's constant is `0` until a loader applies `R_BPF_64_64` and substitutes the `rxcnt` object. Do not treat the raw `0` as the map fd, and do not treat this as a map-index reference.

No string `XPOST` exists under `alive2/src` or `alive2/rocq` (searched). Nothing in this object is labeled that way. CO-RE field fixups are not ELF relocations against `xdp1`. They are eight `BPF_CORE_FIELD_BYTE_OFFSET` records (kind `0`) in `.BTF.ext`, and the same eight rows in `bpf.toml` `[CORE]`. The instruction offset fields in the object are already the vmlinux byte offsets; a loader may still patch them from these records.

`.BTF` magic `0xeb9f`, version 1, header 24, type length `0x34c`, string length `0x605`. Strings include `xdp_prog1`, `xdp_md`, `ethhdr`, `iphdr`, `udphdr`, `rxcnt`, `bpf_map_def`, `maps`, `LICENSE`. `.rel.BTF` has two `R_BPF_64_NODYLD32` entries: `LICENSE` at BTF offset `0x344`, `rxcnt` at `0x35c`. Those patch BTF datasec variable offsets, not `xdp1`. `.rel.BTF.ext` is 99 times `R_BPF_64_NODYLD32` against the section symbol `xdp1` (insn-offset fields inside the ext section). Debug relocations (`R_BPF_64_ABS32` / `R_BPF_64_ABS64` against `.debug_*`, plus `rxcnt` and `LICENSE` in `.rel.debug_addr`) are not program references.

Map image at `maps`, 20 bytes, little endian: `type=2` (`BPF_MAP_TYPE_ARRAY`), `key_size=4`, `value_size=8`, `max_entries=256`, `map_flags=0`. Symbol `rxcnt`. `bpf.toml` agrees, and estimates 2048 value bytes. BTF strings name the `bpf_map_def` fields; the type graph itself was not walked field by field.

License section: `GPL`.

Endianness that matters for this object:

- ELF and the instruction encoding are little endian (opcode is the first byte of each slot).
- `alive2/rocq/upstream/validator/Extraction.v` lines 13–14 extract `Archi.ptr64` as true and `Archi.big_endian` as false. `eval_end` for `BE32` therefore takes the swap arm, not the truncate arm (`ebpfBinSem.v` lines 318–324).
- CompCert `decode_val` / `encode_val` were not read. Halfword and word packet accesses are only equivalent to the C source if memory is little endian. The checksum's explicit byte loads do not depend on that; the ethertype compare and the `daddr` store do.

## Real disassembly

`llvm-objdump -d --no-show-raw-insn -r --symbolize-operands --section=xdp1`. CO-RE lines are objdump's rendering of `.BTF.ext`, not extra instructions. `<L0>` is slot `27`. `<L1>` is slot `104`.

```
0000000000000000 <xdp_prog1>:
       0:	w0 = 0x1
       1:	w2 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [2] struct xdp_md::data_end (0:1)
       2:	w8 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [2] struct xdp_md::data (0:0)
       3:	r6 = r8
       4:	r6 += 0xe
       5:	if r6 > r2 goto +0x62 <L1>
       6:	w1 = *(u16 *)(r8 + 0xc)
		0000000000000030:  CO-RE <byte_off> [8] struct ethhdr::h_proto (0:2)
       7:	if w1 != 0x8 goto +0x60 <L1>
       8:	r7 = r8
       9:	r7 += 0x22
      10:	if r7 > r2 goto +0x5d <L1>
      11:	w1 = *(u8 *)(r6 + 0x9)
		0000000000000058:  CO-RE <byte_off> [15] struct iphdr::protocol (0:7)
      12:	if w1 != 0x11 goto +0x5b <L1>
      13:	r1 = r8
      14:	r1 += 0x2a
      15:	if r1 > r2 goto +0x58 <L1>
      16:	w1 = 0x11
      17:	*(u32 *)(r10 - 0x4) = w1
      18:	r2 = r10
      19:	r2 += -0x4
      20:	r1 = 0x0 ll
		00000000000000a0:  R_BPF_64_64	rxcnt
      22:	call 0x1
      23:	if r0 == 0x0 goto +0x3 <L0>
      24:	r1 = *(u64 *)(r0 + 0x0)
      25:	r1 += 0x1
      26:	*(u64 *)(r0 + 0x0) = r1
<L0>:
      27:	w1 = *(u16 *)(r8 + 0x0)
      28:	w2 = *(u16 *)(r8 + 0x6)
      29:	*(u16 *)(r8 + 0x0) = w2
      30:	w2 = *(u16 *)(r8 + 0x8)
      31:	w3 = *(u16 *)(r8 + 0x2)
      32:	*(u16 *)(r8 + 0x8) = w3
      33:	*(u16 *)(r8 + 0x2) = w2
      34:	w2 = *(u16 *)(r8 + 0xa)
      35:	w3 = *(u16 *)(r8 + 0x4)
      36:	*(u16 *)(r8 + 0xa) = w3
      37:	*(u16 *)(r8 + 0x6) = w1
      38:	*(u16 *)(r8 + 0x4) = w2
      39:	w1 = 0xa7100cb
      40:	*(u32 *)(r6 + 0x10) = w1
		0000000000000140:  CO-RE <byte_off> [15] struct iphdr::<anon 9>.<anon 0>.daddr (0:9:0:1)
      41:	w1 = 0x0
      42:	*(u16 *)(r6 + 0xa) = w1
		0000000000000150:  CO-RE <byte_off> [15] struct iphdr::check (0:8)
      43:	w3 = *(u8 *)(r8 + 0xe)
      44:	w3 <<= 0x8
      45:	w2 = *(u8 *)(r8 + 0xf)
      46:	w3 |= w2
      47:	w2 = *(u8 *)(r8 + 0x10)
      48:	w2 <<= 0x8
      49:	w4 = *(u8 *)(r8 + 0x11)
      50:	w2 |= w4
      51:	w2 += w3
      52:	w3 = *(u8 *)(r8 + 0x12)
      53:	w3 <<= 0x8
      54:	w4 = *(u8 *)(r8 + 0x13)
      55:	w3 |= w4
      56:	w2 += w3
      57:	w3 = *(u8 *)(r8 + 0x14)
      58:	w3 <<= 0x8
      59:	w4 = *(u8 *)(r8 + 0x15)
      60:	w3 |= w4
      61:	w2 += w3
      62:	w3 = *(u8 *)(r8 + 0x16)
      63:	w3 <<= 0x8
      64:	w4 = *(u8 *)(r8 + 0x17)
      65:	w3 |= w4
      66:	w2 += w3
      67:	w3 = *(u8 *)(r8 + 0x18)
      68:	w3 <<= 0x8
      69:	w4 = *(u8 *)(r8 + 0x19)
      70:	w3 |= w4
      71:	w2 += w3
      72:	w4 = *(u8 *)(r8 + 0x1a)
      73:	w4 <<= 0x8
      74:	w3 = *(u8 *)(r8 + 0x1b)
      75:	w4 |= w3
      76:	w3 = *(u8 *)(r8 + 0x20)
      77:	w3 <<= 0x8
      78:	w5 = *(u8 *)(r8 + 0x21)
      79:	w3 |= w5
      80:	w5 = *(u8 *)(r8 + 0x1e)
      81:	w5 <<= 0x8
      82:	w0 = *(u8 *)(r8 + 0x1f)
      83:	w5 |= w0
      84:	w2 += w4
      85:	w4 = *(u8 *)(r8 + 0x1d)
      86:	w0 = *(u8 *)(r8 + 0x1c)
      87:	w0 <<= 0x8
      88:	w0 |= w4
      89:	w2 += w0
      90:	w2 += w5
      91:	w2 += w3
      92:	w3 = w2
      93:	w3 >>= 0x10
      94:	w2 &= 0xffff
      95:	w2 += w3
      96:	w3 = w2
      97:	w3 >>= 0x10
      98:	w3 += w2
      99:	w3 ^= -0x1
     100:	r3 = be16 r3
     101:	*(u16 *)(r6 + 0xa) = w3
		0000000000000328:  CO-RE <byte_off> [15] struct iphdr::check (0:8)
     102:	*(u16 *)(r7 + 0x6) = w1
		0000000000000330:  CO-RE <byte_off> [22] struct udphdr::check (0:3)
     103:	w0 = 0x3
<L1>:
     104:	exit
```

Objdump prints slot `39` as `w1 = 0xa7100cb`. The immediate bytes at file `0x40+0x138` are `b4 01 00 00 cb 00 71 0a`, so the imm is `0x0a7100cb` (leading zero dropped in the print). That is `bpf_htonl(0xcb00710a)` already folded. On a little-endian word store it is the bytes `cb 00 71 0a`, the address `203.0.113.10` from the C comment. Do not re-swap this immediate.

## Entries and instruction list

Entry: `xdp_prog1` at slot `0` of `xdp1`. Failure sink `<L1>` is slot `104` (`exit`). `<L0>` is slot `27`, the fall-through of the null check and the target of slot `23`.

Jump slots (the only control flow; every offset is a signed 16-bit field; target = slot + 1 + offset):

| Slot | Byte off | Opcode | Kind | Target |
| --- | --- | --- | --- | --- |
| 5 | `0x28` | `0x2d` | JMP64 `JGT` `r6 > r2` +`0x62` | 104 |
| 7 | `0x38` | `0x56` | JMP32 `JNE` `w1 != 8` +`0x60` | 104 |
| 10 | `0x50` | `0x2d` | JMP64 `JGT` `r7 > r2` +`0x5d` | 104 |
| 12 | `0x60` | `0x56` | JMP32 `JNE` `w1 != 0x11` +`0x5b` | 104 |
| 15 | `0x78` | `0x2d` | JMP64 `JGT` `r1 > r2` +`0x58` | 104 |
| 23 | `0xb8` | `0x15` | JMP64 `JEQ` `r0 == 0` +3 | 27 |
| 104 | `0x340` | `0x95` | EXIT | — |

No `JA`. No backward edge. No jump lands on slot `21` (the `LDDW` trailer). Slot indices, not a compacted instruction stream, are what the offsets count.

Opcode histogram over the 104 logical instructions (one count for the `LDDW`, slot `21` not counted):

| Opcode | n | Class | C++ `decode_ebpf` | Rocq `decode_insn` / `decode_lddw_insn` |
| --- | --- | --- | --- | --- |
| `0xb4` | 5 | ALU32 MOV K | accept `EbAlu::Mov` W32 | `Palu MOV W32` |
| `0xbc` | 2 | ALU32 MOV X | accept | `Palu MOV W32` |
| `0x0c` | 11 | ALU32 ADD X | accept `Add` | `Palu ADD W32` |
| `0x4c` | 10 | ALU32 OR X | accept `Or` | `Palu OR W32` |
| `0x64` | 10 | ALU32 LSH K | accept `Lsh` | `Palu LSH W32` |
| `0x74` | 2 | ALU32 RSH K | accept `Rsh` | `Palu RSH W32` |
| `0x54` | 1 | ALU32 AND K | accept `And` | `Palu AND W32` |
| `0xa4` | 1 | ALU32 XOR K | accept `Xor` | `Palu XOR W32` |
| `0xdc` | 1 | ALU END, source bit set, imm 16, dst `r3`, src nibble 0 | **reject** (code `0xd0` is not in the ALU switch) | `Palu (END BE32 S16) W32` |
| `0xbf` | 4 | ALU64 MOV X | accept `Mov` W64 | `Palu MOV W64` |
| `0x07` | 5 | ALU64 ADD K | accept `Add` W64 | `Palu ADD W64` |
| `0x2d` | 3 | JMP64 JGT X | accept `Jgt` W64 | `Pjmpcmp (GT Unsigned) W64` |
| `0x56` | 2 | JMP32 JNE K | accept `Jne` W32 | `Pjmpcmp NE W32` |
| `0x15` | 1 | JMP64 JEQ K | accept `Jeq` W64 | `Pjmpcmp EQ W64` |
| `0x85` | 1 | JMP CALL, src nibble 0, imm 1, offset 0 | **reject** (jump switch has no code `0x80`) | `Pcall CallByStaticID imm` |
| `0x95` | 1 | EXIT | accept `Exit` | `Pret` |
| `0x61` | 2 | LDX W (mode MEM) | **reject** class LDX | `Pload Word` |
| `0x69` | 7 | LDX H | **reject** | `Pload HalfWord` |
| `0x71` | 21 | LDX B | **reject** | `Pload Byte` |
| `0x79` | 1 | LDX DW | **reject** | `Pload DBWord` |
| `0x63` | 2 | STX W | **reject** class STX | `Pstore Word` |
| `0x6b` | 9 | STX H | **reject** | `Pstore HalfWord` |
| `0x7b` | 1 | STX DW | **reject** | `Pstore DBWord` |
| `0x18` | 1 | LD DW, two slots | **reject** class LD | `Plddw PSEUDO_Constant` (src `R0`, imm 0/0, reserved 0) |

58 logical instructions are in classes the C++ decoder accepts. 46 are not: 43 memory ops, plus `LDDW`, `CALL`, and `END`. `decode_ebpf` walks every 8 bytes and throws on the first failure, which is slot `1`, opcode `0x61` (`ebpf_decode.cpp` lines 164–167: "unsupported class"). The later ALU and jump rows are classified against that decoder, but they are not reached in one call on this section. There is no ST-immediate, no atomic, no `JA`, no `DIV`/`MOD`, no `MOVSX`, no signed jump, no load-acquire, no probe load.

Per-slot operands that are not obvious from the histogram:

- ALU32 MOV K: slot `0` imm `1` → `r0` (`XDP_DROP`); slot `16` imm `0x11` → `r1` (UDP key); slot `39` imm `0x0a7100cb` → `r1`; slot `41` imm `0` → `r1`; slot `103` imm `3` → `r0` (`XDP_TX`).
- ALU64 MOV X: `3` `r6=r8`; `8` `r7=r8`; `13` `r1=r8`; `18` `r2=r10`.
- ALU64 ADD K: `4` `r6+=14`; `9` `r7+=0x22`; `14` `r1+=0x2a`; `19` `r2+=-4` (imm bytes `fc ff ff ff`); `25` `r1+=1`.
- ALU32 shifts are all immediate `8` (the ten `lsh`) or `16` (the two `rsh`). AND imm is `0xffff`. XOR imm is `0xffffffff` (`-1`).
- `be16` is slot `100`, byte `0x320`: `dc 03 00 00 10 00 00 00`.
- Stack store: slot `17`, STX W, `dst=r10`, `src=r1`, offset `-4`.
- Map value: slot `24` LDX DW `*(u64*)(r0+0)`; slot `26` STX DW back to `(r0+0)`.
- Packet base in `r8` (zero-extended `xdp_md.data`). `data_end` in `r2` until the helper. `r6 = data+14` (IPv4 header). `r7 = data+0x22` (UDP header, assuming IHL = 5).

What the bytes do, as a straight-line reading of that listing plus the C file (not a new ISA):

1. `r0 = 1`. Five unsigned checks then exit with that `r0` if they fail: `data+14 <= data_end`, ethertype halfword `== 8`, `data+0x22 <= data_end`, IPv4 protocol byte `== 0x11`, `data+0x2a <= data_end`. The compares are strict `JGT` (`ptr+len > data_end`), so equality with `data_end` is accepted. `8` is the little-endian halfword load of on-wire bytes `08 00` (`bpf_htons(ETH_P_IP)` on a little-endian host). `0x11` is UDP.
2. Spill key `0x11` at `fp-4`. `LDDW` of `rxcnt` into `r1`, key pointer in `r2`, `call 1`. The C file names that call `bpf_map_lookup_elem`. If `r0 != 0`, add `1` to the `u64` at `r0`. A null return skips the increment and still falls into the rewrite.
3. Swap the first 12 packet bytes as three `u16` pairs (Ethernet destination with source).
4. Store `0x0a7100cb` at IPv4 `daddr` (`r6+16`). Zero `iphdr.check`. Sum the 20 header bytes as ten big-endian `u16`s (explicit byte loads, shifts, ors, adds), fold twice with `>> 16` and `& 0xffff`, XOR with `-1`, `be16`, store the halfword back to `check`.
5. Store `r1`, which is still `0` from slot `41`, to `udphdr.check` (`r7+6`). `r0 = 3`. Exit.

The helper is after the five checks, so a failing packet does not call it. Slots `82` and `86` overwrite `r0` during the checksum; the helper pointer is dead after slot `26`. Success returns `3`, not the pointer.

Bounds versus stores, from the offsets (IHL is not read; the object assumes a 20-byte IPv4 header):

- Ethernet check `data+14 <= end` covers MAC bytes `0..11` and ethertype at `12`.
- `data+0x22 <= end` covers IPv4 bytes `14..33` (last byte of the `daddr` word at `r6+16`).
- `data+0x2a <= end` covers the UDP checksum halfword at `data+40..41`.

## Semantic rules actually read

C++ decoder, all of `alive2/src/ebpf.h` and `alive2/src/ebpf_decode.cpp`:

- Classes only: ALU `0x04`, JMP `0x05`, JMP32 `0x06`, ALU64 `0x07` (lines 7–13, 61–168). Any other class throws. That is the whole memory and `LDDW` gap.
- ALU codes accepted at offset 0: ADD `0x00`, SUB `0x10`, MUL `0x20`, OR `0x40`, AND `0x50`, LSH `0x60`, RSH `0x70`, XOR `0xa0`, ARSH `0xc0`, plus NEG `0x80`, DIV/MOD `0x30`/`0x90` with offset 0 or 1, MOV `0xb0`. No END `0xd0`.
- Jumps: JA `0x00`, EXIT `0x90`, and the ten compare codes. No CALL `0x80`. `jump_target` is `index + 1 + off` (or `imm` for JMP32 JA). `index` is the byte offset divided by 8 (line 40).
- Register field must be `<= 10`. This program's registers are `r0`–`r8` and `r10` only.

C++ lifter, `alive2/src/ebpf_lift.h` and `alive2/src/ebpf_lift.cpp` lines 1–709 (the `run` / `build_blocks` / `init_regs` / `emit_alu` / `emit_cmp` path). The concrete interpreter from line 713 down was not used to judge this object. With `LiftBug::None`:

- ALU32: truncate both operands to `i32`, operate, `zext` back to `i64` (`emit_alu` lines 516–539). ALU64 MOV of a register is the source value unchanged. ALU64 immediate is sign-extended (`imm64`, lines 196–200) unless `ImmNoSignExtend`.
- ADD/OR/AND/XOR map to `BinOp::Add/Or/And/Xor` (`arith_op`, lines 656–663). LSH/RSH map to `Shl`/`LShr`, and the amount is masked with 31 or 63 (`shift`, lines 553–558) unless `ShiftWithoutMask`.
- Conditional jumps become `ICmp` plus a two-way `Branch` (`emit_cmp` lines 643–653, `icmp_cond` lines 679–693). `JGT` is `ICmp::UGT`. `JNE` is `NE`. `JEQ` is `EQ`. JMP32 compares truncate to `i32`. EXIT is `Return` of `r0` (line 497). There is no memory instruction, no call instruction, and no byte-swap instruction in this emitter.
- `build_blocks` sets `loop` if a jump target is `<=` the jump's vector index (lines 228–229). This object has no such edge, but the lifter never builds blocks for it.
- `LiftInit::Rocq` poisons `r1` and `r10` and marks them `RegOrigin::Pointer`; other registers start `Undef` unless seeded (lines 304–328). `pointer_alu` / `pointer_jmp` only set `EbSite::pointer_use`. They still emit integer `BinOp` / `ICmp`. Packet arithmetic would not become a pointer add even if the loads existed.

Rocq syntax and decoder, read in full: `alive2/rocq/upstream/theories/ebpfSyntax.v`, `alive2/rocq/upstream/theories/ebpfDecoder.v`.

- `decode_insn` accepts the ALU ops above and, at code `0xd`, END. For ALU32, source-bit imm selects `LE32` and source-bit reg selects `BE32`; imm `0x10`/`0x20`/`0x40` selects `S16`/`S32`/`S64` (lines 91–109). Slot `100` is `END BE32 S16` at width `W32`, and `check_src_r0` holds because the src nibble is 0. The source bit is the endian selector, not a register operand.
- CALL code `0x8` on JMP64 with src `R0` is `Pcall CallByStaticID` (lines 127–134). Slot `22` matches, imm `1`.
- MEM mode `(opcode >> 5) == 3` is unsigned `Pload` / `Pstore` (lines 165–183). Every load and store in this object is that mode. No sign-extending load (`0x80` mode) and no probe load.
- `find_instr` on opcode `0x18` reads the next slot and requires its low 32 bits (reserved) to be 0, then `decode_lddw_insn` (lines 268–276, 235–246). Slot `20` matches `PSEUDO_Constant`. `exec_lddw` advances PC twice (`nextinstr` twice), so slot `21` is not a separate instruction unless a jump lands on it. None does.

Rocq semantics that were read in `alive2/rocq/upstream/theories/ebpfBinSem.v`:

- `ebpf_call_function` is an uninterpreted `Variable` (lines 58–61): helper id, `r1`–`r5`, and the current outcome, returning an option of `(r0 value, new mem)`.
- `eval_alu32` / `eval_alu64` / `exec_alu` (lines 332–390). ALU32 arithmetic is `Val.loword`, then `Val.longofintu` (zero-extend). ALU64 immediates go through `Int.signed` (`int64_of_int`, line 81; `eval_val_int`, lines 108–116), so slot `19`'s `-4` sign-extends. Shifts are masked by `eval_shift_mask` (31 or 63, lines 236–243).
- `eval_end`, `swab16`, `swab32`, `swab64` (lines 258–329). On `Archi.big_endian = false`, `BE32` calls `swapn`, and `S16` is `swab16`. The file's comment says `swab16(0x3412) = 0x1234`. CompCert's `bitfield_insert` definition is not in this tree and was not read. `eval_alu32`'s END arm returns `eval_end` directly, not `Val.longofintu`.
- `eval_cmp32` / `eval_cmp64` / `exec_jmpcmp` (lines 412–498). Unsigned `GT` is `Cgt` via `cmpu_bool` / `cmplu_bool`. A compare that returns `None` is `Stuck`. `eval_cmp_static` does not fire for these jumps (`r6>r2`, `w1!=8`, `w1!=0x11`, `r0==0` are not in its constant cases).
- `exec_load` / `load` / `loadv_unaligned` (lines 544–589) and `exec_store` / `store` (lines 633–646). Sizes: byte `Mint8unsigned`, half `Mint16unsigned`, word `Mint32`, dword `Mint64`. A failed load or store is `Stuck`. `exec_load` turns a `Vlong` base into a pointer only through `cast_i2p` and `addr_map`; a `Vptr` base uses `Val.offset_ptr`. `exec_store` only does `Val.offset_ptr` on the destination register. It does not call `cast_i2p`.
- `exec_lddw` (lines 648–659): `PSEUDO_Constant` writes `Int64.ofwords hi lo` and steps PC by two. Every other pseudo goes through `cast_i2p` and is `Stuck` on failure. The relocation is outside this rule: the decoder sees a constant `0`, while the ELF says the constant is the `rxcnt` object.
- `exec_instr` (lines 888–905) has an arm for `Pcall CallInternal` only. `CallByStaticID` falls through to `| _ => Stuck`. The external step is a different constructor, `exec_step_external` (lines 979–991): it requires `ebpf_call_function` to return `Some`, then sets `r0` to that result, undefines `r1`–`r5` (`undef_caller_save_regs`, lines 662–667), and steps PC by one. Memory may change. `exec_instr_event` does not record the call; the step trace uses `eBPF_ext_call`.
- Initial state (lines 993–1007): `r1` is a pointer to `ctx`, `r10` is a pointer to the stack at `bpf_stack_size` (512, line 720), other registers start `Vundef`. Final state wants `r0` to be `Vlong` or `Vptr` (lines 1009–1017).
- `Extraction.v` lines 13–14, as cited above.

`alive2/rocq/upstream/validator/Validation.v` was read only around `bpf_interpreter_trace_check` (the `Pcall CallByStaticID` arm near lines 172–200). That checker does not call `ebpf_call_function`. It takes `r0` from a trace word and injects `Vlong`. The comment there says the return is assumed to be `Vlong`, not a pointer.

Not read, so not used as rules: `CMemoryModel.v`, `GlobalSem.v`, `Nondeterminism.v`, `SCLanguage.v`, `ebpfState.v`, the bodies of `exec_call_internal` and `exec_ret`, the atomic block (`exec_atomic` and below), probe-load bodies beyond their names, CompCert `Integers` / `decode_val` / `encode_val`, and `third_party/alive2/ir/instr.cpp` (the div-UB comment in the lifter points at line 213; this program has no division). `ebpf_gate.cpp` was searched for memory/helper/map handling and the search returned no matches; it was not reviewed as a gate for this object.

## IR mapping against the existing C++ lifter only

`lift_ebpf` consumes `vector<EbInsn>` from `decode_ebpf`. There is no other C++ mapping. Memory, `LDDW`, `CALL`, and `END` have no `EbAlu` / `EbJmp` constructor (`ebpf.h` lines 12–36) and no emitter. They cannot be written down as Alive2 IR by this lifter.

If the 58 accepted opcodes occurred in a program the decoder could finish, `LiftBug::None` would lower them as follows. This is the mapping, not a conversion of `case_swap`.

| Slots | Source op | IR the lifter emits |
| --- | --- | --- |
| 0, 16, 39, 41, 103 | ALU32 MOV K | `i32` immediate (zero-extended into the `i64` constant, then truncated), result `zext` to `i64`. High 32 bits become 0. |
| 92, 96 | ALU32 MOV X | `trunc` src to `i32`, `zext` to `i64`. |
| 51, 56, 61, 66, 71, 84, 89, 90, 91, 95, 98 | ALU32 ADD X | `trunc` both, `BinOp::Add` on `i32`, `zext` to `i64`. |
| 46, 50, 55, 60, 65, 70, 75, 79, 83, 88 | ALU32 OR X | same with `BinOp::Or`. |
| 94 | ALU32 AND K `0xffff` | `BinOp::And` on `i32` with constant `0xffff`, then `zext`. |
| 99 | ALU32 XOR K `-1` | `BinOp::Xor` on `i32` with constant `0xffffffff`, then `zext`. |
| 44, 48, 53, 58, 63, 68, 73, 77, 81, 87 | ALU32 LSH K `8` | amount masked with `31`, `BinOp::Shl` on `i32`, `zext`. |
| 93, 97 | ALU32 RSH K `16` | amount masked with `31`, `BinOp::LShr` on `i32`, `zext`. |
| 3, 8, 13, 18 | ALU64 MOV X | the source `i64` value, no truncate. |
| 4, 9, 14, 19, 25 | ALU64 ADD K | sign-extended immediate (`14`, `34`, `42`, `-4`, `1`), `BinOp::Add` on `i64`. |
| 5, 10, 15 | JMP64 JGT X | `ICmp::UGT` on `i64`, branch to the target block or fall through. |
| 7, 12 | JMP32 JNE K | `trunc` dst to `i32`, compare `NE` to `i32` constant `8` or `17`. |
| 23 | JMP64 JEQ K `0` | `ICmp::EQ` on `i64` against constant `0`. |
| 104 | EXIT | `Return` of the `i64` in `r0`. |

Those jumps are not integer compares in the object. Slots `5`, `10`, and `15` compare packet pointers that were loaded and then incremented. The lifter has no load, so it cannot feed those `ICmp`s. Under `LiftInit::Rocq` the original `r1` is poison, but `r8` and `r2` are results of `LDXW`, which this IR does not have. Marking `pointer_use` does not create a memory model.

`call 1` is not an Alive2 call in this lifter. `be16` is not a `BinOp`. The `R_BPF_64_64` is not an immediate operand the decoder preserves: a future decoder that emits `PSEUDO_Constant 0` will drop the map.

Implementer constraint already visible in the lifter, not exercised here because decode throws: `build_blocks` indexes `leader` and `block_of` by the vector position `i`, while `jump_target` uses `EbInsn.index` (the slot). Those coincide only while every slot is one vector element. Folding `LDDW` into one element without keeping slot numbers makes `+0x62` and `+3` point at the wrong instruction. The second `LDDW` word must stay a hole in the slot space, not an instruction and not a deleted index.

## Memory, helper, map, loop

- Memory: required. Packet loads and stores through pointers taken from `xdp_md` (`u32` loads at `ctx+0` and `ctx+4`, then used as 64-bit pointers). Widths used: `u8`, `u16`, `u32`, `u64`. One stack store, `u32` at `r10-4`, then that address is the helper key pointer. One `u64` load/store through the helper result. No other stack slot. Rocq's 512-byte frame would cover `fp-4`. The C++ lifter has none of this. `exec_store` will not accept a `Vlong` packet pointer unless some earlier step made it a `Vptr`; `exec_load` will, via `addr_map`. That split is a real modeling gap for the stores, which are most of the packet writes.
- Helper: required. One call, static id `1`, src nibble `0`, after the checks. Arguments: `r1` = relocated `rxcnt`, `r2` = `fp-4` (key `0x11`), `r3`–`r5` are not set up by this program (`r1` was also used as a scratch pointer before being overwritten by the `LDDW`). The call clobbers `r1`–`r5` in `exec_step_external` and returns in `r0`. The program only needs `r0` afterward, plus callee-saved `r6`, `r7`, `r8` and `r10`. The id is `1` in the encoding; the name `bpf_map_lookup_elem` is from the C source and the BTF line string, not from a helper table in the lifter. No helper table was found in the C++ lifter.
- Map: required. `rxcnt`, `BPF_MAP_TYPE_ARRAY`, key 4, value 8, 256 entries, flags 0. Referenced by `R_BPF_64_64`, not by a map index. Key `17` is in range. The value update is a plain `u64` add of `1`, not an atomic. A null lookup skips the update. The counter is a side effect; it is not the XDP return.
- Loop: none. Every branch is forward. Five edges go to `exit`. One edge skips the three-slot increment (`23` → `27`). `LiftInfo.loop` would be false if the CFG were built. Do not unroll anything. Do not report a back edge.

CO-RE (kind 0, section `xdp1`), already baked into the offsets above, still present for a loader:

| Insn byte | Slot | type id | access | field |
| --- | --- | --- | --- | --- |
| `0x008` | 1 | 2 | `0:1` | `xdp_md.data_end` |
| `0x010` | 2 | 2 | `0:0` | `xdp_md.data` |
| `0x030` | 6 | 8 | `0:2` | `ethhdr.h_proto` |
| `0x058` | 11 | 15 | `0:7` | `iphdr.protocol` |
| `0x140` | 40 | 15 | `0:9:0:1` | `iphdr` anon `daddr` |
| `0x150` | 42 | 15 | `0:8` | `iphdr.check` |
| `0x328` | 101 | 15 | `0:8` | `iphdr.check` |
| `0x330` | 102 | 22 | `0:3` | `udphdr.check` |

## Conversion result

**NOT CONVERTED.**

`decode_ebpf` on the `xdp1` bytes throws at slot `1` (`unsupported class in opcode 0x61`) and never returns a vector. `lift_ebpf` is not invoked. There is no Alive2 function, no CFG, and no SMT query for this object. The 58 ALU/jump opcodes are not a program by themselves: their operands are packet pointers, a map pointer, and a checksum over bytes the lifter cannot load. Calling the missing memory/helper/endian model "unsupported" is not a successful conversion. Nothing here was marked EQUIVALENT.

## Proof coverage

No theorem in the files that were read is about this ELF.

- The Rocq decoder can name every instruction in `xdp1`, including loads, stores, the constant-form `LDDW`, `CallByStaticID 1`, and `END BE32 S16`. That is a decode claim, not a proof that the object was run.
- `exec_instr` gets stuck on `CallByStaticID`. Only `exec_step_external` runs it, and only by applying the uninterpreted `ebpf_call_function`. There is no definition of helper `1`, no array map, and no equation that the lookup of key `17` returns a pointer to an 8-byte value or null.
- `Validation.v`'s trace checker would force that result to `Vlong` if a trace were supplied. `bpf_map_lookup_elem` returns a pointer. The checker's own comment records that assumption. A passing trace check under that assumption would not be a proof of this program.
- `exec_lddw` of `PSEUDO_Constant` loads the immediate `0` that is in the file. It does not apply `R_BPF_64_64`. A semantics run that ignores `.relxdp1` looks up the wrong object.
- `alive2/src/ebpf_exhibit.cpp` (the paragraph read at the `supported-scope-equivalent` sentence) says that scope does not cover loops, memory, maps, helpers, or pointer arithmetic. This program needs memory, a map, a helper, and pointer arithmetic. It does not need a loop. It is outside that scope. EXCLUDED / UNKNOWN / UNSUPPORTED are not passes, by that same paragraph.
- `eval_end` plus `Extraction.v`'s `Archi.big_endian = false` is the only endian rule read for `be16`. `swab16` was not executed. CompCert's `bitfield_insert` was not read.

## Counterexample idea

Do not treat a model as agreeing with this object unless it separates the following. One witness is enough to break a "rewrite the destination and return TX" summary.

Take a 42-byte (or longer) Ethernet frame whose ethertype bytes are `08 00`, whose IPv4 header is 20 bytes with protocol `17`, and whose UDP header starts at offset `34`. `data_end - data >= 42`, so all three `JGT` checks fall through.

- Success return is `r0 = 3`, not `1`, and not the map pointer. The early `r0 = 1` is dead on this path. Slots `82` and `86` also clobber `r0` before slot `103`.
- `daddr` bytes become `cb 00 71 0a` (`203.0.113.10`). A model that stores the C macro `0xcb00710a` without the htonl already folded into the immediate, or that byte-swaps `0x0a7100cb` a second time, writes a different address. `case_mark`'s `203.0.113.77` is a different program.
- `iphdr.check` is not left as the input checksum and not left as the zero written at slot `42`. It is the `be16` of the ones' complement of the 20-byte header sum. Omitting `be16` on a little-endian store swaps the two checksum bytes relative to this object.
- `udphdr.check` becomes `0`. Keeping the original UDP checksum is a different packet. IPv4 allows that zero.
- The first 12 bytes are the MAC pair swap. A model that only patches IP leaves them unchanged.
- If the lookup result is null, the packet rewrite still happens and `r0` is still `3`. The `u64` at the value is unchanged. If the lookup returns a pointer, that `u64` increases by `1` and the packet result is still `3`. A model that returns the counter, or that drops the packet when the lookup fails, is wrong.
- The lookup key is `17`, not "whatever protocol was in the packet" after a failed compare: the compare must already have succeeded. A short frame (`data+14 > data_end`), or ethertype not `08 00`, or protocol not `17`, or `data+42 > data_end`, returns `r0 = 1` and must not call helper `1` and must not write the packet. A trace with a map lookup on that input is a counterexample.
- IHL is not consulted. A 24-byte IPv4 header with protocol `17` and a long enough frame still takes the success path and treats offset `34` as UDP. A model that skips options diverges from the object. That is a spec bug if someone "fixes" it, not a bug in the ELF.

## Gaps that make the status ISSUES

1. `decode_ebpf` rejects class LDX at the second instruction, and also rejects all STX, the `LDDW`, `call 1`, and `be16`. The lifter never runs.
2. The lifter's IR has no memory, no helper, no map, and no endian op. Pointer compares would be integer `ICmp`s even if the loads were added as plain values.
3. The only map reference is `R_BPF_64_64` against `rxcnt`. The instruction encoding is a constant `0` (`PSEUDO_Constant`). Dropping the relocation or reading it as a map index both change the program. Rocq `exec_lddw` does the former. `exec_instr` then gets stuck on the call; the external step is uninterpreted; the validator trace path forces `Vlong`.
4. `exec_store` does not use the `cast_i2p` path that `exec_load` uses, so a `Vlong` packet pointer that survived a load still cannot be stored in the semantics that were read.
5. `be16` depends on `swab16` and on `Archi.big_endian = false`. The swap function's CompCert primitive was not read, so the checksum bytes are not a closed proof obligation yet.

STATUS: ISSUES
