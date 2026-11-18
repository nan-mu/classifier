# firewall — observation report

Produce an observation report for the firewall BPF object so a later implementer can compile it, without inventing a shared ISA.

Conversion result: **NOT CONVERTED**. No `.alive` file is emitted. This note classifies the ELF against the decoder and lifter that already exist. It does not invent an ISA, a memory IR, a helper, or a success path.

STATUS: ISSUES

## Evidence

Commands actually run:

- `shasum -a 256 /Volumes/SSD/bs/build/firewall/bpf.o` → `143bd90de464fd13d032818d5a9f626044238c44a34230319d93b36161a9aa3f` (matches the requested digest). File size 8640, same as `bpf.toml` `size`.
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -a` on that ELF (header, sections, symbols, relocations).
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r -s --section-headers --syms --full-contents` on that ELF. The `xdp` disassembly, including the `R_BPF_64_64 blacklist` annotation and the four CO-RE byte-offset notes, is quoted below from that run.
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -p` on `.BTF`, `.BTF.ext`, `license`, `.debug_str`.
- A local little-endian unpack of the ELF section bytes: `xdp` as 23 slots of `opcode:u8, regs:u8, off:i16, imm:i32`; `.maps` and `license` raw bytes; the one `.relxdp` `Elf64_Rel`; BTF types; `.BTF.ext` core-relo records. The slot dump matches llvm-objdump. No compiler was run.

ELF identity from `llvm-readelf -a`: ELF64, `ELFDATA2LSB` (2's complement, little endian), `ET_REL`, `EM_BPF`, `e_entry` 0, no program headers, 27 section headers at file offset `0x1b00`. Endianness of the file and of every instruction field below is little-endian. There is no `END` / byte-swap opcode. The ethertype test is the immediate `8`, which is what a little-endian `u16` load of on-wire `08 00` produces. I did not read a CompCert `Archi.big_endian` instantiation in this repo, so I do not claim `decode_val` in the Rocq memory model is little-endian.

Notes file `/Volumes/SSD/bs/build/firewall/bpf.toml` agrees with the disassembly and the BTF map shape. Its `aot_addr = 0x40380258` is not in the ELF. I did not use it.

## Executable sections

| Index | Name | Flags | File offset | Size | Role |
| --- | --- | --- | --- | --- | --- |
| 2 | `.text` | AX (`0x6`) | `0x40` | **0** | empty. Not the program. Shares the file offset with `xdp` only because its size is zero. |
| 3 | `xdp` | AX (`0x6`) | `0x40` | **0xb8 (184)** | the only nonzero executable section |

No other section has `SHF_EXECINSTR`. `.maps` (32 bytes, all zero) and `license` (4 bytes, `GPL\0`) are `WA`, not executable.

## Entries

One function. Symbol `firewall`, `FUNC GLOBAL`, value 0, size 184, section index 3 (`xdp`). That is the whole section. ELF `e_entry` is 0 and there are no program headers, so the entry is this symbol, not `e_entry`.

`llvm-objdump -d` prints `Disassembly of section xdp` and `<firewall>:`. It does not disassemble `.text`.

Source file symbol: `FILE LOCAL firewall.c`. Debug strings name `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/firewall.c`. BTF has `int firewall(struct xdp_md *ctx)` and section name `xdp`.

## Instruction list

23 eight-byte slots, indices 0..22. One of them is the high half of `LDDW`, so there are 22 architectural instructions. `LDDW` at slot 12 consumes slot 13; the next opcode is at slot 14. No jump target is 13.

Bytes are the `xdp` section, little-endian. `regs` is `src:4|dst:4`.

| pc | bytes | op | dst | src | off | imm | class (this repo) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | `b400000002000000` | `0xb4` | r0 | r0 | 0 | 2 | ALU32 MOV K |
| 1 | `6113040000000000` | `0x61` | r3 | r1 | 4 | 0 | LDX MEM W |
| 2 | `6111000000000000` | `0x61` | r1 | r1 | 0 | 0 | LDX MEM W |
| 3 | `bf12000000000000` | `0xbf` | r2 | r1 | 0 | 0 | ALU64 MOV X |
| 4 | `070200000e000000` | `0x07` | r2 | r0 | 0 | 14 | ALU64 ADD K |
| 5 | `2d32100000000000` | `0x2d` | r2 | r3 | +16 | 0 | JMP JGT X (unsigned) |
| 6 | `69140c0000000000` | `0x69` | r4 | r1 | 12 | 0 | LDX MEM H |
| 7 | `56040e0008000000` | `0x56` | r4 | r0 | +14 | 8 | JMP32 JNE K |
| 8 | `0701000022000000` | `0x07` | r1 | r0 | 0 | 34 (`0x22`) | ALU64 ADD K |
| 9 | `2d310c0000000000` | `0x2d` | r1 | r3 | +12 | 0 | JMP JGT X (unsigned) |
| 10 | `b70100000c000000` | `0xb7` | r1 | r0 | 0 | 12 (`0xc`) | ALU64 MOV K |
| 11 | `0f12000000000000` | `0x0f` | r2 | r1 | 0 | 0 | ALU64 ADD X |
| 12 | `1801000000000000` | `0x18` | r1 | r0 | 0 | 0 | LD DW IMM (`LDDW` low) |
| 13 | `0000000000000000` | `0x00` | r0 | r0 | 0 | 0 | `LDDW` high half, not an insn |
| 14 | `8500000001000000` | `0x85` | r0 | r0 | 0 | 1 | JMP CALL K, static id 1 |
| 15 | `bf01000000000000` | `0xbf` | r1 | r0 | 0 | 0 | ALU64 MOV X |
| 16 | `b400000002000000` | `0xb4` | r0 | r0 | 0 | 2 | ALU32 MOV K |
| 17 | `1501040000000000` | `0x15` | r1 | r0 | +4 | 0 | JMP JEQ K |
| 18 | `6112000000000000` | `0x61` | r2 | r1 | 0 | 0 | LDX MEM W |
| 19 | `0402000001000000` | `0x04` | r2 | r0 | 0 | 1 | ALU32 ADD K |
| 20 | `6321000000000000` | `0x63` | r1 | r2 | 0 | 0 | STX MEM W |
| 21 | `b400000001000000` | `0xb4` | r0 | r0 | 0 | 1 | ALU32 MOV K |
| 22 | `9500000000000000` | `0x95` | r0 | r0 | 0 | 0 | JMP EXIT |

Real disassembly from `llvm-objdump -d -r` of section `xdp` (not `.text`):

```
0000000000000000 <firewall>:
       0:	b4 00 00 00 02 00 00 00	w0 = 0x2
       1:	61 13 04 00 00 00 00 00	w3 = *(u32 *)(r1 + 0x4)
			0000000000000008:  CO-RE <byte_off> [13] struct xdp_md::data_end (0:1)
       2:	61 11 00 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x0)
			0000000000000010:  CO-RE <byte_off> [13] struct xdp_md::data (0:0)
       3:	bf 12 00 00 00 00 00 00	r2 = r1
       4:	07 02 00 00 0e 00 00 00	r2 += 0xe
       5:	2d 32 10 00 00 00 00 00	if r2 > r3 goto +0x10 <L0>
       6:	69 14 0c 00 00 00 00 00	w4 = *(u16 *)(r1 + 0xc)
			0000000000000030:  CO-RE <byte_off> [16] struct ethhdr::h_proto (0:2)
       7:	56 04 0e 00 08 00 00 00	if w4 != 0x8 goto +0xe <L0>
       8:	07 01 00 00 22 00 00 00	r1 += 0x22
       9:	2d 31 0c 00 00 00 00 00	if r1 > r3 goto +0xc <L0>
      10:	b7 01 00 00 0c 00 00 00	r1 = 0xc
			0000000000000050:  CO-RE <byte_off> [22] struct iphdr::<anon 9>.<anon 0>.saddr (0:9:0:0)
      11:	0f 12 00 00 00 00 00 00	r2 += r1
      12:	18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00	r1 = 0x0 ll
			0000000000000060:  R_BPF_64_64	blacklist
      14:	85 00 00 00 01 00 00 00	call 0x1
      15:	bf 01 00 00 00 00 00 00	r1 = r0
      16:	b4 00 00 00 02 00 00 00	w0 = 0x2
      17:	15 01 04 00 00 00 00 00	if r1 == 0x0 goto +0x4 <L0>
      18:	61 12 00 00 00 00 00 00	w2 = *(u32 *)(r1 + 0x0)
      19:	04 02 00 00 01 00 00 00	w2 += 0x1
      20:	63 21 00 00 00 00 00 00	*(u32 *)(r1 + 0x0) = w2
      21:	b4 00 00 00 01 00 00 00	w0 = 0x1
<L0>:
      22:	95 00 00 00 00 00 00 00	exit
```

### Jump slots

`jump_target` in `alive2/src/ebpf_decode.cpp` is `index + 1 + off` for a conditional jump (`ja_uses_imm` is false). The same `PC + 1 + offset` shape is `exec_jmpcmp` plus `nextinstr` in `alive2/rocq/upstream/theories/ebpfBinSem.v`. All four offsets are positive and land on slot 22.

| pc | kind | off | target | not-taken |
| --- | --- | --- | --- | --- |
| 5 | JMP64 unsigned `r2 > r3` | +16 | 22 `exit` | 6 |
| 7 | JMP32 `w4 != 8` | +14 | 22 `exit` | 8 |
| 9 | JMP64 unsigned `r1 > r3` | +12 | 22 `exit` | 10 |
| 17 | JMP64 `r1 == 0` | +4 | 22 `exit` | 18 |

No `JA`. No backward edge. Slot 22 is `EXIT` and does not fall through. The C++ block builder sets `loop` only when `tgt <= i` (`alive2/src/ebpf_lift.cpp`, `build_blocks`). That predicate is false for every edge here. **Loop: no.**

### What the body does (from the bytes, matched to BTF line strings in this ELF)

BTF strings, not a separate C reading: `void *data_end = (void *)(long)ctx->data_end`, `void *data = (void *)(long)ctx->data`, `if ((void *)(eth + 1) > data_end)`, `h_proto = eth->h_proto`, `if (h_proto != bpf_htons(ETH_P_IP))`, `if ((void *)(ip + 1) > data_end)`, `cnt = bpf_map_lookup_elem(&blacklist, &ip->saddr)`, `if (cnt) { *cnt = *cnt + 1; }`.

Register story, assuming the raw offsets and ignoring the loader patches listed later:

- pc 0 writes `r0 = 2` (ALU32, high bits cleared). This is the value left behind on every early exit.
- pc 1 reads `u32` at `r1+4` into `r3` before pc 2 overwrites `r1`. BTF `xdp_md.data_end` is `__u32` at byte 4.
- pc 2 reads `u32` at `r1+0` into `r1`. BTF `xdp_md.data` is `__u32` at byte 0. After this, `r1` is no longer the context pointer.
- pc 3–4 copy that value to `r2` and add 14. BTF `ethhdr` size is 14. The `0xe` immediate has **no** CO-RE record.
- pc 5 exits with `r0 = 2` when `r2 > r3` (unsigned 64).
- pc 6 reads `u16` at `r1+12` into `r4`. BTF `ethhdr.h_proto` is `__be16` at byte 12.
- pc 7 exits with `r0 = 2` when the low 32 bits of `r4` are not 8.
- pc 8 adds `0x22` (34 = 14 + 20) to `r1`. BTF `iphdr` size is 20. The `0x22` immediate has **no** CO-RE record.
- pc 9 exits with `r0 = 2` when that pointer is above `r3`.
- pc 10–11 replace `r1` with the immediate 12 and add it to `r2`. `r2` becomes `data + 14 + 12`. BTF access `0:9:0:0` on `iphdr` is the anonymous union at byte 12, then its first struct, then `saddr` (`__be32` at bit 0 of that struct). So the compile-time key address is `&iphdr.saddr`.
- pc 12–13 are `lddw r1, 0` with `src_reg = 0`. The map is not in the immediate. See relocations.
- pc 14 is `call 1` with `src_reg = 0`. Args still in registers: `r1` is the `lddw` result, `r2` is the key pointer, `r3` is still the `data_end` load, `r4` is still `h_proto`, `r5` was never written.
- pc 15 copies `r0` to `r1`. pc 16 sets `r0 = 2` again, because the call overwrote `r0`.
- pc 17 exits with `r0 = 2` when `r1 == 0`.
- pc 18–20 load a `u32` at `r1+0`, add 1 with ALU32, and store that `u32` back. This is a direct store, not a second call.
- pc 21 sets `r0 = 1`, then pc 22 exits.

`r10` is never read or written. No stack slot is used.

Debug strings list `XDP_ABORTED`, `XDP_DROP`, `XDP_PASS`, `XDP_TX`, `XDP_REDIRECT`, `xdp_action`. The parsed BTF has no enum, so this ELF does not assign those names to 0, 1, or 2. The observable returns in the instruction stream are the immediates **2** (early exits and the null-pointer exit) and **1** (after the store).

## Relocations, maps, BTF, CO-RE

Keep these three apart. They are not the same reference.

**Raw `LDDW`.** Slots 12–13 are `18 01 00 00` plus eight zero bytes. `dst = r1`, `src_reg = 0`, both immediates 0. In `alive2/rocq/upstream/theories/ebpfDecoder.v`, `decode_lddw_insn` maps `src_reg = R0` to `Plddw PSEUDO_Constant`. That is a 64-bit constant 0, not a map. `src_reg` is not `R1` (`PSEUDO_MAP_FD`), not `R5` (`PSEUDO_MAP_IDX`), not `R2` (`PSEUDO_MAP_VALUE`), not `R6` (`PSEUDO_MAP_IDX_VALUE`). The syntax comment in `alive2/rocq/upstream/theories/ebpfSyntax.v` lists those source-register encodings; none of them is present in the opcode byte.

**Code relocation, separate from the raw immediate.** `.relxdp` has one `Elf64_Rel`: section offset `0x60`, type `1` (`R_BPF_64_64`), symbol index 12. `0x60` is byte 96, which is slot 12. Symbol 12 is `blacklist`, `OBJECT GLOBAL`, size 32, section `.maps`. llvm-objdump prints `R_BPF_64_64 blacklist` on the `lddw` line. A loader patches the wide immediate. The instruction bits in the file are still zero, and `src_reg` is still 0. Treating the reloc as if the object already contained `BPF_PSEUDO_MAP_FD` or a map index would invent bits that are not there.

**Not a map reference.** `.rel.BTF` has two `R_BPF_64_NODYLD32` (type 4) entries, symbols `blacklist` and `LICENSE`. Those patch BTF datasec records, not `xdp`. Debug relocs (`R_BPF_64_ABS32`, `R_BPF_64_ABS64`) point at debug sections and at symbols `xdp`, `LICENSE`, `blacklist`. They are not instruction operands.

**Map metadata is BTF, not the `.maps` bytes.** `.maps` is 32 zero bytes. Symbol `blacklist` covers that whole section. Parsed `.BTF` (magic `0xeb9f`, 33 types):

- type 10, anonymous struct, size 32. Fields: `type` pointer-to-array of **1** `int`; `max_entries` pointer-to-array of **256** `int`; `key` pointer to `__u32`; `value` pointer to `__u32`. That is the libbpf `__uint` / `__type` encoding: map type value 1, max_entries 256, key 4 bytes, value 4 bytes. `bpf.toml` names type 1 as `BPF_MAP_TYPE_HASH`. The integer 1 is the array length in BTF; the ELF does not contain the enumerator text `BPF_MAP_TYPE_HASH`.
- type 11, `VAR blacklist`, linkage 1, type 10.
- type 32, `DATASEC .maps`, one variable, type 11, offset 0, size 32.

`license` bytes are `47 50 4c 00` (`GPL`). BTF type 33 is `DATASEC license` for `VAR LICENSE`, a 4-byte `char` array.

**CO-RE, also not an ELF relocation on `.relxdp`.** `.BTF.ext` header length 32, core-relo subsection record size 16, one section named `xdp`, four records. `kind = 0` on every record (`BPF_FIELD_BYTE_OFFSET`; the kind number is the record, the name is the usual UAPI spelling of kind 0). They match `bpf.toml` `[CORE]` and the objdump notes:

| insn byte off | slot | type id | access | BTF type I parsed | field |
| --- | --- | --- | --- | --- | --- |
| `0x08` | 1 | 13 | `0:1` | `xdp_md` | `data_end` at byte 4, `__u32` |
| `0x10` | 2 | 13 | `0:0` | `xdp_md` | `data` at byte 0, `__u32` |
| `0x30` | 6 | 16 | `0:2` | `ethhdr` | `h_proto` at byte 12, `__be16` |
| `0x50` | 10 | 22 | `0:9:0:0` | `iphdr` | `saddr` at byte 12 of the struct, `__be32` |

`xdp_md` in this BTF is 24 bytes: `data`, `data_end`, `data_meta`, `ingress_ifindex`, `rx_queue_index`, `egress_ifindex`, each `__u32`. `iphdr` bitfields: `ihl` and `version` are 4-bit fields in the first byte; the program never loads them. The bounds constant `0x22` is `sizeof(ethhdr)+sizeof(iphdr)` baked into an ALU immediate, not a `BPF_TYPE_SIZE` relo (no kind 9 record exists).

Neither `decode_ebpf` nor `find_instr` reads `.BTF.ext` or `.relxdp`.

## Semantic rules actually read

Rocq decoder, `alive2/rocq/upstream/theories/ebpfDecoder.v`, read in full:

- `decode_insn` class/src/code split. ALU32/ALU64 opcode nibble `0xb` with immediate source is `Palu MOV`. Nibble `0x0` is `Palu ADD`. JMP64 nibble `0x2` is `Pjmpcmp (GT Unsigned)`. JMP32 nibble `0x5` with immediate source is `Pjmpcmp NE` at width `W32`. JMP64 nibble `0x1` is `Pjmpcmp EQ`. JMP64 code `0x8`, immediate source, `src_reg = R0`, offset 0, is `Pcall CallByStaticID`. Code `0x9` with zero dst/src/imm/off is `Pret`.
- Memory mode: `(op >> 5) == 3` is the MEM mode used here. Size bits: `0` Word, `1` HalfWord. `LDX` plus `imm == 0` is `Pload`. `STX` plus `imm == 0` is `Pstore` of a register. Opcode `0x61` is `Pload Word`. Opcode `0x69` is `Pload HalfWord`. Opcode `0x63` is `Pstore Word`.
- `decode_lddw_insn`: `R0` → `PSEUDO_Constant`. The second slot's low 32 bits must be 0 (`find_instr`); they are.
- `find_instr` on opcode `0x18` consumes `pc` and `pc+1` and does not apply ELF relocations.

Classification under that decoder:

| pc | Rocq instruction |
| --- | --- |
| 0 | `Palu MOV W32 R0 (inr 2)` |
| 1 | `Pload Word R3 R1 (off 4)` |
| 2 | `Pload Word R1 R1 (off 0)` |
| 3 | `Palu MOV W64 R2 (inl R1)` |
| 4 | `Palu ADD W64 R2 (inr 14)` |
| 5 | `Pjmpcmp (GT Unsigned) W64 R2 (inl R3) (off 16)` |
| 6 | `Pload HalfWord R4 R1 (off 12)` |
| 7 | `Pjmpcmp NE W32 R4 (inr 8) (off 14)` |
| 8 | `Palu ADD W64 R1 (inr 34)` |
| 9 | `Pjmpcmp (GT Unsigned) W64 R1 (inl R3) (off 12)` |
| 10 | `Palu MOV W64 R1 (inr 12)` |
| 11 | `Palu ADD W64 R2 (inl R1)` |
| 12–13 | `Plddw PSEUDO_Constant R1 (lo 0) (hi 0)` |
| 14 | `Pcall CallByStaticID (imm 1)` |
| 15 | `Palu MOV W64 R1 (inl R0)` |
| 16 | `Palu MOV W32 R0 (inr 2)` |
| 17 | `Pjmpcmp EQ W64 R1 (inr 0) (off 4)` |
| 18 | `Pload Word R2 R1 (off 0)` |
| 19 | `Palu ADD W32 R2 (inr 1)` |
| 20 | `Pstore Word R1 (inl R2) (off 0)` |
| 21 | `Palu MOV W32 R0 (inr 1)` |
| 22 | `Pret` |

Rocq execution, `alive2/rocq/upstream/theories/ebpfBinSem.v`, the definitions named here were read. `exec_atomic` and the race relation were not; this program has no atomic opcode.

- `int64_of_int` is `Int64.repr (Int.signed i)`. ALU64 immediates are sign-extended. The immediates in this program are 14, 34, 12, all small and positive, so the sign bit is clear.
- `eval_alu32` `MOV` is `Val.longofintu` of the source. `ADD` is `Val.longofintu (Val.add (Val.loword dst) src)`. I did not open CompCert's `Val.longofintu` body. The load caster next to it zero-extends: `load_value_casting` maps `Vint i` to `Vlong (Int64.repr (Int.unsigned i))`.
- `eval_alu64` `MOV` returns the source. `ADD` is `Val.addl`. I did not open CompCert's `Val.addl`.
- `exec_alu` writes the destination and then `nextinstr` (PC + 1). Same-register `SUB`/`XOR` special case does not apply.
- `eval_cmp64` unsigned `GT` is `Val.cmplu_bool ... Cgt`. `EQ` is `Ceq`. Immediate source is `Vlong (int64_of_int i)`, so the `0` at pc 17 is the 64-bit zero. `eval_cmp32` `NE` compares `Val.loword` values. `eval_cmp_static` does not fold any compare in this program (no same-register compare, and the unsigned-64 `GT`/`LE` constant folds are for `0` and `-1` as the unsigned extreme, not for these operands).
- `exec_jmpcmp`: `None` from the compare is `Stuck`. A true condition sets `PC` to `offset_ptr PC off`, then `nextinstr` adds one. A false condition only does `nextinstr`.
- `exec_load`: if the base is `Vlong`, address is `cast_i2p (base + signed offset)` through `addr_map`; if `Vptr`, address is `Val.offset_ptr`. A failed cast or a failed `load` is `Stuck`. `Word` uses `Mint32`, `HalfWord` uses `Mint16unsigned`, then `load_value_casting` zero-extends a `Vint`. I did not read `cast_i2p`'s full fixpoint past the first clause that was in the read window; the call in `exec_load` is what this program hits.
- `exec_store`: address is only `Val.offset_ptr` of the base. There is no `cast_i2p` and no `addr_map` argument. `Word` stores `eval_reg_immw W32` of the source (low 32 bits) with `Mint32`. Failure is `Stuck`. The register file is otherwise unchanged.
- `exec_lddw` for `PSEUDO_Constant` writes `Vlong (Int64.ofwords hi lo)` and steps PC twice. Other pseudo kinds go through `cast_i2p` and `Stuck` on failure. This object takes the constant path.
- `exec_instr` returns `Stuck` for `Pcall CallByStaticID` (the wildcard). The external-call rule is separate.
- `exec_step_external` (read): requires `Pcall` with `CallByStaticID` or `CallByBTF`, then `ebpf_call_function i r1 r2 r3 r4 r5 outcome = Some (res, m')`. `ebpf_call_function` is a `Variable` at line 60 of the same file, type `imm -> val -> val -> val -> val -> val -> outcome -> option (val * mem)`. It is not defined. The next state undefines r1–r5, sets `r0` to `res`, and sets PC to original+1. `code_id'` and `tail_call_cnt'` are quantified and not constrained by the premises I read.
- `exec_ret` on an empty call stack sets PC to `Vnullptr` and keeps `r0`. `initial_lst_state` sets PC to the code block, `R10` to a 512-byte stack pointer (`bpf_stack_size`), `R1` to a context pointer, and every other register to `Vundef`.

C++ decoder, `alive2/src/ebpf_decode.cpp` and `alive2/src/ebpf.h`, read in full. `EbInsn` is only `EbAlu` or `EbJmp`. Classes other than ALU, ALU64, JMP, JMP32 hit `unsupported class`. JMP code `0x80` (the `call` opcode) is not in the jump switch, so it is `unsupported jump opcode`. There is no `LDDW` pair decoder: slot 13 would be decoded on its own if execution reached it.

So `decode_ebpf` accepts, if they were presented alone, pc 0, 3, 4, 5, 7, 8, 9, 10, 11, 15, 16, 17, 19, 21, 22. It rejects the program at **pc 1** (`0x61`, class LDX). It would also reject pc 2, 6, 12, 13, 14, 18, 20. `make_alive_trace` calls `decode_ebpf` first (`alive2/src/ebpf_lift.cpp`). The lifter never sees this section.

Syntax file `alive2/rocq/upstream/theories/ebpfSyntax.v` was read in full for the instruction and pseudo-pointer inductive types. `alive2/rocq/upstream/theories/ebpfState.v` was not read; register-map operations are used by the semantics file but the state lemmas were not opened.

Not read, so not used as rules: `CMemoryModel.v`, `Nondeterminism.v`, `SCLanguage.v`, CompCert `Values`/`Memory` bodies, and the Linux helper table. The name `bpf_map_lookup_elem` is a string in this ELF's `.BTF`, not a Rocq definition. Helper immediate `1` is just the call immediate.

## IR mapping against the existing C++ lifter only

The lifter (`alive2/src/ebpf_lift.cpp`, `emit_alu`, `emit_cmp`, `emit`, `build_blocks`) only runs on `EbInsn`. There is no IR opcode in this lifter for `Pload`, `Pstore`, `Plddw`, or `Pcall`. The concrete walker marks a `MemInstr` as `MemorySummary::Changed` and then `StepStatus::Unsupported`, and its `ICmp` switch only evaluates `EQ` and `UGT`. That walker is unreachable here because decode throws first.

What the same functions would emit for the ALU/JMP slots, with `LiftBug::None`, if those slots were the whole program. This is a mapping, not a conversion. Registers are `i64`. ALU32 immediates are zero-extended to `i64` (`imm64` with `sign` false) and then truncated. ALU64 immediates are sign-extended.

| pc | IR the current lifter emits for this opcode |
| --- | --- |
| 0, 16 | `r0 = zext i64 (trunc i32 (i64 2))` |
| 3 | `r2 = r1` (bare 64-bit mov, no trunc) |
| 4 | `r2 = add i64 r2, sext(14)` |
| 5 | `icmp ugt i64 r2, r3`, branch to the exit block or the fall-through block |
| 7 | `icmp ne i32 (trunc r4), (trunc (i64 8))`, branch. The concrete walker does **not** evaluate `ICmp::NE`. |
| 8 | `r1 = add i64 r1, sext(34)` |
| 9 | `icmp ugt i64 r1, r3`, branch |
| 10 | `r1 = sext(12)` (64-bit mov immediate returns the immediate) |
| 11 | `r2 = add i64 r2, r1` |
| 15 | `r1 = r0` |
| 17 | `icmp eq i64 r1, sext(0)`, branch |
| 19 | `r2 = zext i64 (add i32 (trunc r2), (trunc (i64 1)))` |
| 21 | `r0 = zext i64 (trunc i32 (i64 1))` |
| 22 | `ret i64 r0` |

`build_blocks` would also mark the instruction after each conditional jump as a leader, and the exit slot as its own block. Taken edges all go to the exit block. `info.loop` would be false. Pointer-origin tracking exists (`RegOrigin::Pointer`) but nothing in this lifter creates a pointer from a load, because loads are not decoded.

pc 1, 2, 6, 12, 13, 14, 18, 20 have no row. That is the conversion failure.

## Memory, helper, map, loop

- **Memory: required.** Four loads (pc 1, 2, 6, 18) and one store (pc 20). Widths: three `u32`, one `u16`, one `u32` store. pc 1 and pc 2 are context field loads. pc 6 is a packet halfword. pc 18 and pc 20 are a `u32` at offset 0 of whatever pc 14 returned. `exec_load` can turn a `Vlong` into a pointer only through `addr_map`. `exec_store` cannot. A helper result that is a `Vlong` address makes the counter store `Stuck`.
- **Helper: yes.** pc 14, `CallByStaticID` immediate 1, `src_reg` 0. BTF line string says `bpf_map_lookup_elem(&blacklist, &ip->saddr)`. The Rocq rule passes r1–r5 to an undefined `ebpf_call_function` and may change memory. No hash lookup, no key compare, no NULL-on-miss is defined. After the call the model clobbers r1–r5; the program reloads `r1` from `r0` and does not reuse r2–r5. `r0` is rewritten to 2 at pc 16 before the null check.
- **Map: yes, but not as an instruction immediate.** One map, symbol `blacklist`, BTF type value 1, max_entries 256, key `__u32`, value `__u32`. Identity is the `R_BPF_64_64` reloc at `xdp+0x60`. The value update is the pc 20 store, not `call 2`. `.maps` contributes no bytes of map state.
- **Loop: no.** Four forward branches, all to pc 22. No back-edge, no `JA`, no call-internal, no tail call.
- **CO-RE: yes**, four kind-0 byte-offset records. Not applied by either decoder.
- **Stack: unused.** `r10` does not appear.

## Proof coverage

No theorem in this repo is about this program.

- `alive2/rocq/upstream/theories/ebpfSyntax.v` has `ireg_eq` and `preg_eq` only.
- `alive2/rocq/upstream/theories/ebpfBinSem.v` contains a commented-out `is_label_correct` for a `Plabel` constructor that is not in the current instruction type. I found no other `Lemma`/`Theorem` there. `ebpf_call_function` is a `Variable`.
- `alive2/rocq/upstream/validator/Validation.v` was not read end to end. The part that was read (`is_final_state`, and the `Pcall CallByStaticID` / `CallByBTF` branch around lines 171–186) is an executable trace checker, not a proof. On an external call it takes `r0` from the trace as a `Vlong` and does not undefine r1–r5. A comment there says the return might be a pointer. `Pret` with an empty stack is the final state. That checker does not mention firewall, hash maps, or CO-RE.
- `alive2/src/ebpf_gate.cpp` `OpKind` (read through the switch at the top of the file) is only mov, neg, ALU, `JA`, exit, and compare. A program that does not decode cannot enter that gate.
- `alive2/src/ebpf_check.cpp` (the SMT harness at the top of the file) operates on an `EbExec` of already-decoded instructions. It does not decode this ELF.

Nothing proves that the early-exit immediate is 2, that a hit returns 1, or that the stored word is the old word plus one.

## Counterexample idea

Do not treat a missing helper as success. Two concrete inputs separate the ELF from a lifter that ignores the reloc and the call.

Shared context, using the raw BTF offsets (not a CO-RE-patched target): `data` and `data_end` are integers that `cast_i2p` can resolve, packet bytes live in that region, and `r1` at entry is the context pointer whose first two `__u32` fields are those integers.

1. **Short packet, no helper.** `data_end == data`. pc 4 produces `data+14`. pc 5's unsigned compare is true. Exit value is 2. pc 14 must not run. A converter that drops pc 5 and still executes `call 1` is wrong on this input. The distinguishing observation is exit value 2 and no call.

2. **Hit versus raw `lddw`.** Packet length at least 34 bytes, bytes at `data+12` are `08 00`, and the `__u32` at `data+26` equals key `K`. The map `blacklist` contains `K → 0`. After a resolved `R_BPF_64_64`, pc 14 is `bpf_map_lookup_elem` on that map and that key, the value becomes 1, and `r0` at exit is 1. The file's raw `lddw` is the constant 0 with `PSEUDO_Constant`. Feeding that constant to an uninterpreted call, or returning a `Vlong` that `exec_store` cannot write, yields either `Stuck` or exit value 2 with the map cell still 0. That is the counterexample to "the immediate in the object is the map" and to "call 1 can be skipped".

A third, separate hole, not required to reject conversion: the kind-0 record on pc 10 relocates the `saddr` byte offset, while `0x22` at pc 8 does not move. On a target where `saddr` is past byte 16, the key's 4 bytes can extend past `data_end` even though pc 9 passed. I am not claiming a specific kernel layout where that happens. The record is the evidence that the offset is relocatable and the bounds immediate is not.

## Gaps (why this is ISSUES, not PASS)

1. `decode_ebpf` rejects the program at pc 1 (`LDX W`). It also has no decoding for pc 2, 6, 12, 13, 14, 18, 20. The lifter has no load, store, `lddw`, or call IR. Conversion cannot start.
2. The map reference is an `R_BPF_64_64` relocation against `blacklist` at `xdp+0x60`. The raw instruction is `Plddw PSEUDO_Constant` of 0. `exec_lddw` writes that 0. It does not read the reloc, and the opcode is not `PSEUDO_MAP_FD` or `PSEUDO_MAP_IDX`.
3. `call 1` is `CallByStaticID`. `exec_instr` returns `Stuck`. The step rule calls an undefined `Variable`. There is no hash-map lookup and no value pointer for the pc 20 store. `exec_store` has no `cast_i2p` path.
4. Four `BPF_FIELD_BYTE_OFFSET` records (kind 0) sit on pc 1, 2, 6, and 10. They are not in `.relxdp`. The bounds immediates `0xe` and `0x22` are not relocated. Neither decoder applies any of this.
5. No proof covers this object. The validator's external-call branch, the part that was read, forces `r0` to a `Vlong` and does not clobber r1–r5, which disagrees with `exec_step_external`.

STATUS: ISSUES
