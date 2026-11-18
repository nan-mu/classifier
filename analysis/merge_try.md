# merge_try observation

Observation for a later implementer. This file does not invent a shared ISA and does not emit an Alive2 program. Conversion result: **NOT CONVERTED**.

## Evidence

Commands actually run:

- `shasum -a 256 /Volumes/SSD/bs/build/merge_try/bpf.o`
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -h -S -s -r -W` on that file
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r --section=xdp` (with and without raw bytes), `-d -r` for the whole file, `-s --section=xdp`, `-s --section=license`, `-s --section=.BTF`, `-s --section=.BTF.ext`
- `bpf.toml` at `/Volumes/SSD/bs/build/merge_try/bpf.toml` (754 bytes). Its `[xdp]` asm matches the objdump mnemonics. Its `[CORE]` records match the `.BTF.ext` core-relo blob parsed below.
- C input named by that toml: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/merge_try.c` (read only as the named source, not as the ISA).

SHA-256 computed: `19432b3394729eb9dd1698f317ba31223d1afe749da03dad0bf14be1a09d88ba`. It matches the expected digest.

Rules read:

- `alive2/src/ebpf.h` (`EbInsn` is only `EbAlu` or `EbJmp`)
- `alive2/src/ebpf_decode.cpp` (whole file)
- `alive2/src/ebpf_lift.cpp` (`build_blocks`, `emit_alu`, `emit_wide`, `emit_narrow`, `emit_cmp`, `icmp_cond`, `concrete` memory flag)
- `alive2/src/ebpf_test.cpp` lines 68–94 (`reject_encoding("LDX", 0x61, ...)`)
- `alive2/rocq/upstream/theories/ebpfDecoder.v` (`decode_insn`, `decode_lddw_insn`, `find_instr`)
- `alive2/rocq/upstream/theories/ebpfSyntax.v` instruction and `aluOp` / `cmpOp` constructors (lines 148–248)
- `alive2/rocq/upstream/theories/ebpfBinSem.v`: `nextinstr`, `eval_reg_immw`, `eval_val_int`, `eval_alu32`, `eval_alu64`, `exec_alu`, the RFC9669 jump comment, `eval_cmp32`, `eval_cmp64`, `exec_jmp32`, `exec_jmp64`, `exec_jmpcmp`, `cast_i2p`, `load`, `exec_load`, `exec_ret` (the live definition at line 819, not the commented one at 811), `exec_instr`, `initial_lst_state`, `final_lst_state`, and `Lemma is_label_correct` (lines 41–47)
- `alive2/rocq/upstream/validator/Extraction.v` lines 13–14 only (`Archi.ptr64` true, `Archi.big_endian` false)
- `tooling/vendor/xpost-elf/src/lib.rs` and `encode.rs` section names (`.xpost.meta`, `.xpost.image`, `.xpost.mem`) so XPOST is not confused with this object

Not read, so not used as rules: `CMemoryModel.v`, `GlobalSem.v`, `SCLanguage.v`, `Nondeterminism.v`, the body of `Validation.v` (a `Theorem`/`Lemma` search returned nothing), CompCert `decode_val`, and `src/Cross/EBPF/*.lean`. The only lemma statement read in `ebpfBinSem.v` is `is_label_correct`, and it is about a `Plabel` constructor, not about these BPF jumps.

## ELF

| field | value |
| --- | --- |
| class / data | ELF64, little endian (`EI_DATA` = 1, 2's complement) |
| type / machine | `REL`, `EM_BPF` |
| entry | `0`. No program headers. This is not an executable image. |
| endianness of the encoding | little endian. Each slot is 8 bytes, opcode at the first byte. |

Executable sections (`AX`), from `llvm-readelf -S`:

| section | off | size | align | role |
| --- | --- | --- | --- | --- |
| `.text` | `0x40` | **0** | 4 | empty. Not the program. |
| `xdp` | `0x40` | **128** (`0x80`) | 8 | the program |

`.text` and `xdp` share file offset `0x40` because `.text` has size 0. `llvm-objdump -d -r` on the whole file prints only `xdp`.

Entry symbol: `merge_try`, `FUNC GLOBAL`, value 0, size 128, section index 3 (`xdp`). One function, one basic entry, slot 0.

Other symbols that are not the program: `FILE merge_try.c`; section symbol `xdp`; `LICENSE` object, size 4, section `license` (`PROGBITS` `WA`, not executable). Section bytes are `47 50 4c 00` (`GPL`).

No `.maps` section. No map symbol. No `.xpost.meta`, `.xpost.image`, or `.xpost.mem`.

## Relocations, CO-RE, maps

There is **no** `.rel.xdp` and **no** relocation against the instruction bytes.

`llvm-readelf -r` relocations are only on debug and BTF metadata:

- `.rel.debug_info`, `.rel.debug_str_offsets`, `.rel.debug_line`: `R_BPF_64_ABS32` to debug section symbols
- `.rel.debug_addr`, `.rel.debug_frame`, `.rel.debug_line`: `R_BPF_64_ABS64` to the section symbol `xdp` or to `LICENSE`
- `.rel.BTF`: one `R_BPF_64_NODYLD32` to `LICENSE` at BTF offset `0x19c`
- `.rel.BTF.ext`: fourteen `R_BPF_64_NODYLD32` to the section symbol `xdp`

Those are raw section-symbol references inside DWARF/BTF. They are not instruction operands, not XPOST relocations, and not map-index references.

`llvm-objdump -d -r` still prints three lines marked `CO-RE <byte_off>`. That text comes from `.BTF.ext`, not from an ELF relocation on `xdp`. Parsed `.BTF.ext` header (little endian): magic `0xeb9f`, version 1, `hdr_len` 32, `core_relo_off` `0xc0`, `core_relo_len` `0x3c`. The core-relo blob starts at section offset `0xe0`: `rec_size` 16, `sec_name_off` `0x73`, `num_info` 3, then three 16-byte records. BTF strings start at header `0x18` + `str_off` `0x18c` = `0x1a4`; string `0x73` is `xdp`. Records, also listed in `bpf.toml` `[CORE]`:

| insn byte off | slot | type id | kind | objdump name | offset already in the slot |
| --- | --- | --- | --- | --- | --- |
| `0x0008` | 1 | 2 | 0 | `struct xdp_md::data_end (0:1)` | `+4` |
| `0x0010` | 2 | 2 | 0 | `struct xdp_md::data (0:0)` | `+0` |
| `0x0030` | 6 | 8 | 0 | `struct ethhdr::h_proto (0:2)` | `+0xc` |

Kind is the integer 0. Objdump labels it `byte_off`. The enum definition was not read in this repo, so it is not given another name here. The numeric offsets in the encoding are the compile-time field offsets. A loader may patch those offset fields later. As stored in this object they are raw encoded immediates/offsets, not relocations.

No LDDW (`opcode 0x18`). `decode_lddw_insn` in `ebpfDecoder.v` (lines 235–246) is therefore unused. In particular there is no `src = R5` / `PSEUDO_MAP_IDX` map-index reference and no `PSEUDO_MAP_FD` / `PSEUDO_MAP_VALUE` reference. `ebpf_test.cpp` also rejects a lone `0x18` as LDDW; this object simply has none.

BTF is present (`.BTF` size `0x3e4`, `.BTF.ext` size `0x11c`). Strings seen in the section dump include `xdp_md`, `data`, `data_end`, `data_meta`, `ingress_ifindex`, `rx_queue_index`, `egress_ifindex`, `ethhdr`, `h_dest`, `h_source`, `h_proto`, `merge_try`, `LICENSE`. The type graph was not fully decoded past the three CO-RE records and those strings.

## Entries and instruction list

One entry: `merge_try` at `xdp+0`, 16 slots, 128 bytes. No second slot of an LDDW. Jump offset is the 16-bit field. Target formula actually read (`ebpf_decode.cpp` `jump_target`, lines 26–31): `index + 1 + off`, because none of these jumps are JMP32 JA (`ja_uses_imm` stays false). Rocq does the same extra one via `nextinstr` (`rs#PC <- offset_ptr PC 1`) after `exec_jmp64` / `exec_jmpcmp` have added `off`.

| slot | bytes (opcode regs off-lo off-hi imm) | class | fields | objdump | target |
| --- | --- | --- | --- | --- | --- |
| 0 | `b4 00 00 00 01 00 00 00` | ALU32 (`0x4`) MOV imm | dst r0, src reg field 0, off 0, imm 1 | `w0 = 0x1` | fall 1 |
| 1 | `61 12 04 00 00 00 00 00` | LDX (`0x1`) MEM W | dst r2, src r1, off 4, imm 0 | `w2 = *(u32 *)(r1 + 0x4)` | fall 2 |
| 2 | `61 11 00 00 00 00 00 00` | LDX MEM W | dst r1, src r1, off 0, imm 0 | `w1 = *(u32 *)(r1 + 0x0)` | fall 3 |
| 3 | `bf 13 00 00 00 00 00 00` | ALU64 (`0x7`) MOV reg | dst r3, src r1, off 0, imm 0 | `r3 = r1` | fall 4 |
| 4 | `07 03 00 00 0e 00 00 00` | ALU64 ADD imm | dst r3, src reg field 0, off 0, imm 14 | `r3 += 0xe` | fall 5 |
| 5 | `2d 23 09 00 00 00 00 00` | JMP (`0x5`) JGT reg | dst r3, src r2, off +9, imm 0 | `if r3 > r2 goto +9` | taken 15, else 6 |
| 6 | `69 13 0c 00 00 00 00 00` | LDX MEM H | dst r3, src r1, off 12, imm 0 | `w3 = *(u16 *)(r1 + 0xc)` | fall 7 |
| 7 | `16 03 04 00 86 dd 00 00` | JMP32 (`0x6`) JEQ imm | dst r3, src reg field 0, off +4, imm `0x0000dd86` | `if w3 == 0xdd86 goto +4` | taken 12, else 8 |
| 8 | `56 03 06 00 08 00 00 00` | JMP32 JNE imm | dst r3, off +6, imm 8 | `if w3 != 0x8 goto +6` | taken 15, else 9 |
| 9 | `07 01 00 00 22 00 00 00` | ALU64 ADD imm | dst r1, imm `0x22` | `r1 += 0x22` | fall 10 |
| 10 | `2d 21 04 00 00 00 00 00` | JMP JGT reg | dst r1, src r2, off +4 | `if r1 > r2 goto +4` | taken 15, else 11 |
| 11 | `05 00 02 00 00 00 00 00` | JMP JA | dst 0, src 0, off +2, imm 0 | `goto +2` | 14 |
| 12 | `07 01 00 00 36 00 00 00` | ALU64 ADD imm | dst r1, imm `0x36` | `r1 += 0x36` | fall 13 |
| 13 | `2d 21 01 00 00 00 00 00` | JMP JGT reg | dst r1, src r2, off +1 | `if r1 > r2 goto +1` | taken 15, else 14 |
| 14 | `b4 00 00 00 02 00 00 00` | ALU32 MOV imm | dst r0, imm 2 | `w0 = 0x2` | fall 15 |
| 15 | `95 00 00 00 00 00 00 00` | JMP EXIT | dst 0, src 0, off 0, imm 0 | `exit` | halt, value r0 |

Jump slots: 5, 7, 8, 10, 11, 13, and EXIT at 15. Every taken offset is strictly positive, so no back edge. `Lifter::build_blocks` would set `loop` only when `tgt <= i` (`ebpf_lift.cpp` lines 228–229). That function is not reached for this object (decode throws first). From the bytes alone, the loop flag is false.

Leaders the same function would mark, if decode succeeded: 0, and the target plus the fall-through of every non-exit jump. Blocks:

| block | slots | exit edge |
| --- | --- | --- |
| b0 | 0–5 | taken b7 (slot 15), else b1 (slot 6) |
| b1 | 6–7 | taken b5 (slot 12), else b2 (slot 8) |
| b2 | 8 | taken b7, else b3 (slot 9) |
| b3 | 9–10 | taken b7, else b4 (slot 11) |
| b4 | 11 | JA to b6 (slot 14) |
| b5 | 12–13 | taken b7, else b6 |
| b6 | 14 | fall into b7 |
| b7 | 15 | exit |

The C source's "shared suffix" is only slots 14–15 (`w0 = 2; exit`). The ethernet length check is the shared prefix (slot 5, `+0xe`). The IPv4 check (`+0x22` at slot 9) and the IPv6 check (`+0x36` at slot 12) are separate arms. They are not one bounds check after the ethertype split.

`r1` is the context pointer only at slots 0–1. Slot 2 overwrites `r1` with the loaded `data` word. Slot 6's base is that value, not the original context. `r10` is never named. No call, no store, no atomic, no stack spill.

## Real disassembly

`llvm-objdump -d -r --section=xdp /Volumes/SSD/bs/build/merge_try/bpf.o`:

```
0000000000000000 <merge_try>:
       0:	b4 00 00 00 01 00 00 00	w0 = 0x1
       1:	61 12 04 00 00 00 00 00	w2 = *(u32 *)(r1 + 0x4)
		0000000000000008:  CO-RE <byte_off> [2] struct xdp_md::data_end (0:1)
       2:	61 11 00 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x0)
		0000000000000010:  CO-RE <byte_off> [2] struct xdp_md::data (0:0)
       3:	bf 13 00 00 00 00 00 00	r3 = r1
       4:	07 03 00 00 0e 00 00 00	r3 += 0xe
       5:	2d 23 09 00 00 00 00 00	if r3 > r2 goto +0x9 <L2>
       6:	69 13 0c 00 00 00 00 00	w3 = *(u16 *)(r1 + 0xc)
		0000000000000030:  CO-RE <byte_off> [8] struct ethhdr::h_proto (0:2)
       7:	16 03 04 00 86 dd 00 00	if w3 == 0xdd86 goto +0x4 <L0>
       8:	56 03 06 00 08 00 00 00	if w3 != 0x8 goto +0x6 <L2>
       9:	07 01 00 00 22 00 00 00	r1 += 0x22
      10:	2d 21 04 00 00 00 00 00	if r1 > r2 goto +0x4 <L2>
      11:	05 00 02 00 00 00 00 00	goto +0x2 <L1>
<L0>:
      12:	07 01 00 00 36 00 00 00	r1 += 0x36
      13:	2d 21 01 00 00 00 00 00	if r1 > r2 goto +0x1 <L2>
<L1>:
      14:	b4 00 00 00 02 00 00 00	w0 = 0x2
<L2>:
      15:	95 00 00 00 00 00 00 00	exit
```

Section bytes (`-s --section=xdp`) match those slots from `0000` through `0070`.

## Semantic rules read

C++ decode (`ebpf_decode.cpp`) accepts only classes `kAlu` `0x04`, `kJmp` `0x05`, `kJmp32` `0x06`, and `kAlu64` `0x07`. Anything else throws `unsupported class in opcode 0x...` (lines 164–167). Opcode high nibble is `kOp`, bit `0x08` selects register source.

Rocq `decode_insn` (`ebpfDecoder.v`) uses the same class split, and it also decodes LDX/ST/STX. Size under MEM mode (`opcode >> 5 == 3`): size field `(opcode >> 3) & 3` is Word, HalfWord, Byte, DBWord for 0, 1, 2, 3 (lines 165–172). `0x61` is LDX + MEM + Word. `0x69` is LDX + MEM + HalfWord. Both require imm 0, which these slots have. They decode as `Pload Word` / `Pload HalfWord`, not as signed loads (`Ploadsx` is mode `opcode >> 5 == 4`).

Per slot, against code that was read:

| slot | C++ `decode_ebpf` | Rocq `decode_insn` | rule for the effect |
| --- | --- | --- | --- |
| 0 | `EbAlu` W32 `Mov`, imm 1 | `Palu MOV W32 r0 (inr 1)` | `eval_alu32` MOV is `Val.longofintu` of the imm (`ebpfBinSem.v` 349). High 32 bits become 0. |
| 1 | **reject** class `0x1` | `Pload Word r2 r1 off 4` | `exec_load` (`575–588`). See memory below. |
| 2 | **reject** class `0x1` | `Pload Word r1 r1 off 0` | same, and the destination is the base register |
| 3 | `EbAlu` W64 `Mov`, src r1 | `Palu MOV W64 r3 (inl r1)` | `eval_alu64` MOV returns the source value (`371`). Copy, no extension. |
| 4, 9, 12 | `EbAlu` W64 `Add`, imm | `Palu ADD W64` with imm | `eval_val_int` W64 sign-extends the imm through `int64_of_int` (`81`, `108–115`). These imms are positive (`14`, `0x22`, `0x36`). `eval_alu64` ADD is `Val.addl` (`358`). |
| 5, 10, 13 | `EbJmp` W64 `Jgt`, src reg | `Pjmpcmp (GT Unsigned) W64` | `eval_cmp64` uses `Val.cmplu_bool ... Cgt` (`435`). Unsigned, strict. `None` becomes `Stuck` (`494`). |
| 6 | **reject** class `0x1` | `Pload HalfWord r3 r1 off 12` | `load` HalfWord is `loadv_unaligned Mint16unsigned` (`563`). Result cast by `load_value_casting`: `Vint` becomes `Vlong` of `Int.unsigned` (`569–572`), so the u16 is zero-extended to 64. |
| 7 | `EbJmp` W32 `Jeq`, imm `0xdd86` | `Pjmpcmp EQ W32` | `eval_cmp32` compares `Val.loword` of the dst to `Vint` imm (`412–416`). Not a 64-bit compare. Imm `0xdd86` is positive as int32. |
| 8 | `EbJmp` W32 `Jne`, imm 8 | `Pjmpcmp NE W32` | same width, `Cne` (`426`) |
| 11 | `EbJmp` W64 `Ja`, off 2, imm must be 0 | `Pjmp64 off` | `exec_jmp64` (`449–450`) then `nextinstr` adds 1. C++ rejects a non-zero JA imm (`142–143`); this imm is 0. |
| 14 | same as slot 0 with imm 2 | `Palu MOV W32 r0 (inr 2)` | zero-extended 2 |
| 15 | `EbJmp` `Exit` | `Pret` | C++ requires class JMP, no reg source, off 0, dst 0, src 0 (`130–133`). Rocq `exec_ret` on an empty call stack sets `PC` to `Vnullptr` and leaves `R0` (`819–821`). It does not undef caller-saved registers on that path. `final_lst_state` (`1010–1017`) also demands `R0` is `Vlong` or `Vptr` and `R10` is still the initial stack pointer. |

`initial_lst_state` (`993–1007`) starts `PC` at the code block, `R1` as `Vptr ctx 0`, `R10` as the 512-byte stack pointer, other registers `Vundef`, call stack empty. This program never writes `R10`.

ALU32 immediates in the C++ lifter are zero-extended (`imm64(..., sign_imm)` is sign-extending only for W64, `ebpf_lift.cpp` 196–200 and 523–530), then truncated and zero-extended back to i64 (`emit_alu` 533–539). That matches `Val.longofintu` for these two positive MOV immediates. ALU64 add immediates are sign-extended in both.

JMP32 immediates in `emit_cmp` are `c32(uint32_t imm)` (`649–650`), a 32-bit constant, compared after `trunc32` of the register. That matches `eval_cmp32` using the low word, not `int64_of_int`.

## IR mapping against the existing C++ lifter only

`EbInsn::op` cannot represent a load (`ebpf.h` lines 38–41). `decode_ebpf` throws at slot 1 (`opcode 0x61`) with `eBPF insn 1: unsupported class in opcode 0x61`. `ebpf_test.cpp` line 84 locks that rejection. `Lifter::run` is not entered. No block, phi, or return is built. The concrete tracer initializes `trace.memory` to `MemorySummary::Empty` and only sets `Changed` if it sees a `MemInstr` (`ebpf_lift.cpp` 747 and 963–965). This lifter never emits `MemInstr`.

If the three loads were absent, the lifter's existing emitters would be:

| slots | emitter | Alive2 IR the current code builds |
| --- | --- | --- |
| 0, 14 | `emit_narrow` MOV then `zext64` | i32 constant 1 or 2, zero-extended to i64, written to r0 |
| 3 | `emit_wide` MOV | r3 becomes the current value pointer of r1, no operation |
| 4, 9, 12 | `binop` i64 `BinOp::Add` | r3 or r1 plus a sign-extended i64 immediate |
| 5, 10, 13 | `emit_cmp` then `Branch` | `ICmp` `UGT` on the full i64 values; true edge is the jump target, false edge is the next block (`succ[0]`, `succ[1]`, lines 264–267 and 501–503) |
| 7 | `emit_cmp` W32 | `trunc32` r3, `ICmp` `EQ` against i32 `0xdd86` |
| 8 | `emit_cmp` W32 | `trunc32` r3, `ICmp` `NE` against i32 `8` |
| 11 | `Branch` with no condition | direct branch to the block at slot 14 |
| 15 | `Return(i64, r0)` | returns the i64 in r0. No memory operand. |

There is no load emitter to map slots 1, 2, and 6 onto. Mapping them to a `MemInstr` would be an invention. They stay unmapped.

`pointer_alu` / `pointer_jmp` (`347–362`) only flag sites. They do not synthesize a packet memory. After a real u32 load, r1/r2 would be scalars; the C++ lifter never produces those scalars because it cannot decode the load. If r1 stayed the initial poison pointer (`init_regs`, lines 315–321), the later JGT sites would be marked `pointer_use` and the concrete tracer would refuse a non-concrete register. That is not a model of `xdp_md`.

## Memory, helper, map, loop

- **Memory: required, and missing from the C++ lifter.** Three loads, all little-endian unsigned, all with imm 0.
  - Slot 1: u32 at `ctx+4`, zero-extended into r2. CO-RE name `xdp_md.data_end`.
  - Slot 2: u32 at `ctx+0`, zero-extended into r1, replacing the context pointer. CO-RE name `xdp_md.data`.
  - Slot 6: u16 at `r1+12`, zero-extended into r3. CO-RE name `ethhdr.h_proto`. Base is the integer just loaded, not `ctx`.
- Rocq `exec_load`: if the base is `Vptr`, the address is `Val.offset_ptr`. If the base is `Vlong`, the address is `cast_i2p` of `base + signed(off)` through `addr_map` (`575–580`, `512–521`). A `Vlong` that hits no region is `Stuck`. So the two context loads can be ordinary CompCert loads from the `ctx` block, but the packet halfword is reachable only if some `addr_map` region covers the integer that was stored in `xdp_md.data`. Nothing in the C++ lifter builds `ctx`, the packet, or `addr_map`.
- `Extraction.v` forces `Archi.big_endian = false`. `load` uses `Mint32` / `Mint16unsigned` via `Mem.loadbytes` and `decode_val`. CompCert's `decode_val` itself was not read. The immediates in this object match a little-endian load of network-order ethertypes: bytes `08 00` become `0x0008`, bytes `86 dd` become `0xdd86`. Those are the constants at slots 8 and 7. The source file names them `bpf_htons(ETH_P_IP)` and `bpf_htons(ETH_P_IPV6)` with `ETH_P_IP = 0x0800` and `ETH_P_IPV6 = 0x86DD`.
- No store. The packet and the context are read-only in this program.
- **Helper: no.** No `0x85` CALL. `exec_instr` does not take the `Pcall` path. `ebpf_call_function` is unused.
- **Map: no.** No map section, no map symbol, no LDDW, no map-index pseudo.
- **Loop: no.** All six branch offsets and the JA offset are forward. EXIT ends the function. No tail call.

`r0` is 1 from slot 0 until slot 14. The source returns `XDP_DROP` on every failing check and `XDP_PASS` on the shared success tail. Those macro values were not read from a header; the encoded immediates are 1 and 2.

## Conversion result

**NOT CONVERTED.**

No `.alive` file is emitted. `decode_ebpf` rejects slot 1 before `Lifter::run`. The same rejection applies to slot 6. Calling the missing load model `UNSUPPORTED` and treating the ALU/JMP fragment as a successful lift would drop the three loads that decide the return value. That is not a conversion.

## Proof coverage

No proof in the files that were read covers this object.

- `ebpfBinSem.v` defines `exec_alu`, `exec_jmpcmp`, `exec_jmp64`, `exec_load`, and `exec_ret`, but the only lemma read there is `is_label_correct`, which talks about `Plabel` and does not mention these opcodes.
- `Validation.v` had no `Theorem` or `Lemma` hit in a search. Its body was not read. Nothing there is claimed as a proof of `merge_try`.
- The C++ test suite asserts the opposite of a successful lift: opcode `0x61` must throw (`ebpf_test.cpp` 84).
- No theorem was read that relates these 16 slots to the C source, to XDP return codes, or to an Alive2 refinement.

## Counterexample idea

Hand evaluation from the rules above, not a tool trace. Let the u32 at `ctx+0` be `0x1000` (`data`) and the u32 at `ctx+4` be `0x1022` (`data_end`, exactly 34 bytes later). Packet bytes at `data+12` are `08 00`.

- Slot 0 writes r0 = 1.
- Slots 1–2 write r2 = `0x1022`, r1 = `0x1000`, both zero-extended.
- Slots 3–4 write r3 = `0x100e`.
- Slot 5: unsigned `0x100e > 0x1022` is false.
- Slot 6: u16 load is `0x0008`, zero-extended, not sign-extended.
- Slot 7: low 32 bits `0x8 == 0xdd86` is false.
- Slot 8: `0x8 != 0x8` is false.
- Slots 9–10: r1 = `0x1022`. Unsigned `0x1022 > 0x1022` is false. The compare is strict (`Cgt` / `ICmp UGT`). An implementer who uses `>=` drops this packet.
- Slot 11 jumps to 14. Slot 14 writes r0 = 2. Slot 15 returns 2.

The same length with bytes `86 dd` at `data+12` loads `0xdd86`, takes slot 7 to slot 12, adds `0x36`, and `0x1036 > 0x1022` is true, so the return stays 1. One merged L3 offset cannot return 2 for the first packet and 1 for the second.

A second distinguishing bug: a signed u16 load of `86 dd` yields a value whose low 32 bits are `0xffffdd86`. Slot 7's JMP32 equality is against `0x0000dd86`, so it fails, slot 8 also fails, and a long IPv6 packet (for example `data_end = data + 0x36`) returns 1 instead of 2.

## Status

ISSUES
