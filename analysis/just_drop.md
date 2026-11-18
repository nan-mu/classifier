Produce an observation report for just_drop so a later implementer can compile it, without inventing a shared ISA.

Conversion result: NOT CONVERTED. No `.alive` file is emitted. Status at the end is ISSUES.

# Identity

- ELF: `/Volumes/SSD/bs/build/just_drop/bpf.o`
- sha256 (computed, matches the given digest): `78090f2b29c64caea9ff52f2ede01ab27f3b69e4c46be41030105760f7c9ed24`
- Command: `shasum -a 256 /Volumes/SSD/bs/build/just_drop/bpf.o`
- Notes (not the object): `/Volumes/SSD/bs/build/just_drop/bpf.toml` (`source` points at `just_drop.c`; `[xdp].size = 272`)
- Tools actually run: `/opt/homebrew/opt/llvm/bin/llvm-readelf -a -W`, `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r -s` on section `xdp1`, plus `-s` on `maps`, `license`, `.BTF`
- Endianness: ELF64, `EI_DATA` little endian, `e_machine` EM_BPF, `e_type` ET_REL, `e_entry` 0, no program headers. Instruction slots are little-endian 8-byte words.
- File facts from readelf: 27 sections, section-header offset `0x2188`.

# Executable sections

| idx | name | flags | size | role |
|-----|------|-------|------|------|
| 2 | `.text` | AX | 0 | empty. Not the program. |
| 3 | `xdp1` | AX | `0x110` (272) | the only nonzero executable section. 34 raw slots. |

No other section has `SHF_EXECINSTR`. There is no `.xpost.meta`, `.xpost.mem`, or other Compact-ELF section (`tooling/vendor/xpost-elf` is a different container; this file is not one).

# Entry

- Symbol `xdp_prog1`: FUNC GLOBAL, section `xdp1` (index 3), value 0, size 272. This is the entry.
- Symbol `xdp1`: SECTION LOCAL, index 3.
- Symbol `counter`: OBJECT GLOBAL, section `maps` (index 5), value 0, size 20.
- Symbol `LICENSE`: OBJECT GLOBAL, section `license` (index 6), value 0, size 4. Section bytes are `47 50 4c 00` (`GPL`).
- `e_entry` is 0 and there are no program headers, so the entry is the function symbol, not an ELF entry point.

# Maps image (raw object, not a relocation)

Section `maps` is 20 bytes, the usual `bpf_map_def` layout of five little-endian u32s:

| field | bytes | value |
|-------|-------|-------|
| type | `02 00 00 00` | 2 |
| key_size | `04 00 00 00` | 4 |
| value_size | `08 00 00 00` | 8 |
| max_entries | `00 01 00 00` | 256 |
| map_flags | `00 00 00 00` | 0 |

`bpf.toml` names that row `counter` / `BPF_MAP_TYPE_ARRAY` with the same sizes. `aot_addr = 0x4038028c` is only in the toml. It is not a field in this ELF and it is not an instruction immediate.

# Relocations vs raw immediates vs XPOST vs map index

Program relocation section `.relxdp1` has one entry (readelf):

```
00000000000000c8  0000000c00000001 R_BPF_64_64  counter
```

Symbol index `0xc` is `counter`. Type 1 is `R_BPF_64_64`. Offset `0xc8` is slot 25 (`0xc8 / 8 = 25`), the LDDW low slot. llvm-objdump prints the same site as `R_BPF_64_64 counter`.

Three different things, not to be merged:

1. Raw object reference. Slot 25 bytes are `18 01 00 00 00 00 00 00` and slot 26 is eight zero bytes. Opcode `0x18`, dst `r1`, src field `0`, offset `0`, imm `0`, next imm `0`. In `alive2/rocq/upstream/theories/ebpfSyntax.v` the src-field table says src `0x0` is `dst = (next_imm << 32) | imm` (a constant). `decode_lddw_insn` (`ebpfDecoder.v` lines 235–237) maps src `R0` to `Plddw PSEUDO_Constant`. The constant in the file is 0. That is what the bytes say before relocation.
2. ELF map relocation, not an XPOST relocation. `R_BPF_64_64` against symbol `counter` is the libbpf map-fd/map-object fixup for that LDDW. There is no XPOST relocation record and no compact-ELF section. Do not invent one.
3. Map-index reference. None. A map index would be LDDW src field `0x5` (`PSEUDO_MAP_IDX` in `ebpfSyntax.v` lines 211–217 and `decode_lddw_insn` on `R5`). This src field is 0, and the immediate is not a map index.

CO-RE records are a fourth channel. They are not in `.relxdp1`. llvm-objdump `-d` prints them from `.BTF.ext`, and `bpf.toml` `[CORE]` lists the same five. Kind is field byte-offset. The raw instruction already contains the compile-time offset; nothing in `.relxdp1` rewrites it.

| byte offset | slot | raw field already in the insn | BTF type (objdump / toml) | access |
|-------------|------|-------------------------------|---------------------------|--------|
| `0x00` | 0 | LDX.W offset `4` | `xdp_md.data_end` | `0:1` |
| `0x08` | 1 | LDX.W offset `0` | `xdp_md.data` | `0:0` |
| `0x28` | 5 | LDX.H offset `12` | `ethhdr.h_proto` | `0:2` |
| `0x68` | 13 | LDX.H offset `2` | `vlan_hdr.h_vlan_encapsulated_proto` | `0:1` |
| `0x98` | 19 | ALU64 MOV imm `12` | `iphdr` anon `saddr` | `0:9:0:0` |

`.BTF` string dump (llvm-objdump `-s --section=.BTF`) contains the source text those records came from, including `bpf_htons(ETH_P_8021Q)`, `bpf_htons(ETH_P_8021AD)`, `bpf_htons(ETH_P_IP)`, `return octets[3]`, and `bpf_map_lookup_elem(&counter, &key)`. Other reloc sections (`.rel.debug_*`, `.rel.BTF`, `.rel.BTF.ext`) point at debug/BTF metadata (`R_BPF_64_ABS32`, `R_BPF_64_ABS64`, `R_BPF_64_NODYLD32` for `LICENSE` and `counter`). They are not instruction operands.

# Real disassembly

Command: `llvm-objdump -d -r --section=xdp1`. Raw bytes from `llvm-objdump -s --section=xdp1`, checked slot by slot against that disassembly. LDDW is two slots (25 and 26). Jump offsets are slot counts from the next slot, matching `jump_target` in `alive2/src/ebpf_decode.cpp` lines 26–31 (`index + 1 + off`).

```
0000000000000000 <xdp_prog1>:
       0: 61 12 04 00 00000000   w2 = *(u32 *)(r1 + 4)          CO-RE xdp_md.data_end
       1: 61 11 00 00 00000000   w1 = *(u32 *)(r1 + 0)          CO-RE xdp_md.data
       2: bf 13 00 00 00000000   r3 = r1
       3: 07 03 00 00 0e000000   r3 += 14
       4: 2d 23 1b 00 00000000   if r3 > r2 goto +27 -> slot 32
       5: 69 15 0c 00 00000000   w5 = *(u16 *)(r1 + 12)         CO-RE ethhdr.h_proto
       6: 16 05 02 00 81000000   if w5 == 0x81 goto +2 -> slot 9
       7: b7 04 00 00 0e000000   r4 = 14
       8: 56 05 05 00 88a80000   if w5 != 0xa888 goto +5 -> slot 14
       9: bf 14 00 00 00000000   r4 = r1
      10: 07 04 00 00 12000000   r4 += 18
      11: 2d 24 14 00 00000000   if r4 > r2 goto +20 -> slot 32
      12: b7 04 00 00 12000000   r4 = 18
      13: 69 35 02 00 00000000   w5 = *(u16 *)(r3 + 2)          CO-RE vlan encapsulated proto
      14: 56 05 11 00 08000000   if w5 != 8 goto +17 -> slot 32
      15: 0f 41 00 00 00000000   r1 += r4
      16: bf 13 00 00 00000000   r3 = r1
      17: 07 03 00 00 14000000   r3 += 20
      18: 2d 23 0d 00 00000000   if r3 > r2 goto +13 -> slot 32
      19: b7 02 00 00 0c000000   r2 = 12                         CO-RE iphdr.saddr
      20: 0f 21 00 00 00000000   r1 += r2
      21: 71 11 03 00 00000000   w1 = *(u8 *)(r1 + 3)
      22: 63 1a fc ff 00000000   *(u32 *)(r10 - 4) = w1
      23: bf a2 00 00 00000000   r2 = r10
      24: 07 02 00 00 fcffffff   r2 += -4
      25: 18 01 00 00 00000000   r1 = 0 ll                       R_BPF_64_64 counter
      26: 00 00 00 00 00000000   LDDW high half (not an insn)
      27: 85 00 00 00 01000000   call 1
      28: 15 00 03 00 00000000   if r0 == 0 goto +3 -> slot 32
      29: 79 01 00 00 00000000   r1 = *(u64 *)(r0 + 0)
      30: 07 01 00 00 01000000   r1 += 1
      31: 7b 10 00 00 00000000   *(u64 *)(r0 + 0) = r1
      32: b4 00 00 00 01000000   w0 = 1
      33: 95 00 00 00 00000000   exit
```

The u16 immediates `0x81`, `0xa888`, and `0x8` are the little-endian values of on-wire big-endian ethertypes `0x8100`, `0x88a8`, and `0x0800`. That matches the BTF strings `bpf_htons(ETH_P_8021Q)`, `bpf_htons(ETH_P_8021AD)`, and `bpf_htons(ETH_P_IP)`. I did not read the CompCert `Archi.big_endian` flag this Rocq tree is built with.

What the bytes do, as a program, not as a new ISA: `r1` arrives as `xdp_md *`. Load `data_end` into `r2` and `data` into `r1` as u32 (the BTF type of those fields is `__u32`; the load must zero-extend). Require `data+14 <= data_end`. Read `h_proto`. Non-VLAN uses header length 14. VLAN (`0x81` or `0xa888`) uses length 18 after a second bounds check and reloads the encapsulated proto. Require IPv4 (`0x8`). Advance to the IPv4 header, require 20 bytes, take `saddr`'s last octet (`offset 12`, then byte `+3`, which is not itself a CO-RE site), spill it as a u32 key at `r10-4`, and call helper immediate 1 with `r1` = the relocated map and `r2` = `&key`. If the pointer in `r0` is non-null, add 1 to the u64 at `*r0` with a plain load/add/store (not an atomic, not a second helper). Then `w0 = 1` and exit on every path, including the early bounds failures. `bpf.toml` agrees with this disassembly. I did not read a helper-id table in this repo; the name `bpf_map_lookup_elem` is the BTF string at the call, and the immediate in the slot is 1.

# Jump slot positions

All offsets are forward. No target equals the LDDW high slot 26. No target is past slot 33.

| slot | opcode | off | target slot | label in objdump |
|------|--------|-----|-------------|------------------|
| 4 | JMP64 JGT X | +27 | 32 | L2 |
| 6 | JMP32 JEQ K | +2 | 9 | L0 |
| 8 | JMP32 JNE K | +5 | 14 | L1 |
| 11 | JMP64 JGT X | +20 | 32 | L2 |
| 14 | JMP32 JNE K | +17 | 32 | L2 |
| 18 | JMP64 JGT X | +13 | 32 | L2 |
| 28 | JMP64 JEQ K | +3 | 32 | L2 |
| 33 | EXIT | — | — | — |

Leaders if every non-jump were legal and jumps stayed jumps (this is the rule in `build_blocks`, `ebpf_lift.cpp` lines 214–233; it does not run, because decode throws first): 0, 5, 7, 9, 12, 14, 15, 19, 29, 32. Slot 33 is not its own leader; it is the EXIT terminator of the block that starts at 32. Join points are 9 (fall from 8, taken from 6), 14 (taken from 8, fall from 12–13), and 32 (six taken edges plus fall from 29–31). `loop` would be false: `build_blocks` sets it only when `tgt <= i` (line 228). There is no back-edge.

# Instruction classification against code that was read

`decode_ebpf` (`alive2/src/ebpf_decode.cpp`) only accepts class ALU (`0x04`), JMP (`0x05`), JMP32 (`0x06`), and ALU64 (`0x07`). Any other class throws `unsupported class` at lines 164–167. `EbInsn` (`alive2/src/ebpf.h` lines 38–41) is only `EbAlu` or `EbJmp`. The test `reject_unknown` (`alive2/src/ebpf_test.cpp` lines 82–88) expects LDX `0x61`, ST `0x62`, STX `0x63`, LDDW `0x18`, and CALL `0x85` to throw.

Slot 0 is opcode `0x61`. Classification of the image stops there for the C++ lifter: `decode_ebpf` throws `eBPF insn 0: unsupported class in opcode 0x61`. `lift_ebpf` is not reached. The rows below still classify every slot against the decoder, the lifter, and the Rocq decoder that was read.

| slot | raw opcode | C++ `decode_ebpf` | Rocq `decode_insn` / `find_instr` (`ebpfDecoder.v`) |
|------|------------|-------------------|-----------------------------------------------------|
| 0, 1 | `0x61` LDX W MEM | reject, class LDX | `Pload Word` (lines 165–177). imm must be 0, it is. |
| 2, 9, 16, 23 | `0xbf` ALU64 MOV X | `EbAlu::Mov` W64 reg | `Palu MOV W64` (lines 80–83) |
| 3, 10, 17, 30 | `0x07` ALU64 ADD K | `EbAlu::Add` W64 imm | `Palu ADD W64` (line 58) |
| 4, 11, 18 | `0x2d` JMP64 JGT X | `EbJmp::Jgt` W64 reg | `Pjmpcmp (GT Unsigned) W64` (line 147) |
| 5, 13 | `0x69` LDX H MEM | reject, class LDX | `Pload HalfWord` |
| 6 | `0x16` JMP32 JEQ K | `EbJmp::Jeq` W32 imm | `Pjmpcmp EQ W32` (line 146) |
| 7, 12, 19 | `0xb7` ALU64 MOV K | `EbAlu::Mov` W64 imm | `Palu MOV W64` (line 89) |
| 8, 14 | `0x56` JMP32 JNE K | `EbJmp::Jne` W32 imm | `Pjmpcmp NE W32` (line 150) |
| 15, 20 | `0x0f` ALU64 ADD X | `EbAlu::Add` W64 reg | `Palu ADD W64` |
| 21 | `0x71` LDX B MEM | reject, class LDX | `Pload Byte` |
| 22 | `0x63` STX W MEM | reject, class STX | `Pstore Word` from reg (lines 180–181) |
| 24 | `0x07` imm `0xfffffffc` | `EbAlu::Add` W64 imm `-4` | `Palu ADD W64` |
| 25–26 | `0x18` LDDW, src 0, imm 0 | reject at 25, class LD. Slot 26 is not a separate decode. | `find_instr` lines 268–276: opcode `0x18`, reserved half must be 0, then `Plddw PSEUDO_Constant r1 0 0`. Reloc is ignored. |
| 27 | `0x85` JMP CALL, src 0, imm 1 | class JMP, code nibble `0x8` is not in the switch at lines 146–158, so `unsupported jump opcode` | `Pcall CallByStaticID` imm 1 (lines 127–130) |
| 28 | `0x15` JMP64 JEQ K | `EbJmp::Jeq` W64 imm 0 | `Pjmpcmp EQ W64` |
| 29 | `0x79` LDX DW MEM | reject, class LDX | `Pload DBWord` |
| 31 | `0x7b` STX DW MEM | reject, class STX | `Pstore DBWord` from reg |
| 32 | `0xb4` ALU32 MOV K imm 1 | `EbAlu::Mov` W32 imm 1 | `Palu MOV W32` |
| 33 | `0x95` EXIT | `EbJmp::Exit` (lines 130–133) | `Pret` (lines 137–138) |

# Semantic rules actually read

Read and used:

- `alive2/src/ebpf_decode.cpp` entire file. ALU/JMP decode, `jump_target`, and the class reject.
- `alive2/src/ebpf.h` lines 1–58. `EbAlu`, `EbJmp`, `LiftBug`. No memory, call, or lddw form.
- `alive2/src/ebpf_lift.cpp` entire file. IR emission and the concrete evaluator.
- `alive2/src/ebpf_lift.h` entire file. `LiftInfo.loop`, register origins, no memory type.
- `alive2/src/ebpf_test.cpp` lines 67–97. The reject list named above.
- `alive2/src/ebpf_exhibit.cpp` lines 244–247. Quote: supported-scope-equivalent does not cover loops, memory, maps, helpers, pointer arithmetic, or poison beyond `non_poison`.
- `alive2/rocq/upstream/theories/ebpfSyntax.v` lines 19–245. Registers through `R10` (frame pointer) and `RAX`; `Pload` / `Pstore` / `Plddw` / `Pcall` / `Palu` / `Pjmpcmp` / `Pret`; pseudo-pointer src table.
- `alive2/rocq/upstream/theories/ebpfDecoder.v` entire file. `decode_insn`, `decode_lddw_insn`, `find_instr`.
- `alive2/rocq/upstream/theories/ebpfBinSem.v` at the lines cited below, not as a proof about this ELF.
- `alive2/rocq/upstream/validator/Validation.v` lines 1–45. `bpf_interpreter` calls `find_instr` then `exec_instr`. It has no case that reads an ELF relocation.

Rules that apply to opcodes in this image:

- ALU64 immediate is signed. `eval_val_int` (`ebpfBinSem.v` lines 108–115) uses `int64_of_int`, which is `Int64.repr (Int.signed i)` (line 81). The comment at lines 90–92 says the immediate is signed. C++ `imm64` (`ebpf_lift.cpp` lines 196–200) sign-extends ALU64 immediates unless `LiftBug::ImmNoSignExtend`. Slot 24's `0xfffffffc` is therefore `-4` on both sides. Positive immediates `14`, `18`, `20`, `12`, `1` do not change under sign extension.
- ALU64 MOV copies the source (`eval_alu64` line 371, `emit_wide` lines 564–565 returns `src`). ALU64 ADD is `Val.addl` (line 358) and C++ `BinOp::Add` (`arith_op`, lines 656–658).
- ALU32 MOV zero-extends into 64 bits. `eval_alu32` MOV is `Val.longofintu src` (line 349). C++ `emit_alu` for W32 (lines 536–539) truncates to i32, moves, then `zext64`. Slot 32 (`w0 = 1`) clears the high half. `LiftBug::Alu32AsAlu64` would not; this report assumes `LiftBug::None`.
- JMP64 JGT is unsigned. Rocq `GT Unsigned` goes to `Val.cmplu_bool ... Cgt` (`eval_cmp64`, lines 429–435). C++ `icmp_cond` maps `Jgt` to `ICmp::UGT` (line 683). Taken target is `pc + off` then one more instruction (`exec_jmpcmp` lines 495–497; `nextinstr` is `PC + 1`, lines 66–67), i.e. `pc + 1 + off`.
- JMP32 compares the low 32 bits. `eval_cmp32` uses `Val.loword` (lines 412–414). C++ `emit_cmp` truncates both sides to i32 (lines 643–652) and the imm is the zero-extended 32-bit immediate, not a sign-extended i64.
- JNE is `Cne` in `eval_cmp32` / `eval_cmp64` (lines 426 and 443). C++ symbolic IR maps `Jne` to `ICmp::NE` (line 682). The concrete evaluator in the same file does not: its `ICmp` switch accepts only `EQ` and `UGT` (lines 916–921) and otherwise `stop_unsupported`. Slots 8 and 14 are in that hole.
- LDX unsigned sizes. `exec_load` (`ebpfBinSem.v` lines 575–588) offsets a `Vptr`, or `cast_i2p`s a `Vlong`, then `load` of `Mint8unsigned` / `Mint16unsigned` / `Mint32` / `Mint64` (lines 560–566). `load_value_casting` zero-extends a `Vint` to `Vlong` (lines 569–572). A failed address or load is `Stuck`, not a drop. This program's failed bounds checks are explicit jumps to `w0 = 1; exit`, not `Stuck`.
- STX. `exec_store` (lines 642–645) stores `eval_reg_immw (sizew k)` at `dst+offset`. Word and byte sizes use width W32 (`sizew` in `ebpfSyntax.v` lines 110–114), so the stored value is the low half. DBWord uses the full register. Failure is `Stuck`.
- LDDW constant. `exec_lddw` (lines 648–652) writes `Int64.ofwords hi lo` and steps PC twice. For any other pseudo type it `cast_i2p`s or `Stuck`s. With the raw src field this is the constant 0, and the `R_BPF_64_64` is not consulted.
- CALL. `exec_instr` (lines 888–904) implements `Pcall` only for `CallInternal`. `CallByStaticID` hits the wildcard `Stuck` (line 904). The relational `step` constructor `exec_step_external` (lines 979–990) is separate: if `ebpf_call_function` returns `Some (res, m')` for `CallByStaticID` or `CallByBTF`, it sets `r0` to `res`, undefines `r1`–`r5` (`undef_caller_save_regs`, lines 662–667), and advances PC by 1. `ebpf_call_function` is an uninterpreted `Variable` (lines 60–61). I found no definition of map lookup. `Validation.v`'s `bpf_interpreter` calls `exec_instr`, so on that interpreter the call is `Stuck` even if the parameter exists.
- EXIT. Live `exec_ret` (lines 819–821): on an empty call stack, `PC := Vnullptr` and `r0` is kept. The earlier `exec_ret` at line 811 is inside the comment that ends at line 817. C++ EXIT is `Return(i64, r0)` (`ebpf_lift.cpp` lines 496–497).
- Initial Rocq state that was read (`initial_lst_state`, lines 993–1000): `r1` is `Vptr ctx 0`, `r10` is `Vptr stk bpf_stack_size`, and `bpf_stack_size` is 512 (line 720). A store at `r10-4` lands at offset 508, inside the `[0, 512)` region the same definition mentions. The C++ lifter does not build that stack. In `LiftInit::Rocq` (`ebpf_lift.cpp` lines 315–321) `r1` and `r10` start as `PoisonValue` with origin `Pointer`, not as a memory object. `LiftInit::Zero` makes them zero unless the caller passes an input.

Not read, so not used as rules: `GlobalSem.v`, `CMemoryModel.v`, `Nondeterminism.v`, `SCLanguage.v`, `ebpfState.v` beyond the imports other files name, `Extraction.v`, and any theorem that this object refines Alive2. I did not read a proof of `step`. `exec_instr_event` (lines 962–966) records `eBPF_vload` / `eBPF_vstore` only; a call event is produced by `exec_step_external`, not by that function. Atomic opcodes do not appear in this image; I did not use `Patomic`.

# IR mapping against the existing C++ lifter only

`lift_ebpf` (`ebpf_lift.cpp` lines 1005–1010) receives only what `decode_ebpf` returned. For this image that call throws on slot 0. No function, no block, no instruction is emitted. Do not treat a hypothetical IR listing as a conversion.

If a prefix consisted only of the ALU and JMP opcodes that this decoder already accepts, the emitter that exists today would do only the following. Memory, LDDW, and CALL have no emitter.

- ALU64 MOV X (slots 2, 9, 16, 23): the destination register becomes the source SSA value. No `BinOp`. `bare_mov` (lines 138–146) is true, so a block-initial mov is noted at block entry rather than as its own instruction.
- ALU64 MOV K (slots 7, 12, 19): destination becomes `IntConst i64` of the sign-extended imm (`14`, `18`, `12`).
- ALU64 ADD K / ADD X (slots 3, 10, 15, 17, 20, 24, 30): `BinOp Add` on i64. Slot 24's constant is i64 `-4`. Slot 30's constant is i64 `1`. Register sources are the current SSA values, including a pointer-origin value if one ever reached them. `pointer_alu` (lines 347–354) only sets `EbSite.pointer_use`. It does not change the arithmetic.
- ALU32 MOV K (slot 32): `trunc` to i32, the i32 constant `1`, `zext` back to i64, stored as `r0`.
- JMP64 JGT X (slots 4, 11, 18): `ICmp UGT` on the full i64 values, then `Branch` to the taken block and the fall-through block.
- JMP32 JEQ K (slot 6): `trunc` both sides to i32, `ICmp EQ` against i32 `0x81`, conditional branch.
- JMP32 JNE K (slots 8, 14): same truncation, `ICmp NE` against i32 `0xa888` or i32 `8`. Symbolic IR has this. The concrete walker does not implement `ICmp::NE`.
- JMP64 JEQ K (slot 28): `ICmp EQ` of i64 `r0` and i64 `0`.
- EXIT (slot 33): `Return` of the i64 in `r0`.
- LDX, STX, LDDW, CALL: no `Load`, `Store`, `Call`, or constant-pool instruction is constructed. The only `MemInstr` mention is in the concrete walker (lines 962–965), which marks `MemorySummary::Changed` and then `Unsupported` if it ever sees one. This lifter never creates one. `make_alive_trace` (lines 981–1000) starts from `decode_ebpf` and therefore also throws before a trace exists.

`r10` is register 10, a normal i64 slot (`std::array<Value *, 11>`). Nothing allocates a 512-byte stack or treats `r10-4` as an address.

# Memory, helper, map, and loop requirements

- Loop: no. Seven forward branches, one exit. A later lifter must not report a loop for this object.
- Memory: required, and absent from the C++ lifter.
  - Two u32 loads from the context (`r1+4`, `r1+0`), zero-extended. These are `__u32` fields, not 64-bit pointers.
  - Two u16 loads (ethertype, VLAN ethertype), zero-extended. Little-endian load of a big-endian header field; the compare constants are already swapped in the immediates.
  - One u8 load at `saddr+3`, zero-extended.
  - One u32 stack spill at `r10-4` and one address computed as `r10+(-4)` for the helper key.
  - One u64 load and one u64 store through the pointer returned in `r0`, only on the non-null path. Not atomic. A model that uses XADD or `map_update` is a different program.
  - Bounds failures jump to the exit block. They must not be `Stuck` and must not skip `w0 = 1`.
- Helper: required. Slot 27 is `call 1` with src field 0 (`CallByStaticID`). Arguments set up by the preceding slots: `r1` is the map (only after the reloc is applied), `r2` points at the spilled u32 key. The BTF string at this call is `bpf_map_lookup_elem(&counter, &key)`. No helper semantics were found beyond the uninterpreted `ebpf_call_function`. After a real BPF call, `r1`–`r5` are undefined; `exec_step_external` does undefine them. The C++ lifter does not.
- Map: required. One `BPF_MAP_TYPE_ARRAY` per the toml, definition bytes above, symbol `counter`. Key 4 bytes, value 8 bytes, 256 entries, flags 0. The only link from the instruction stream to that symbol is `R_BPF_64_64` at slot 25. Lookup failure (`r0 == 0`) skips the increment and still returns 1. An in-range array of 256 and a one-octet key means a created map returns a value for every key this program builds; a missing map or a failed lookup is still a defined drop, not UB.
- Pointer arithmetic: the `>` checks are unsigned 64-bit compares of zero-extended u32 addresses plus a constant. Sign-extending the u32 loads, or using a signed compare, disagrees with `eval_cmp64`'s unsigned compare. See the counterexample.
- CO-RE: five field-offset records. The bytes already hold the local offsets. A loader may patch them. The C++ decoder never sees `.BTF.ext`.

Flags: helper yes, map yes, loop no.

# Proof coverage

Nothing in the files that were read proves this object. `Validation.v` is an interpreter loop over `exec_instr`. On slot 0 that decoder can return `Pload`, so Rocq decoding is ahead of the C++ decoder, but then:

- `exec_load` / `exec_store` are `Stuck` unless the address is a pointer the memory model accepts. There is no theorem here that the XDP bounds checks imply that.
- `find_instr` on slots 25–26 yields the constant 0, not map `counter`.
- `bpf_interpreter` uses `exec_instr`, which is `Stuck` on `Pcall CallByStaticID`. The relational rule can step the call only by assuming `ebpf_call_function`. That assumption does not say what lookup returns, and it does not describe the later `*r0 += 1`.
- The C++ concrete walker cannot evaluate `ICmp::NE` (slots 8 and 14) and cannot evaluate any memory op.
- `ebpf_exhibit.cpp` states that the supported equivalence scope excludes memory, maps, helpers, and pointer arithmetic. This program is entirely outside that scope.
- I did not read a lemma connecting `step` to Alive2 IR.

# Counterexample

Do not encode the LDDW as the constant 0 and call that the program. Bytes at slots 25–26 are imm 0 with src 0, which is what both decoders read. `.relxdp1` at file offset `0xc8` names `counter`. Take an initial array element 0 for the key this program builds, and a packet that passes the IPv4 checks (for example `data = 0`, `data_end = 64`, ethertype bytes `08 00` at offset 12, and a 20-byte IPv4 header whose `saddr` last octet is 0). With the relocation applied, helper 1 returns the value pointer and slots 29–31 store 1. With the raw immediate, `r1` is 0 and there is no such store. Those two runs are not equivalent. Ignoring `.relxdp1`, or treating this as an XPOST reloc or a map-index LDDW (src 5), is the same mistake.

A second, independent bug, if a later lifter sign-extends the u32 `data` / `data_end` loads or compares them with a signed `ICmp`: let `data = 0xfffffff0` and `data_end = 0x10`. Zero-extended, `r3 = 0xfffffffe` and unsigned `r3 > r2` is true, so slot 4 jumps to slot 32, `r0 = 1`, and the helper is not called. Sign-extending those loads makes `r1 = -16` and `r3 = -2`. A signed compare of `-2 > 0x10` is false, so execution falls into the packet load. The branch differs before any byte of the packet is read. The existing `Jgt` mapping is unsigned (`ICmp::UGT`, `eval_cmp64` `GT Unsigned`); the bug is sign-extending the LDX.W, which neither `load_value_casting` nor a faithful ALU32 zero-extend does.

# Concrete gaps

1. `decode_ebpf` throws on slot 0 (`unsupported class in opcode 0x61`). The same reject hits every LDX, both STX, the LDDW, and the CALL. `lift_ebpf` does not run.
2. No C++ IR exists for packet loads, the stack spill, the map-value load/store, LDDW, or `call 1`. `EbInsn` cannot represent them.
3. Neither decoder applies `R_BPF_64_64`. Rocq turns slots 25–26 into `PSEUDO_Constant 0`. The map symbol is only in `.relxdp1` and the `maps` section.
4. `exec_instr` is `Stuck` on this call. `ebpf_call_function` is an assumption, not a map-lookup definition. `bpf_interpreter` never reaches the increment.
5. The concrete C++ walker has no `ICmp::NE`, so the two VLAN/IPv4 `JNE`s would not evaluate even after a decode front-end.
6. CO-RE offsets are in `.BTF.ext` only. The lifter does not read them.

ISSUES
