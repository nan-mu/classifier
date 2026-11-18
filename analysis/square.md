# square — observation report

Conversion result: **NOT CONVERTED**. No `.alive` file is emitted. This note classifies the ELF against the decoder and lifter that already exist. It does not invent an ISA, a memory IR, or a success path.

STATUS: ISSUES

## Evidence

Commands actually run:

- `shasum -a 256 /Volumes/SSD/bs/build/square/bpf.o` → `d99e28628825f172ea6815a58b0bb5e77567b1468a49f0997686ada5123a90d1` (matches the requested digest). File size 8328, same as `bpf.toml` `size`.
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -h -S -s -r -l -W` on that ELF.
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r -l --section=xdp` and `-s` for `xdp`, `.text`, `license`, `.maps`, `.BTF`, `.BTF.ext`.
- A local struct-unpack of the `xdp` bytes (little-endian `opcode:u8, regs:u8, off:i16, imm:i32`). It matches llvm-objdump slot for slot. No compiler was run.

ELF identity: ELF64, `ELFDATA2LSB`, `ET_REL`, `EM_BPF`, entry point 0, no program headers. Section-header string table is section 1. Endianness of the file and of every instruction field below is little-endian. There is no `END` / byte-swap opcode in the program; the explicit byte loads and stores are the endian conversion.

## Executable sections

| Index | Name | Flags | File offset | Size | Role |
| --- | --- | --- | --- | --- | --- |
| 2 | `.text` | AX (`0x6`) | `0x40` | **0** | empty. Not the program. Shares the file offset with `xdp` only because its size is zero. |
| 3 | `xdp` | AX (`0x6`) | `0x40` | **240** | the only nonzero executable section |

No other section has `SHF_EXECINSTR`. `license` and `.maps` are `WA`, not executable.

## Entries

One function.

- Symbol 11: `square`, `FUNC`, `GLOBAL`, section index 3 (`xdp`), value 0, size 240.
- llvm-objdump entry label: `0000000000000000 <square>`.
- Source named by `bpf.toml`: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/square.c` function `square` (`SEC("xdp")`). That C file was read. The compiled body does not call helpers and does not touch the map.

`240 / 8 = 30` slots. No slot has opcode `0x18`, so there is no LDDW pair and no second-slot immediate. Instruction count is 30, not 15. Jump displacements below are in slots, not bytes.

## Instruction list

`dst` is the low nibble of byte 1, `src` the high nibble. `off` is the signed 16-bit field. `imm` is the signed 32-bit field. Class is `opcode & 7` as in `alive2/src/ebpf_decode.cpp` (`kAlu=0x04`, `kJmp=0x05`, `kJmp32=0x06`, `kAlu64=0x07`) and `alive2/rocq/upstream/theories/ebpfDecoder.v` `BPF_CLASS`.

| pc | section off | raw (8 bytes) | asm (llvm-objdump) | class | C++ `decode_ebpf` | Rocq `decode_insn` (read) |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | `0x00` | `b4000000 00000000` | `w0 = 0x0` | ALU32 `0x04` MOV K | `EbAlu` W32 Mov Imm r0, 0 | `Palu MOV W32 R0 (inr 0)` |
| 1 | `0x08` | `61120400 00000000` | `w2 = *(u32 *)(r1 + 0x4)` | LDX `0x01` MEM W | **reject** unsupported class `0x61` | `Pload Word R2 R1 +4` |
| 2 | `0x10` | `61110000 00000000` | `w1 = *(u32 *)(r1 + 0x0)` | LDX MEM W | **reject** class `0x61` | `Pload Word R1 R1 +0` |
| 3 | `0x18` | `bf130000 00000000` | `r3 = r1` | ALU64 MOV X | `EbAlu` W64 Mov Reg r3, r1 | `Palu MOV W64 R3 (inl R1)` |
| 4 | `0x20` | `07030000 08000000` | `r3 += 0x8` | ALU64 ADD K | `EbAlu` W64 Add Imm r3, 8 | `Palu ADD W64 R3 (inr 8)` |
| 5 | `0x28` | `2d231700 00000000` | `if r3 > r2 goto +0x17 <L0>` | JMP JGT X | `EbJmp` W64 Jgt Reg r3, r2, off 23 | `Pjmpcmp (GT Unsigned) W64 R3 (inl R2) +23` |
| 6 | `0x30` | `1c320000 00000000` | `w2 -= w3` | ALU32 SUB X | `EbAlu` W32 Sub Reg r2, r3 | `Palu SUB W32 R2 (inl R3)` |
| 7 | `0x38` | `a6021500 04000000` | `if w2 < 0x4 goto +0x15 <L0>` | JMP32 JLT K | `EbJmp` W32 Jlt Imm r2, 4, off 21 | `Pjmpcmp (LT Unsigned) W32 R2 (inr 4) +21` |
| 8 | `0x40` | `71120900 00000000` | `w2 = *(u8 *)(r1 + 0x9)` | LDX MEM B | **reject** class `0x71` | `Pload Byte R2 R1 +9` |
| 9 | `0x48` | `64020000 08000000` | `w2 <<= 0x8` | ALU32 LSH K | `EbAlu` W32 Lsh Imm r2, 8 | `Palu LSH W32 R2 (inr 8)` |
| 10 | `0x50` | `71130800 00000000` | `w3 = *(u8 *)(r1 + 0x8)` | LDX MEM B | **reject** | `Pload Byte R3 R1 +8` |
| 11 | `0x58` | `4c320000 00000000` | `w2 \|= w3` | ALU32 OR X | `EbAlu` W32 Or Reg r2, r3 | `Palu OR W32 R2 (inl R3)` |
| 12 | `0x60` | `71130a00 00000000` | `w3 = *(u8 *)(r1 + 0xa)` | LDX MEM B | **reject** | `Pload Byte R3 R1 +10` |
| 13 | `0x68` | `64030000 10000000` | `w3 <<= 0x10` | ALU32 LSH K | `EbAlu` W32 Lsh Imm r3, 16 | `Palu LSH W32 R3 (inr 16)` |
| 14 | `0x70` | `4c320000 00000000` | `w2 \|= w3` | ALU32 OR X | `EbAlu` W32 Or Reg | `Palu OR W32` |
| 15 | `0x78` | `71130b00 00000000` | `w3 = *(u8 *)(r1 + 0xb)` | LDX MEM B | **reject** | `Pload Byte R3 R1 +11` |
| 16 | `0x80` | `64030000 18000000` | `w3 <<= 0x18` | ALU32 LSH K | `EbAlu` W32 Lsh Imm r3, 24 | `Palu LSH W32 R3 (inr 24)` |
| 17 | `0x88` | `4c320000 00000000` | `w2 \|= w3` | ALU32 OR X | `EbAlu` W32 Or Reg | `Palu OR W32` |
| 18 | `0x90` | `2c220000 00000000` | `w2 *= w2` | ALU32 MUL X | `EbAlu` W32 Mul Reg r2, r2 | `Palu MUL W32 R2 (inl R2)` |
| 19 | `0x98` | `bc230000 00000000` | `w3 = w2` | ALU32 MOV X | `EbAlu` W32 Mov Reg r3, r2 | `Palu MOV W32 R3 (inl R2)` |
| 20 | `0xa0` | `74030000 18000000` | `w3 >>= 0x18` | ALU32 RSH K | `EbAlu` W32 Rsh Imm r3, 24 | `Palu RSH W32 R3 (inr 24)` |
| 21 | `0xa8` | `73310b00 00000000` | `*(u8 *)(r1 + 0xb) = w3` | STX MEM B | **reject** class `0x73` | `Pstore Byte R1 (inl R3) +11` |
| 22 | `0xb0` | `bc230000 00000000` | `w3 = w2` | ALU32 MOV X | `EbAlu` W32 Mov Reg | `Palu MOV W32` |
| 23 | `0xb8` | `74030000 10000000` | `w3 >>= 0x10` | ALU32 RSH K | `EbAlu` W32 Rsh Imm r3, 16 | `Palu RSH W32` |
| 24 | `0xc0` | `73310a00 00000000` | `*(u8 *)(r1 + 0xa) = w3` | STX MEM B | **reject** | `Pstore Byte R1 (inl R3) +10` |
| 25 | `0xc8` | `73210800 00000000` | `*(u8 *)(r1 + 0x8) = w2` | STX MEM B | **reject** | `Pstore Byte R1 (inl R2) +8` |
| 26 | `0xd0` | `74020000 08000000` | `w2 >>= 0x8` | ALU32 RSH K | `EbAlu` W32 Rsh Imm r2, 8 | `Palu RSH W32 R2 (inr 8)` |
| 27 | `0xd8` | `73210900 00000000` | `*(u8 *)(r1 + 0x9) = w2` | STX MEM B | **reject** | `Pstore Byte R1 (inl R2) +9` |
| 28 | `0xe0` | `b4000000 02000000` | `w0 = 0x2` | ALU32 MOV K | `EbAlu` W32 Mov Imm r0, 2 | `Palu MOV W32 R0 (inr 2)` |
| 29 | `0xe8` | `95000000 00000000` | `exit` | JMP EXIT | `EbJmp` Exit | `Pret` |

`decode_ebpf` stops at pc 1. The later “would decode” rows are what the same function does on that opcode in isolation (`ebpf_decode.cpp` lines 55–168). They are not a successful decode of this object.

### Jump slots

Only two instructions have a nonzero `off`. Both are forward. `jump_target` (`ebpf_decode.cpp` lines 26–31) is `index + 1 + off` because `ja_uses_imm` is false for these.

- pc 5: `off = +23`, target pc `29` (`<L0>` / `exit`). Fall-through is pc 6. Not a back edge (`target <= i` is the loop test in `ebpf_lift.cpp` `build_blocks`).
- pc 7: `off = +21`, target pc `29`. Fall-through is pc 8.

No other `off` is nonzero, so no ALU offset is hiding a jump. CFG if the memory ops were ordinary non-terminators (this is not built, because decode throws first):

- block pc 0–5, conditional edge to pc 29 or pc 6
- block pc 6–7, conditional edge to pc 29 or pc 8
- block pc 8–28, fall-through to pc 29
- block pc 29, exit

`LiftInfo.loop` would be false. There is no `JA`.

### What the body does (from the bytes, matched to `square.c`)

pc 0 sets `r0 = 0` (`XDP_ABORTED` in the C return on the failure paths). pc 1 zero-extends `*(u32 *)(r1+4)`, which the CO-RE note names `xdp_md.data_end`, into `r2`. pc 2 zero-extends `*(u32 *)(r1+0)` (`xdp_md.data`) into **`r1`, destroying the context pointer**. pc 3–5 are `data+8 > data_end` as a 64-bit unsigned compare; taken means exit with `r0` still 0. pc 6 is the 32-bit subtract `data_end - (data+8)`. pc 7 exits with `r0 = 0` when that difference is `< 4`. pc 8–17 assemble a little-endian `u32` from bytes `r1+8` through `r1+11`. pc 18 is a 32-bit square (`w2 *= w2`). pc 19–27 store that `u32` back little-endian, byte order p[3], p[2], p[0], p[1]. pc 28 sets `r0 = 2` (`XDP_PASS`). pc 29 exits.

Both packet pointers are 32-bit loads, so later ALU64 arithmetic is on zero-extended integers, not on the original `xdp_md *`.

## Relocations, maps, BTF, CO-RE

`llvm-readelf -r` has **no** `.rel.xdp` and **no** `.rel.text`. Nothing in the instruction stream is an ELF relocation.

CO-RE is not an ELF relocation and not an XPOST. `.BTF.ext` header (`magic 0xeb9f`, version 1, `hdr_len 0x20`) has `core_relo_off 0x1c0`, `core_relo_len 0x2c`. That subsection is `rec_size 16`, one info sec, `num_info 2`. Records, also printed by `llvm-objdump -r` as `CO-RE <byte_off>` and copied in `bpf.toml` `[CORE]`:

| insn byte off | type id | access string | kind | meaning |
| --- | --- | --- | --- | --- |
| `0x8` (pc 1) | 17 | `0:1` at BTF string `0x12d` | 0 | `BPF_CORE_FIELD_BYTE_OFFSET` of `xdp_md::data_end` |
| `0x10` (pc 2) | 17 | `0:0` at BTF string `0x15b` | 0 | same kind, `xdp_md::data` |

Kind 0 rewrites the **16-bit offset field** of those two LDX slots. The raw offsets already in the object are `4` and `0`. The immediates are `0`. A loader that skips CO-RE keeps those raw offsets; that is not the same thing as “there is no relocation.”

Other relocations, none of which are instruction operands:

- `.rel.BTF`: `R_BPF_64_NODYLD32` at `0x250` → symbol `workload`; at `0x268` → symbol `LICENSE`. These are BTF datasec variable fixups, not map-index immediates and not `PSEUDO_MAP_*` LDDW.
- `.rel.debug_addr`: `R_BPF_64_ABS64` to section symbol `xdp` (four times), to `LICENSE`, and to `workload`. Debug addresses, not code.
- `.rel.debug_info`, `.rel.debug_str_offsets`, `.rel.debug_frame`, `.rel.debug_line`, `.rel.BTF.ext`: debug / BTF-ext section-name and line records. `.rel.BTF.ext` points at section symbol `xdp` (the CO-RE and line records name their section). Not an instruction patch by itself.

Map symbol: 13 `workload`, `OBJECT`, `GLOBAL`, section 5 `.maps`, value 0, size 32. Section contents are 32 zero bytes. `bpf.toml` says `BPF_MAP_TYPE_HASH`, `max_entries 2`, `key_size 1`, `value_size 32`, `aot_addr 0x40380270`. That `aot_addr` is a build note. Every ELF section address is 0 (`ET_REL`); it is not a pointer immediate in `xdp`.

No instruction uses src-immediates 1–6 of an LDDW (`ebpfSyntax.v` `pseudo_ptr_ty`: `PSEUDO_MAP_FD`, `PSEUDO_MAP_IDX`, `PSEUDO_MAP_VALUE`, `PSEUDO_MAP_IDX_VALUE`). There is no map-index reference in the code. The map is a side table for the test harness. The C comment says the app copies map key 0 into the context and copies the context back to key 1; `square` itself only computes on `ctx`.

License section: bytes `47 50 4c 00` (`GPL`), symbol `LICENSE` size 4.

BTF strings that were read off `.BTF` include `xdp_md`, `data`, `data_end`, `data_meta`, `ingress_ifindex`, `rx_queue_index`, `egress_ifindex`, `workload`, `w0`–`w7`, and the `square.c` source lines. `.BTF` also has the two `R_BPF_64_NODYLD32` symbol references above. I did not walk every BTF type record by hand past the string table and the two core-relo records; llvm-objdump already names type 17 as `struct xdp_md`.

## Semantic rules actually read

Read and used:

- `alive2/src/ebpf_decode.cpp` entire file. Class filter is only ALU, ALU64, JMP, JMP32. Anything else, including LDX `0x01` and STX `0x03`, throws `unsupported class in opcode` (lines 164–167). ALU32 mov/sub/mul/or/lsh/rsh with `off == 0` are accepted (lines 96–108). JMP `JGT` is code `0x20` (line 149). JMP32 `JLT` is code `0xa0` (line 151). EXIT requires class JMP, no source bit, `dst=src=off=0` (lines 130–133).
- `alive2/src/ebpf_lift.cpp`: `build_blocks`, `init_regs` (`LiftInit::Zero` versus `Rocq`, where r1 and r10 start as `PoisonValue` / `RegOrigin::Pointer`), `pointer_alu` / `pointer_jmp`, `emit` / `emit_alu` / `emit_wide` / `emit_narrow` / `shift` / `emit_cmp` / `arith_op` / `shift_op` / `icmp_cond`. Not read in full: the concrete `Trace` walker from the `emit_step` lambda downward (about line 768 on).
- `alive2/src/ebpf.h`: `EbAlu`, `EbJmp`, `EbInsn` variants. The lifter only receives that variant. There is no load or store alternative.
- `alive2/src/ebpf_project.cpp`: `supported_insn` (lines 238–249), `eval_alu` (Mov/Add/Sub/Div only), `jgt_cond` (unsigned greater only), the `finish` path that calls `decode_ebpf` and stores `ill-formed` on a throw (lines 852–864), and the blocked-pc rule `unsupported || pointer_use` (lines 922–927).
- `alive2/src/ebpf_gate.cpp`: `op_kind` / `effects` for the ALU/JMP subset only. The gate never sees this object, because decode throws first. I did not read the rest of the gate’s worklist.
- `alive2/rocq/upstream/theories/ebpfSyntax.v` through the `instruction` inductive (line 245): `Pload`, `Pstore`, `Palu`, `Pjmpcmp`, `Pret`, `Plddw` / `pseudo_ptr_ty`. I did not read the rest of that file.
- `alive2/rocq/upstream/theories/ebpfDecoder.v`: `decode_insn`, `decode_lddw_insn`, `find_instr`. Mode `op >> 5 == 3` is MEM (`0x60`). Size `(op >> 3) & 3`: 0 Word, 2 Byte. LDX with `imm == 0` is `Pload`. STX with `imm == 0` is `Pstore` of a register. LDDW is only opcode `0x18` and consumes the next slot; this object has none.
- `alive2/rocq/upstream/theories/ebpfBinSem.v`: `eval_alu32` / `eval_alu64` / `exec_alu` (ALU32 result is `Val.longofintu`, so the high half is zero), `eval_shift_mask` (W32 mask 31, W64 mask 63; the comment quotes the kernel verifier’s immediate-range check), `eval_cmp32` / `eval_cmp64` / `exec_jmpcmp` / `eval_cmp_static`, `load` / `exec_load` / `store` / `exec_store`, `exec_instr`, and the live `exec_ret` (lines 819–839, empty call stack sets PC to `Vnullptr` and keeps `R0`). I did not read call, tail-call, or atomic bodies. I did not read `ebpfState.v`. I did not read CompCert’s `Val.offset_ptr` definition; it is not in this tree.

Not read, so not used as a rule: `ir/memory.cpp`, `ir/instr.cpp` (only the comment at `emit_divmod` citing `sdiv` UB at `instr.cpp:213`), Linux `verifier.c` except the quotation inside `ebpfBinSem.v`, and any helper ABI.

Rocq memory rules that matter here, and the gap inside them:

- `exec_load` (`ebpfBinSem.v` 575–589): a `Vptr` base uses `Val.offset_ptr`; a `Vlong` base is `cast_i2p` through `addr_map`; any other base, or a failed load, is `Stuck`. `load_value_casting` zero-extends a `Vint` to `Vlong`. A Word load of `data` therefore yields a scalar, not a `Vptr`.
- `exec_store` (633–646) always stores through `Val.offset_ptr rs#r o`. It does **not** call `cast_i2p`. After pc 2, `r1` is that scalar. I cannot claim the Rocq store succeeds on this program. I also cannot claim CompCert `offset_ptr` of a `Vlong` is `Vundef`, because I did not read that definition. The concrete gap is: the store rule, as written, has no scalar-address path, and this program’s stores use the scalar produced by the `u32` load.
- `eval_alu32` MUL is `Val.longofintu (Val.mul (loword dst) (loword src))`. The square is the low 32 bits, then zero-extended. Shifts are masked. JMP32 `LT Unsigned` is `Val.cmpu_bool ... Clt` on the low halves (`eval_cmp32`).

## IR mapping against the existing C++ lifter only

The lifter never runs on this object. `decode_ebpf` throws at pc 1, and `ebpf_project.cpp` records gate `ill-formed` with that exception text. There is no `IR::Function` for `square`.

For the slots whose opcode the decoder does accept, the mapping below is what `emit_alu` / `emit_cmp` / `emit` do with `LiftBug::None`. Memory slots have no mapping. `pointer_alu` does not change the IR; it only sets `EbSite.pointer_use`. A pointer still becomes an `i64` `BinOp` or `ICmp`.

| pcs | decoded op | IR `emit_*` actually implements |
| --- | --- | --- |
| 0, 28 | ALU32 MOV imm | `imm64` **without** sign-extend (sign-extend is W64 only), `trunc` to `i32`, MOV is the truncated immediate, then `zext` to `i64`. `w0 = 0` and `w0 = 2` clear the high half. |
| 3 | ALU64 MOV reg | `bare_mov`: the destination value pointer **is** the source. No trunc. Copies whatever origin `r1` has. |
| 4 | ALU64 ADD imm | `i64 BinOp::Add` of `r3` and `i64 8` (sign-extended immediate, positive here). |
| 5 | JMP64 JGT reg | `ICmp UGT` on the full `i64` values, `Branch` to the target block then the fall-through block. |
| 6 | ALU32 SUB reg | `trunc` both operands to `i32`, `BinOp::Sub`, `zext` to `i64`. |
| 7 | JMP32 JLT imm | `trunc` `r2` to `i32`, `ICmp ULT` against `i32 4` (`c32` of the unsigned immediate), then the same taken/fall branch shape. |
| 9, 13, 16 | ALU32 LSH imm | `trunc` to `i32`, shift amount `And` with `i32 31`, `BinOp::Shl`, `zext`. Amounts 8, 16, 24 are unchanged by the mask. |
| 11, 14, 17 | ALU32 OR reg | `trunc`, `BinOp::Or`, `zext`. |
| 18 | ALU32 MUL reg | `trunc`, `BinOp::Mul`, `zext`. Same-register source is still a multiply; the lifter does not special-case it. (`exec_alu` only special-cases same-register SUB and XOR.) |
| 19, 22 | ALU32 MOV reg | `trunc` the source to `i32`, then `zext`. High half cleared. |
| 20, 23, 26 | ALU32 RSH imm | `trunc`, amount `And 31`, `BinOp::LShr` (logical, not `AShr`), `zext`. |
| 29 | EXIT | `Return(i64, r0)`. |
| 1, 2, 8, 10, 12, 15, 21, 24, 25, 27 | LDX / STX | no variant, no `IR::Load`, no `IR::Store`. `EbTypes` declares `i8` only for MOVSX. |

`LiftInit::Rocq` would mark an untouched `r1` as pointer poison. That origin is wrong for every use after pc 2, because pc 2 replaces `r1` with a zero-extended `u32`. The lifter cannot see that replacement.

## Memory, helper, map, loop

- Memory: required. Two `u32` context loads (pc 1, 2), four `u8` packet loads (pc 8, 10, 12, 15), four `u8` packet stores (pc 21, 24, 25, 27). Addresses are `r1 + {0,4}` while `r1` is still the context, then `r1 + {8,9,10,11}` after `r1` has been replaced by the `data` integer. The bounds checks are the two jumps, not a helper. A correct model has to keep the packet bytes and the failure path that does not store.
- Helper: **no**. No `call` opcode `0x85`, no src `0/1/2` call, no tail call.
- Map: **present in the ELF, not referenced by any instruction**. No LDDW, no map fd, no map index, no `bpf_map_*` helper. `.maps` / `workload` / BTF `R_BPF_64_NODYLD32` / `bpf.toml` `aot_addr` are metadata. Do not invent a map load in the IR.
- Loop: **no**. Both edges go to pc 29, which is after the branch. The lifter’s back-edge test would not fire.

## Proof coverage

None for this object.

`finish` in `ebpf_project.cpp` calls `decode_ebpf` before the gate and before `project`. The throw at pc 1 becomes gate `ill-formed`. `scope_of` returns `unsupported` when the gate is not `ready`. No SMT query is built. That is a decode failure, not a proof of equivalence, and it must not be reported as success.

Even the ALU/JMP subset is outside the projection that `supported_insn` actually checks:

- In scope, and only if they were reached: ALU64 MOV (pc 3), ALU64 ADD (pc 4), JMP64 JGT (pc 5), EXIT (pc 29).
- Out of scope (`width != W64`, or the op is not Mov/Add/Sub/Div, or the jump is not JGT/JA/EXIT): every ALU32 instruction, including the square and the shifts, and the JMP32 `JLT` at pc 7. `eval_alu` has no Mul, Or, Lsh, or Rsh case. `jgt_cond` is not a JLT rule.
- Loads and stores are outside `EbInsn`, so they are outside `supported_insn` as well. Rocq has `exec_load` / `exec_store` / `exec_instr` arms, but the C++ projection never calls them. I did not read a lemma that those Rocq rules match this XDP program.
- Pointer block: if pc 1–2 are ignored and `r1` stays a pointer, pc 3 copies it, pc 4 is `pointer_use`, and pc 5 compares a pointer. `ebpf_project.cpp` marks that `Unsupported` with reason `bitvector use of a pointer register`. That block is an artifact of dropping the loads. It is not a proof about the real pc 5, whose operands are zero-extended `u32`s.

I did not read a completed proof, a `.alive` witness, or an exhibit fixture for `square`.

## Counterexample idea

Do not treat a skipped check as the same program.

Packet: `data = 0x1000`, `data_end = 0x100A` (10 bytes). Then:

- pc 1–2: `r2 = 0x100A`, `r1 = 0x1000` (context pointer gone).
- pc 4–5: `r3 = 0x1008`, `0x1008 > 0x100A` is false, so the first branch falls through.
- pc 6–7: `w2 = 0x100A - 0x1008 = 2`, `2 < 4` is true, branch to pc 29.
- Result: `r0 = 0`, and bytes at `data+8` and `data+9` are not read for a square and not written. Offsets `+10` and `+11` are past `data_end`.

A converter that keeps only `data+8 <= data_end` and then always executes pc 8–27 reads and writes two bytes past `data_end`. That is a counterexample to dropping pc 7. The distinguishing observation is the exit value `0` and the absence of stores, against any store or any `r0 = 2`.

A second input distinguishes “`r1` is still the context pointer”: `data = 0x1000`, `data_end = 0x1010`, context pointer `0x2000`, payload `u32` at `data+8` equal to `2`. The real program does not take pc 5, computes `2 * 2 = 4`, stores bytes `04 00 00 00`, returns `2`. A model that skips pc 2 compares `0x2008 > 0x1010`, takes the abort edge, returns `0`, and writes nothing.

CO-RE is a third, separate hole: kind 0 on pc 1 and pc 2 asks a loader to replace offsets `4` and `0` from target BTF. Leaving the raw offsets in place is not a model of that relocation. I am not claiming a specific kernel where `data_end` is not at byte 4; the record is the evidence that the offset is relocatable.

A 64-bit square is not a counterexample by itself. pc 18 is ALU32, and the later stores only write the low 8 bits of ALU32 shifts, so the low 32 bits of a 64-bit product match. The observable bugs are the bounds checks, the overwrite of `r1`, and the stores through the scalar data pointer.

## Gaps (why this is ISSUES, not PASS)

1. `decode_ebpf` rejects ten memory instructions (pc 1, 2, 8, 10, 12, 15, 21, 24, 25, 27). The existing lifter has no load/store IR. Conversion cannot start.
2. `exec_store` has no `cast_i2p` path, while every store in this program uses `r1` after a zero-extending `u32` load. Copying the Rocq load rule and assuming the store rule works is not justified by the text that was read.
3. The C++ projection’s proved opcode set does not include ALU32, MUL, OR, LSH, RSH, or JMP32 JLT, which are most of the arithmetic.
4. Two `BPF_CORE_FIELD_BYTE_OFFSET` records sit on the context loads. They are not ELF relocations and not map-index immediates. Ignoring them changes which `xdp_md` field is read.

STATUS: ISSUES
