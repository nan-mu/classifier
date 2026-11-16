# Observation: xdp_drop

Conversion result: **NOT CONVERTED**. No `.alive` file is emitted. This note classifies the object that is on disk. It does not define a new ISA and does not treat the Lean eBPF AST and the C++ lifter as one encoding.

## Evidence

- SHA-256 of `/Volumes/SSD/bs/build/xdp_drop/bpf.o`, computed with `shasum -a 256`: `1197f07a580c3cd1b971e0de6ff2edfabcc1af78830b7f198d8d4dee09b76184`. Matches the digest given for this task.
- `file`: ELF 64-bit LSB relocatable, eBPF, version 1 (SYSV), with debug_info, not stripped.
- `llvm-readelf -h` (`/opt/homebrew/opt/llvm/bin/llvm-readelf`, which is `llvm-readobj`): ELF64, data 2's complement little endian (`EI_DATA` = 1), type `REL`, machine `EM_BPF`, entry point `0`, no program headers, 27 section headers, flags `0`.
- Disassembly and section bytes: `llvm-objdump -d --section=xdp --section=.text` and `llvm-objdump -s` / `llvm-readelf -x` on `xdp`, `.maps`, and `license`. Same LLVM prefix.
- Notes file `/Volumes/SSD/bs/build/xdp_drop/bpf.toml` agrees with the disassembly below (176-byte `xdp` image, one map). It is not the disassembly source of record.
- C source named by that note and by `.debug_str`: `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/xdp_drop.c`.
- BTF and `.BTF.ext` were parsed from the section bytes (magic `0xeb9f`, version 1). Strings and the disassembly were checked against that parse.

## Executable sections

| Nr | Name | Type | Off | Size | Flags | Role |
|---|---|---|---|---|---|---|
| 2 | `.text` | PROGBITS | `0x40` | **0** | `AX` (`SHF_ALLOC|SHF_EXECINSTR`) | empty. Not the program. Shares file offset `0x40` with `xdp` only because its size is 0. |
| 3 | `xdp` | PROGBITS | `0x40` | `0xb0` (176) | `AX` | the only executable bytes. |

No other section has the execute flag. There is no `PT_LOAD` and no ELF entry. The program entry is the symbol, not `e_entry`.

## Entry

- Symbol `xdp_firewall`, `FUNC`, `GLOBAL`, section index 3 (`xdp`), value `0`, size `176`.
- `.BTF.ext` func_info, record size 8, one record: section name `xdp`, `insn_off = 0`, `type_id = 15`.
- BTF type 15 is `FUNC xdp_firewall` → type 14, a `FUNC_PROTO` whose only parameter is type 12, a pointer to type 13 `struct xdp_md`.
- One function. No subprograms, no static calls, no tail calls.

176 bytes is 22 raw 8-byte slots, indices 0..21. Slot 14 is `LDDW` and slot 15 is its continuation, so there are 21 logical instructions. Jump offsets below are in raw slots, continuation included.

## Real disassembly

`llvm-objdump -d --section=xdp` (bytes confirmed with `llvm-readelf -x xdp`):

```
0000000000000000 <xdp_firewall>:
       0:	b4 00 00 00 00 00 00 00	w0 = 0x0
       1:	61 13 04 00 00 00 00 00	w3 = *(u32 *)(r1 + 0x4)
       2:	61 11 00 00 00 00 00 00	w1 = *(u32 *)(r1 + 0x0)
       3:	bf 12 00 00 00 00 00 00	r2 = r1
       4:	07 02 00 00 0e 00 00 00	r2 += 0xe
       5:	2d 32 0f 00 00 00 00 00	if r2 > r3 goto +0xf <L0>
       6:	b4 00 00 00 02 00 00 00	w0 = 0x2
       7:	69 14 0c 00 00 00 00 00	w4 = *(u16 *)(r1 + 0xc)
       8:	56 04 0c 00 08 00 00 00	if w4 != 0x8 goto +0xc <L0>
       9:	07 01 00 00 22 00 00 00	r1 += 0x22
      10:	b4 00 00 00 00 00 00 00	w0 = 0x0
      11:	2d 31 09 00 00 00 00 00	if r1 > r3 goto +0x9 <L0>
      12:	b7 01 00 00 0c 00 00 00	r1 = 0xc
      13:	0f 12 00 00 00 00 00 00	r2 += r1
      14:	18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00	r1 = 0x0 ll
      16:	85 00 00 00 01 00 00 00	call 0x1
      17:	bf 01 00 00 00 00 00 00	r1 = r0
      18:	b4 00 00 00 02 00 00 00	w0 = 0x2
      19:	15 01 01 00 00 00 00 00	if r1 == 0x0 goto +0x1 <L0>
      20:	b4 00 00 00 01 00 00 00	w0 = 0x1
<L0>:
      21:	95 00 00 00 00 00 00 00	exit
```

`.text` contributes no instructions.

## Instruction list

Fields are little endian, as in the ELF header. `off` and `imm` are the raw fields. Jump target = slot + 1 + off (`alive2/src/ebpf_decode.cpp` `jump_target`, lines 26–31). All four offsets are positive. None target slot 15.

| Slot | Bytes | Class from opcode low 3 bits | Fields | Jump |
|---|---|---|---|---|
| 0 | `b4 00 00 00 00 00 00 00` | ALU32 (`0x4`) | MOV imm, dst r0, src field 0, off 0, imm 0 | fall through |
| 1 | `61 13 04 00 00 00 00 00` | LDX (`0x1`) | mode/size `0x60`, dst r3, src r1, off +4, imm 0 | fall through |
| 2 | `61 11 00 00 00 00 00 00` | LDX | dst r1, src r1, off 0, imm 0 | fall through |
| 3 | `bf 12 00 00 00 00 00 00` | ALU64 (`0x7`) | MOV reg, dst r2, src r1, off 0 | fall through |
| 4 | `07 02 00 00 0e 00 00 00` | ALU64 | ADD imm, dst r2, imm 14, src field 0 | fall through |
| 5 | `2d 32 0f 00 00 00 00 00` | JMP (`0x5`) | JGT reg, dst r2, src r3, off +15, imm 0 | taken → 21, else 6 |
| 6 | `b4 00 00 00 02 00 00 00` | ALU32 | MOV imm, dst r0, imm 2 | fall through |
| 7 | `69 14 0c 00 00 00 00 00` | LDX | size half (`0x08` in the opcode), dst r4, src r1, off +12, imm 0 | fall through |
| 8 | `56 04 0c 00 08 00 00 00` | JMP32 (`0x6`) | JNE imm, dst r4, imm 8, off +12, src field 0 | taken → 21, else 9 |
| 9 | `07 01 00 00 22 00 00 00` | ALU64 | ADD imm, dst r1, imm `0x22` | fall through |
| 10 | `b4 00 00 00 00 00 00 00` | ALU32 | MOV imm, dst r0, imm 0 | fall through |
| 11 | `2d 31 09 00 00 00 00 00` | JMP | JGT reg, dst r1, src r3, off +9 | taken → 21, else 12 |
| 12 | `b7 01 00 00 0c 00 00 00` | ALU64 | MOV imm, dst r1, imm 12, src field 0 | fall through |
| 13 | `0f 12 00 00 00 00 00 00` | ALU64 | ADD reg, dst r2, src r1 | fall through |
| 14 | `18 01 00 00 00 00 00 00` | LD (`0x0`), opcode `0x18` | dst r1, src field **0**, off 0, imm 0 | wide; next slot is not a separate op |
| 15 | `00 00 00 00 00 00 00 00` | continuation | low 32 bits 0, high imm 0 | not a target |
| 16 | `85 00 00 00 01 00 00 00` | JMP | opcode `0x85`, dst 0, src field 0, off 0, imm **1** | fall through to 17 |
| 17 | `bf 01 00 00 00 00 00 00` | ALU64 | MOV reg, dst r1, src r0 | fall through |
| 18 | `b4 00 00 00 02 00 00 00` | ALU32 | MOV imm, dst r0, imm 2 | fall through |
| 19 | `15 01 01 00 00 00 00 00` | JMP | JEQ imm, dst r1, imm 0, off +1, src field 0 | taken → 21, else 20 |
| 20 | `b4 00 00 00 01 00 00 00` | ALU32 | MOV imm, dst r0, imm 1 | fall through |
| 21 | `95 00 00 00 00 00 00 00` | JMP | EXIT, all other fields 0 | halt |

CFG from those edges only: 0→1→2→3→4→5; 5→6 or 5→21; 6→7→8; 8→9 or 8→21; 9→10→11; 11→12 or 11→21; 12→13→14→16→17→18→19; 19→20 or 19→21; 20→21; 21 exits. No back edge. Slot 15 is inside the wide instruction, not a block leader.

What the bytes do, matched to `xdp_drop.c` and to BTF field offsets (bit offset / 8):

- r1 arrives as `struct xdp_md *`. BTF type 13: `data` at bit 0, `data_end` at bit 32, both `__u32` (type 8 → type 9, size 4). Slot 1 reads `data_end` into r3. Slot 2 reads `data` into r1, which drops the context pointer.
- Slot 3–4: r2 = data + 14. `sizeof(struct ethhdr)` is 14 (BTF type 16, size 14). Slot 5 is unsigned `r2 > r3`, the compiled form of `(void *)(eth + 1) > data_end`. Taken returns the r0 written at slot 0.
- Slot 6 writes 2, then slot 7 reads a halfword at data+12. BTF `ethhdr.h_proto` is field 2, bit offset 96. Slot 8 leaves the function unless that halfword's low 32 bits are not 8. The source compares `eth->h_proto != bpf_htons(ETH_P_IP)` with `ETH_P_IP` = `0x0800`. On this little-endian object the immediate is `8`, not `0x0800`.
- Slot 9 adds `0x22` (34 = 14 + 20). BTF `iphdr` size is 20. Slot 10 writes 0 again so the slot 11 failure does not return the 2 from slot 6. Slot 11 is the `ip + 1` bound.
- Slot 12's immediate 12 is not a pointer. `.BTF.ext` core relo, record size 16, section `xdp`, four records, all kind 0:

  | insn byte off | slot | type | access | kind |
  |---|---|---|---|---|
  | `0x8` | 1 | 13 `xdp_md` | `0:1` | 0 |
  | `0x10` | 2 | 13 `xdp_md` | `0:0` | 0 |
  | `0x38` | 7 | 16 `ethhdr` | `0:2` | 0 |
  | `0x60` | 12 | 22 `iphdr` | `0:9:0:0` | 0 |

  Kind 0 is `BPF_CORE_FIELD_BYTE_OFFSET` in `/Volumes/SSD/bs/libbpf-mcu/include-bpf/vmlinux.h` line 10279. `iphdr` field 9 is the anonymous union at bit 96; its member 0 is the `{saddr,daddr}` struct; member 0 of that is `saddr`. 96/8 = 12, which is the immediate already in the slot. Slot 13 adds it to r2 (data+14), so r2 becomes the address of `ip->saddr`. The program never loads those 4 bytes into a register.
- Slot 14–15 and the relocation are the map. Slot 16 calls helper id 1. Slots 17–20 turn a null result into return value 2 and a non-null result into 1.
- Return immediates match `/Volumes/SSD/bs/libbpf-mcu/include-bpf/vmlinux.h` lines 22613–22618: `XDP_ABORTED = 0`, `XDP_DROP = 1`, `XDP_PASS = 2`. The source returns aborted on a short header, drop on a map hit, pass otherwise. r10 is unused. There are no stores.

## Relocations: object symbol, not a map index, not XPOST

Code relocation, `llvm-readelf -r`, section `.relxdp` (REL, not RELA), one entry:

- Offset `0x70` = slot 14.
- `r_info` = `0x0000000c00000001`: symbol index 12, type 1.
- `llvm-readelf` prints type 1 as `R_BPF_64_64`, symbol `blocklist`.
- Symbol 12: `OBJECT`, `GLOBAL`, section 5 (`.maps`), value 0, size 32.
- The 16 instruction bytes at `0x70` are zeros. The addend sitting in the immediate is 0.

`.maps` itself (`llvm-readelf -x .maps`) is 32 zero bytes. The map's parameters are not in those bytes.

BTF type 10, size 32, is the map definition struct: `type` at bit 0, `max_entries` at bit 64, `key` at bit 128, `value` at bit 192. Libbpf's `__uint` encoding is an array length: type's array has 1 element, max_entries' array has 256. `BPF_MAP_TYPE_HASH = 1` (`vmlinux.h` line 10587, `BPF_MAP_TYPE_UNSPEC = 0` on the line above). Key and value are both `__u32`, size 4. BTF type 11 is `VAR blocklist`, linkage 1, pointing at type 10. DATASEC `.maps` (type 32) places that var at offset 0, size 32. This matches `bpf.toml`: `BPF_MAP_TYPE_HASH`, `max_entries = 256`, `key_size = 4`, `value_size = 4`.

Three different references, only one of which is present:

1. **Raw object reference.** The relocation names symbol `blocklist`, a 32-byte object in `.maps`. That is the map.
2. **Not a map-index reference.** `alive2/rocq/upstream/theories/ebpfSyntax.v` lines 211–212 and `ebpfDecoder.v` `decode_lddw_insn` lines 240 and 242 map source register R5 to `PSEUDO_MAP_IDX` and R6 to `PSEUDO_MAP_IDX_VALUE`. This instruction's source field is 0, and both immediates are 0. Nothing in the opcode selects map 0 or any other index.
3. **Not an XPOST relocation.** The file is `ET_REL` / `EM_BPF`. Section names include no `.xpost.meta`, `.xpost.image`, or `.xpost.mem`. Those names are what `tooling/vendor/xpost-elf` uses for a compact image. This object is not one.

Other relocations do not patch opcodes: `.rel.debug_*`, `.rel.BTF` (`R_BPF_64_NODYLD32` on `blocklist` and `LICENSE`), `.rel.BTF.ext` (`R_BPF_64_NODYLD32` on section symbol `xdp`). `license` is the four bytes `47 50 4c 00` (`GPL`), symbol `LICENSE` size 4.

`decode_lddw_insn` (`ebpfDecoder.v` lines 235–237) maps source R0 to `PSEUDO_Constant`. `exec_lddw` (`ebpfBinSem.v` lines 648–652) then writes `Int64.ofwords hi lo`, here 0, and steps the PC twice. That is what the raw slots say. It is the wrong map identity: the map is the `R_BPF_64_64` record, which neither decoder reads.

## Semantic rules actually read

C++ decoder and lifter, read in full unless noted:

- `alive2/src/ebpf_decode.cpp`. Classes it accepts are ALU `0x04`, JMP `0x05`, JMP32 `0x06`, ALU64 `0x07` (lines 7–13, 61–163). Anything else, including LD and LDX, is `unsupported class` (lines 164–167). `CALL` is JMP class with high nibble `0x8`, which is not JA, not EXIT, and not in the compare switch, so it is `unsupported jump opcode` (lines 145–158). There is no 16-byte consume for opcode `0x18`. The same file rejects a non-zero ALU offset except DIV/MOD/MOVSX/NEG (lines 68–97) and rejects a non-zero source register on an immediate ALU or compare (lines 118–119 and 160–161).
- `alive2/src/ebpf_test.cpp` lines 82–88 names the same three opcodes this object needs: `reject_encoding("LDX", 0x61, ...)`, `reject_encoding("LDDW", 0x18, ...)`, `reject_encoding("CALL", 0x85, ..., imm 1)`.
- `alive2/src/ebpf_lift.cpp`. ALU32 MOV/ADD: truncate both sides to i32, operate, `ZExt` back to i64 (lines 516–539, 573–577). ALU64 MOV is the source value itself (lines 561–565); a register MOV is a bare copy (`bare_mov`, lines 138–146). ALU64 ADD is `BinOp::Add` (lines 656–667). ALU64 immediates are sign-extended unless `LiftBug::ImmNoSignExtend` (lines 195–200, 524). JMP compares become `ICmp` then a two-way `Branch`; JGT is `ICmp::UGT`, JNE is `ICmp::NE`, JEQ is `ICmp::EQ` (lines 643–654, 679–693). JMP32 compares the truncated 32-bit values; a JMP32 immediate is `c32` of the unsigned 32-bit pattern (lines 643–651). EXIT is `Return` of r0 as i64 (lines 496–497). A jump target outside `[0, n)` throws (lines 223–226). A backward edge sets `loop` (lines 227–229). No load, store, call, or wide-immediate emitter exists. `ebpf_file.cpp` `read_bytes` (lines 13–18) feeds the entire file to `decode_ebpf`; it does not look up a section. Pointing it at this ELF would decode the ELF header, and `.text` is empty anyway.
- `alive2/src/ebpf.h` is the ALU/JMP sum type only. No memory or call variant.

Rocq theories read for the opcodes that occur. Paths under `alive2/rocq/upstream/theories/`:

- `ebpfDecoder.v` `decode_insn` lines 54–160: ALU32/ALU64 MOV (`code 0xb`, offset 0) and ADD (`code 0x0`); JMP/JMP32 JEQ `0x1`, JGT unsigned `0x2`, JNE `0x5`; EXIT `code 0x9` on JMP64 with imm source, dst r0, src r0, off 0, imm 0; CALL `code 0x8` with imm source and src R0 is `Pcall CallByStaticID` (lines 127–130). Memory mode: opcode high bits `0x3` and class LDX, size field `(opcode >> 3) & 3`, size 0 = Word, size 1 = HalfWord, imm must be 0, result `Pload` (lines 161–177). `find_instr` lines 268–276: opcode `0x18` takes the next word; the low 32 bits of that word must be 0; otherwise `None`.
- `ebpfSyntax.v` lines 204–225 and 233–244: `Pload`, `Plddw`, `Palu`, `Pjmpcmp`, `Pcall`, `Pret`. Pseudo source numbers as cited above. Caller-saved registers are R1–R5 (line 30).
- `ebpfBinSem.v`:
  - `nextinstr` is PC + 1 (lines 66–67). `int64_of_int` is `Int64.repr (Int.signed i)` (line 81). `eval_val_int` sign-extends a W64 immediate (lines 108–116).
  - `eval_alu32` MOV is `Val.longofintu` of the 32-bit source, so the high half is cleared (lines 332–349). `eval_alu64` MOV returns the source; ADD is `Val.addl` (lines 355–371). `exec_alu` writes the destination and steps once (lines 377–390).
  - `eval_cmp64` / `eval_cmp32` (lines 412–444): JGT unsigned uses `Val.cmplu_bool` / `Val.cmpu_bool` with `Cgt`; JNE uses `Cne`; JEQ uses `Ceq`. The 32-bit compare is on `Val.loword`. `exec_jmpcmp` (lines 484–498) adds the offset to PC when the condition is true, then `nextinstr` in both cases, so the landing slot is PC + 1 + off. A `None` condition is `Stuck`.
  - `exec_load` (lines 560–589): a `Vlong` base is turned into a pointer only by `cast_i2p` against `addr_map`; a `Vptr` base is `offset_ptr`. The load is `Mint32` or `Mint16unsigned`. A `Vint` result is zero-extended to `Vlong`. Failure is `Stuck`, not a zero. I did not read CompCert's `Archi.big_endian` for this target, so I am not claiming the Rocq memory chunk is little endian. The ELF and the immediate `8` are little endian, as above.
  - `exec_lddw` for `PSEUDO_Constant` writes the 64-bit immediate and steps twice (lines 648–652). Other pseudo kinds go through `cast_i2p` and `Stuck` if the address is not in `addr_map`.
  - `exec_instr` (lines 888–905) dispatches `Pload`, `Plddw`, `Palu`, `Pjmpcmp`, `Pret`, and `Pcall CallInternal` only. `CallByStaticID` falls into `_ => Stuck`.
  - The small-step relation is different from `exec_instr`. `exec_step_external` (lines 979–990) allows `CallByStaticID` or `CallByBTF` when the parameter `ebpf_call_function` (lines 60–61) returns `Some (res, m')`. It then undefines R1–R5 (`undef_caller_save_regs`, lines 661–667), writes R0, and sets PC to the old PC + 1. It does not say what helper id 1 does. In that constructor, `code_id'` and `tail_call_cnt'` are not constrained by the pre-state. I read no definition that instantiates `ebpf_call_function` for map lookup.
  - `exec_ret` with an empty call stack sets PC to `Vnullptr` and leaves R0 (lines 819–821). `initial_lst_state` (lines 993–1000) starts R1 as `Vptr ctx`, R10 as the stack pointer, other registers `Vundef`. `final_lst_state` (lines 1010–1017) returns R0.
- `ebpfState.v` lines 29 and 83–92: a register file is `Pregmap.t val`; `outcome` is `Next` or `Stuck`; `addr_region` is block, size, and base address. I did not read a packet or hash-map memory theory.

Helper id 1, from a header rather than from the lifter: `/Volumes/SSD/bs/libbpf-mcu/include-bpf/bpf/bpf_helper_defs.h` lines 55–64, `bpf_map_lookup_elem(void *map, const void *key)` assigned `(void *) 1`, returns the value pointer or NULL. `src/Observation/Insn.lean` lines 21–36 also numbers `lookup` as 1 with arity 2. That Lean table is not the C++ IR and is not used as one.

Rules not read, so not used: CompCert `Mem.load` endianness and `Archi` for the BPF target; libbpf's reloc applicator (nothing here claims it rewrites the source field to 1); Alive2 `ir/instr.cpp` `toSMT` for `BinOp` and `ICmp` beyond what `ebpf_lift.cpp` calls; any proof script under `alive2/rocq/upstream/validator/` other than the existence of the tree.

## IR mapping against the C++ lifter only

`lift_ebpf` is never reached for this object. `decode_ebpf` walks 8-byte slots with no relocation argument. Slot 1 is opcode `0x61`, class `0x1`, and lines 164–167 throw `eBPF insn 1: unsupported class in opcode 0x61`. Slots 0 and the later ALU/JMP slots are classifiable, but they are not a program the lifter can build.

If those ALU/JMP opcodes were presented alone, the existing emitters are:

| Slots | Decoded `EbInsn` | IR the current lifter emits |
|---|---|---|
| 0, 6, 10, 18, 20 | `EbAlu` MOV, W32, imm 0 / 2 / 0 / 2 / 1 | `Trunc` to i32, the i32 immediate, `ZExt` to i64. High 32 bits become 0. |
| 3, 17 | `EbAlu` MOV, W64, register | no new arithmetic op; the destination slot is the source value. |
| 4, 9 | `EbAlu` ADD, W64, imm 14 and `0x22` | `BinOp Add` i64, immediate sign-extended. Both immediates are positive, so the sign bit is clear. |
| 12 | `EbAlu` MOV, W64, imm 12 | the i64 immediate 12. The CO-RE record is ignored; the lifter has no BTF input. |
| 13 | `EbAlu` ADD, W64, register | `BinOp Add` i64 of r2 and r1. |
| 5, 11 | `EbJmp` JGT, W64, register | `ICmp UGT` i64, branch to the target block or fall through. |
| 8 | `EbJmp` JNE, W32, imm 8 | truncate dst to i32, `ICmp NE` against i32 8. |
| 19 | `EbJmp` JEQ, W64, imm 0 | `ICmp EQ` i64 against sign-extended 0. |
| 21 | `EbJmp` EXIT | `Return` i64 r0. |

There is no IR mapping for slots 1, 2, 7, 14, 15, or 16. Mapping slot 14 to `IntConst 0` would repeat the constant-`LDDW` mistake above. Mapping slot 16 to a nop, or to `CallInternal`, would not be this lifter: internal calls are not a `EbJmp` variant, and `ebpf_test.cpp` requires `call 1` to throw.

`LiftInit::Zero` puts every unmentioned register at i64 0 (`ebpf_lift.cpp` lines 291–301). `LiftInit::Rocq` poisons r1 and r10 and undefs the rest (lines 304–328). The Rocq initial state I read makes r1 a context pointer. Neither init creates an `xdp_md`, a packet, or a hash map. Register-only SSA and phis at the four join points would be mechanically possible after the gaps below are filled; they are not a conversion of this object. `loop` would stay false: every successor is a later slot.

## Memory, helper, map, loop

- **Memory: required.** Three loads, no stores, no atomics, no stack (r10 never appears). Slot 1: 4 bytes at ctx+4. Slot 2: 4 bytes at ctx+0. Slot 7: 2 bytes at data+12. The lookup key is a pointer into the packet (data+26), not a register-resident word. Bounds are the two unsigned `>` checks, and equality is allowed (`>` not `>=`): a 14-byte frame passes the first check, a 34-byte frame passes the second. The Rocq `exec_load` I read faults if the address is not a `Vptr` in `addr_map`. The C++ lifter has no memory instruction at all (`feasibility-report.md` lines 152 and 160, read this turn).
- **Helper: required.** One call, imm 1, src field 0: `bpf_map_lookup_elem`. Arguments in r1 (map) and r2 (pointer to the 4-byte source address). The only use of the result is null versus non-null (slots 17–20). R2–R5 are dead after the call. No other helper id appears.
- **Map: required.** One map, symbol `blocklist`, hash, 256 entries, key 4, value 4. Identity is the `R_BPF_64_64` at offset `0x70`, not the zero immediate and not a map index. A hit is a non-null value pointer and the function returns 1. A miss returns 2. The value bytes are not inspected.
- **Loop: not required.** No backward offset, no `JA`, no call back into this image. The C file's `asm volatile("" ::: "memory")` is why the ethernet check and the IPv4 length check are separate jumps rather than one range; it is not a loop. `Function::unroll` is irrelevant until a back edge exists.

## Conversion result

**NOT CONVERTED.**

The first instruction the C++ decoder cannot classify is slot 1. Even a decoder that skipped it would still stop on slot 7 (same class), on slots 14–15 (wide immediate plus a relocation the API does not take), and on slot 16 (`unsupported jump opcode` for `0x85`). `exec_instr` does not execute helper id 1 either. Calling the missing pieces unsupported and emitting IR for the ALU prefix would be a different program: r3 and r1 would not be `data_end` and `data`, and the map would not be consulted.

## Proof coverage

No proof covers this object.

- In `ebpfSyntax.v` the only theorems I found are `ireg_eq` and `preg_eq` (lines 24 and 44). `is_label_correct` in `ebpfBinSem.v` sits inside a comment (the block ends at line 57). I found no lemma about `exec_load`, `exec_lddw`, or `exec_step_external`.
- The C++ equivalence work described in `alive2/feasibility-report.md` lines 103–109 and 171 is ALU/JMP plus explicit reject tests. Those reject tests include `0x61`, `0x18`, and `0x85`. I did not re-run the suite. The report's own section 9 says packet memory, helpers, and maps are not connected to Alive2.
- `ebpf_file` cannot be aimed at this ELF and expected to see `xdp_firewall`. It does not parse sections.

The ALU32 zero-extend, ALU64 sign-extend, unsigned JGT, and EXIT-as-return rules are implemented for isolated encodings. They have not been applied to these bytes, because the bytes do not decode.

## Counterexample

Do not drop slot 15 and keep the encoded offsets. Slot 5's offset is +15, and 5 + 1 + 15 = 21 only while slot 15 exists. After deleting the continuation, the image has slots 0..20 and target 21 is out of range. `ebpf_lift.cpp` lines 223–226 throw `jump target out of range` for that. Rewriting only later offsets by −1 is a different edit and is not what the file says.

A behavioral pair, once a later lifter does consume the relocation and the helper, against the stub "treat `r1 = 0 ll` as the integer 0 and treat `call 1` as a nop":

- Frame of 13 bytes. Slot 5 is taken (data+14 > data_end). Return is 0. The map must not be read.
- Frame of 34 bytes, bytes 12–13 equal `08 00`, and the 4 bytes at offset 26 are a key that is present in `blocklist`. The source returns `XDP_DROP` (immediate 1 at slot 20). The nop-call path leaves r0 = 0 from slot 10, copies that into r1, then slot 18 sets r0 = 2 and slot 19 sees r1 == 0 and exits. Observed return 2. Hit and miss become the same answer, so the map is not in the semantics.

A third frame separates the halfword immediate from a big-endian constant: 34 bytes whose bytes 12–13 are `00 08`. The load is not 8, slot 8 is taken, return is 2 (`XDP_PASS`). Comparing against `0x0800` instead of `8` inverts this frame relative to a real IPv4 ethertype on this little-endian object.

## Status

ISSUES
