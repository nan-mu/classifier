# case_mark observation

Observation report for a later implementer. This file does not invent a shared ISA and does not convert the program. Conversion result: **NOT CONVERTED**. No `.alive` file is emitted.

## Evidence

Commands actually run:

- `shasum -a 256 /Volumes/SSD/bs/build/case_mark/bpf.o` → `2d440d2e2f9370670073b5ffe50fc704732e326a76da4b4f99506af44c52649e` (14880 bytes). Matches the requested digest. A second parse of the same bytes reproduced that digest.
- `/opt/homebrew/opt/llvm/bin/llvm-readelf -h -S -s -r -n --notes` on that path.
- `/opt/homebrew/opt/llvm/bin/llvm-objdump -h` and `llvm-objdump -d` on that path.
- `file` reports `ELF 64-bit LSB relocatable, eBPF, version 1 (SYSV), with debug_info, not stripped`.
- Raw slot decode of section `xdp1` (file offset `0x40`, size `0x348`) plus the `maps` and `license` section bytes and the `.BTF` string table. Notes file `/Volumes/SSD/bs/build/case_mark/bpf.toml` was read after the ELF, not instead of it. Its `[xdp]` asm block matches `llvm-objdump -d`. C source `/Volumes/SSD/bs/libbpf-mcu/tests/xdp/case_mark.c` was read as the compiler input named by `bpf.toml`, not as a substitute for the object.

Rules actually read:

- `alive2/src/ebpf.h`, `alive2/src/ebpf_decode.cpp` (full), `alive2/src/ebpf_lift.h` (full), `alive2/src/ebpf_lift.cpp` (full), `alive2/src/ebpf_file.cpp` (full), `alive2/src/ebpf_test.cpp` lines 82–97.
- `alive2/rocq/upstream/theories/ebpfSyntax.v` lines 90–257 (instruction AST, including `Plddw` / `Pload` / `Pstore` / `Palu` / `Pjmpcmp` / `Pcall` / `Pret`).
- `alive2/rocq/upstream/theories/ebpfDecoder.v` (full `decode_insn`, `decode_lddw_insn`, `find_instr`).
- `alive2/rocq/upstream/theories/ebpfBinSem.v`: `nextinstr`; `eval_reg_immw` / `eval_val_int`; `eval_shift_mask`; `swab16` / `eval_end` / `eval_alu32` / `eval_alu64` / `exec_alu`; `eval_cmp32` / `eval_cmp64` / `exec_jmpcmp`; `exec_load` / `exec_store` / `exec_lddw`; `exec_call_internal` / `exec_ret`; `exec_instr`; `ebpf_call_function` (type only); `step` (`exec_step_internal`, `exec_step_external`); `initial_lst_state`; `exec_instr_event`.
- `alive2/rocq/upstream/validator/Extraction.v` lines 13–14 (`Archi.ptr64` extracted true, `Archi.big_endian` extracted false).
- `doc/观察.md` and `doc/局限.md` (observation kinds and stated gaps). `tooling/server/src/bpf_image.rs` lines 24–71 (how this repo names `R_BPF_64_64`).

Not read, so not used as rules: CompCert `Val.offset_ptr`, `decode_val`, and `Mem.storebytes`; `ebpfState.v`; `GlobalSem.v`; `CMemoryModel.v`; `Validation.v` body (a search found no `Theorem` / `Lemma` there); any definition of helper id 1. `ebpfBinSem.v`'s `is_label_correct` sits inside a comment. The semantics file takes `find_instr` and `ebpf_call_function` as section variables; this report does not claim a file that instantiates them was read.

## File, endianness, executable sections

ELF64, relocatable, `EM_BPF`, little endian (`ELFDATA2LSB`, `EI_DATA = 1`), entry 0, no program headers. 27 section headers at offset `0x3360`.

Executable sections (`SHF_ALLOC|SHF_EXECINSTR`), from both `llvm-readelf -S` and `llvm-objdump -h`:

| section | type | size | role |
| --- | --- | --- | --- |
| `.text` | PROGBITS | **0** | empty. Not the program. Same file offset `0x40` as `xdp1`. |
| `xdp1` | PROGBITS | **840** (`0x348`) | the program. Align 8. |

One entry symbol: `xdp_prog1`, `FUNC`, size 840, section index 3 (`xdp1`), value 0. License section `license` is `GPL\0` (symbol `LICENSE`, 4 bytes). It is not executable.

BTF is present: `.BTF` size `0x969`, header magic `0xeb9f`, version 1, flags 0, type length 844, string length 1541. Strings include `xdp_md`, `data`, `data_end`, `ethhdr`, `iphdr`, `udphdr`, `xdp_prog1`, `xdp1`, `bpf_map_def`, `rxcnt`, `LICENSE`, and the source path `case_mark.c`. `.BTF.ext` size `0x66c`. This report decoded the string table, not every BTF type record. `bpf.toml` `[CORE]` records (section name `xdp1`) name the field accesses: `xdp_md` `0:1` and `0:0`, `ethhdr` `0:2`, `iphdr` `0:7` / `0:9:0:1` / `0:8`, `udphdr` `0:3`.

## Map symbol versus the LDDW word versus XPOST

Three different things. Do not collapse them.

1. Raw object slots 20–21 (byte offset `0xa0` inside `xdp1`):

```
20  18 01 00 00  00 00 00 00    opcode 0x18 dst=r1 src=0 off=0 imm=0
21  00 00 00 00  00 00 00 00    reserved 0, high imm 0
```

`src=0` is the constant form (`PSEUDO_Constant` in `ebpfDecoder.v` `decode_lddw_insn`, the `R0` case). The immediate in the file is 0, not a map fd and not a map index. `src=1` would be `PSEUDO_MAP_FD`. `src=5` would be `PSEUDO_MAP_IDX`. Neither is what the bytes say.

2. Relocation, separate from those bytes. `.relxdp1` (`SHT_REL`, info = section 3, one 16-byte record):

| offset | type | symbol |
| --- | --- | --- |
| `0xa0` | **1 = `R_BPF_64_64`** | index 12 = `rxcnt` |

`tooling/server/src/bpf_image.rs` `map_lddw_slots` treats type 1 on the program section as the LDDW map slot (here slot `0xa0/8 = 20`). The symbol `rxcnt` is `OBJECT`, size 20, section `maps`. The `maps` bytes are a `bpf_map_def`:

| field | value |
| --- | --- |
| type | 2 = `BPF_MAP_TYPE_ARRAY` |
| key_size | 4 |
| value_size | 8 |
| max_entries | 256 |
| map_flags | 0 |

That matches `bpf.toml` `[maps.rxcnt]` and the C `SEC("maps")` definition. The loader, not the raw immediate, is what binds this LDDW to `rxcnt`. There is no map-index immediate in the object. Index 0 would only coincide with `rxcnt` while `rxcnt` stays the first map.

3. This object is not an XPOST container. No `.xpost.meta` / `.xpost.image`. `tooling/vendor/xpost-elf` is a different layout. Do not run it on this file and do not describe `.relxdp1` as an XPOST relocation.

Other relocations are not the map reference. `.rel.BTF` has two `R_BPF_64_NODYLD32` (type 4) records, symbols `LICENSE` and `rxcnt`. `.rel.debug_*` and `.rel.BTF.ext` point at debug/BTF section symbols and at `xdp1`. None of them rewrite the LDDW immediate.

## Entries and instruction list

105 slots, 8 bytes, little endian. 104 logical instructions: slots 20 and 21 are one LDDW. `llvm-objdump -d` numbers 0..20 then 22..104 and hides slot 21 inside `r1 = 0x0 ll`.

Jump slots, using `index + 1 + off` (`jump_target` in `ebpf_decode.cpp`; Rocq `exec_jmpcmp` adds `off` then `nextinstr` adds 1). All offsets are positive int16. No backward target, so `ebpf_lift.cpp` `build_blocks` would not set `loop` on these edges. There is no `JA`.

| slot | encoding | off | target | fall-through |
| --- | --- | --- | --- | --- |
| 5 | `0x2d` JGT64 `r6 > r2` | +98 | 104 `L1` | 6 |
| 7 | `0x56` JNE32 `w1 != 8` | +96 | 104 | 8 |
| 10 | `0x2d` JGT64 `r7 > r2` | +93 | 104 | 11 |
| 12 | `0x56` JNE32 `w1 != 0x11` | +91 | 104 | 13 |
| 15 | `0x2d` JGT64 `r1 > r2` | +88 | 104 | 16 |
| 23 | `0x15` JEQ64 `r0 == 0` | +3 | 27 `L0` | 24 |

`L1` is slot 104 `exit`. `L0` is slot 27. Early exits leave `r0 = 1` from slot 0. The success path executes slot 103 `w0 = 3` and then falls into the same exit.

Class counts (logical instructions):

| class | slots | C++ `decode_ebpf` |
| --- | --- | --- |
| ALU32 mov/add/or/lsh/rsh/and/xor | 42 | accepted |
| ALU64 mov/add | 9 | accepted |
| JMP JGT64 / JNE32 / JEQ64 / EXIT | 7 | accepted |
| ALU32 `END` `0xdc` imm 16 | 1 (slot 100) | rejected, unsupported ALU opcode |
| LDX/STX memory | 43 | rejected, unsupported class |
| LDDW `0x18` plus zero trailer | 1 (slots 20–21) | rejected, unsupported class. Trailer `0x00` is not its own instruction |
| CALL `0x85` imm 1 | 1 (slot 22) | rejected, unsupported jump opcode |

Per-slot list. `off` is the signed int16 field. Memory `src` is the address register in the encoding byte (high nibble); for STX the value register is that nibble and the address register is `dst`.

| slot | op | kind | dst | src | off | imm | C++ | Rocq decode (read) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | `b4` | ALU32 MOV K | r0 | 0 | 0 | 1 | Mov W32 | `Palu MOV W32` |
| 1 | `61` | LDX W | r2 | r1 | 4 | 0 | reject class | `Pload Word` |
| 2 | `61` | LDX W | r8 | r1 | 0 | 0 | reject class | `Pload Word` |
| 3 | `bf` | ALU64 MOV X | r6 | r8 | 0 | 0 | Mov W64 | `Palu MOV W64` |
| 4 | `07` | ALU64 ADD K | r6 | 0 | 0 | 14 | Add W64 | `Palu ADD W64` |
| 5 | `2d` | JMP64 JGT X | r6 | r2 | 98 | 0 | Jgt W64 | `Pjmpcmp (GT Unsigned) W64` |
| 6 | `69` | LDX H | r1 | r8 | 12 | 0 | reject class | `Pload HalfWord` |
| 7 | `56` | JMP32 JNE K | r1 | 0 | 96 | 8 | Jne W32 | `Pjmpcmp NE W32` |
| 8 | `bf` | ALU64 MOV X | r7 | r8 | 0 | 0 | Mov W64 | `Palu MOV W64` |
| 9 | `07` | ALU64 ADD K | r7 | 0 | 0 | 34 | Add W64 | `Palu ADD W64` |
| 10 | `2d` | JMP64 JGT X | r7 | r2 | 93 | 0 | Jgt W64 | `Pjmpcmp (GT Unsigned) W64` |
| 11 | `71` | LDX B | r1 | r6 | 9 | 0 | reject class | `Pload Byte` |
| 12 | `56` | JMP32 JNE K | r1 | 0 | 91 | 17 | Jne W32 | `Pjmpcmp NE W32` |
| 13 | `bf` | ALU64 MOV X | r1 | r8 | 0 | 0 | Mov W64 | `Palu MOV W64` |
| 14 | `07` | ALU64 ADD K | r1 | 0 | 0 | 42 | Add W64 | `Palu ADD W64` |
| 15 | `2d` | JMP64 JGT X | r1 | r2 | 88 | 0 | Jgt W64 | `Pjmpcmp (GT Unsigned) W64` |
| 16 | `b4` | ALU32 MOV K | r1 | 0 | 0 | 17 | Mov W32 | `Palu MOV W32` |
| 17 | `63` | STX W | r10 | r1 | -4 | 0 | reject class | `Pstore Word` |
| 18 | `bf` | ALU64 MOV X | r2 | r10 | 0 | 0 | Mov W64 | `Palu MOV W64` |
| 19 | `07` | ALU64 ADD K | r2 | 0 | 0 | -4 | Add W64 | `Palu ADD W64` |
| 20 | `18` | LDDW | r1 | 0 | 0 | 0 | reject class | `Plddw PSEUDO_Constant` of 0, if the relocation is ignored |
| 21 | `00` | LDDW high |  |  |  | 0 | not a separate insn | consumed with slot 20 (`reserved` must be 0) |
| 22 | `85` | CALL K | r0 | 0 | 0 | 1 | reject jump | `Pcall CallByStaticID 1` |
| 23 | `15` | JMP64 JEQ K | r0 | 0 | 3 | 0 | Jeq W64 | `Pjmpcmp EQ W64` |
| 24 | `79` | LDX DW | r1 | r0 | 0 | 0 | reject class | `Pload DBWord` |
| 25 | `07` | ALU64 ADD K | r1 | 0 | 0 | 1 | Add W64 | `Palu ADD W64` |
| 26 | `7b` | STX DW | r0 | r1 | 0 | 0 | reject class | `Pstore DBWord` |
| 27 | `69` | LDX H | r1 | r8 | 0 | 0 | reject class | `Pload HalfWord` |
| 28 | `69` | LDX H | r2 | r8 | 6 | 0 | reject class | `Pload HalfWord` |
| 29 | `6b` | STX H | r8 | r2 | 0 | 0 | reject class | `Pstore HalfWord` |
| 30 | `69` | LDX H | r2 | r8 | 8 | 0 | reject class | `Pload HalfWord` |
| 31 | `69` | LDX H | r3 | r8 | 2 | 0 | reject class | `Pload HalfWord` |
| 32 | `6b` | STX H | r8 | r3 | 8 | 0 | reject class | `Pstore HalfWord` |
| 33 | `6b` | STX H | r8 | r2 | 2 | 0 | reject class | `Pstore HalfWord` |
| 34 | `69` | LDX H | r2 | r8 | 10 | 0 | reject class | `Pload HalfWord` |
| 35 | `69` | LDX H | r3 | r8 | 4 | 0 | reject class | `Pload HalfWord` |
| 36 | `6b` | STX H | r8 | r3 | 10 | 0 | reject class | `Pstore HalfWord` |
| 37 | `6b` | STX H | r8 | r1 | 6 | 0 | reject class | `Pstore HalfWord` |
| 38 | `6b` | STX H | r8 | r2 | 4 | 0 | reject class | `Pstore HalfWord` |
| 39 | `b4` | ALU32 MOV K | r1 | 0 | 0 | `0x4d7100cb` | Mov W32 | `Palu MOV W32` |
| 40 | `63` | STX W | r6 | r1 | 16 | 0 | reject class | `Pstore Word` |
| 41 | `b4` | ALU32 MOV K | r1 | 0 | 0 | 0 | Mov W32 | `Palu MOV W32` |
| 42 | `6b` | STX H | r6 | r1 | 10 | 0 | reject class | `Pstore HalfWord` |
| 43 | `71` | LDX B | r3 | r8 | 14 | 0 | reject class | `Pload Byte` |
| 44 | `64` | ALU32 LSH K | r3 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 45 | `71` | LDX B | r2 | r8 | 15 | 0 | reject class | `Pload Byte` |
| 46 | `4c` | ALU32 OR X | r3 | r2 | 0 | 0 | Or W32 | `Palu OR W32` |
| 47 | `71` | LDX B | r2 | r8 | 16 | 0 | reject class | `Pload Byte` |
| 48 | `64` | ALU32 LSH K | r2 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 49 | `71` | LDX B | r4 | r8 | 17 | 0 | reject class | `Pload Byte` |
| 50 | `4c` | ALU32 OR X | r2 | r4 | 0 | 0 | Or W32 | `Palu OR W32` |
| 51 | `0c` | ALU32 ADD X | r2 | r3 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 52 | `71` | LDX B | r3 | r8 | 18 | 0 | reject class | `Pload Byte` |
| 53 | `64` | ALU32 LSH K | r3 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 54 | `71` | LDX B | r4 | r8 | 19 | 0 | reject class | `Pload Byte` |
| 55 | `4c` | ALU32 OR X | r3 | r4 | 0 | 0 | Or W32 | `Palu OR W32` |
| 56 | `0c` | ALU32 ADD X | r2 | r3 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 57 | `71` | LDX B | r3 | r8 | 20 | 0 | reject class | `Pload Byte` |
| 58 | `64` | ALU32 LSH K | r3 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 59 | `71` | LDX B | r4 | r8 | 21 | 0 | reject class | `Pload Byte` |
| 60 | `4c` | ALU32 OR X | r3 | r4 | 0 | 0 | Or W32 | `Palu OR W32` |
| 61 | `0c` | ALU32 ADD X | r2 | r3 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 62 | `71` | LDX B | r3 | r8 | 22 | 0 | reject class | `Pload Byte` |
| 63 | `64` | ALU32 LSH K | r3 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 64 | `71` | LDX B | r4 | r8 | 23 | 0 | reject class | `Pload Byte` |
| 65 | `4c` | ALU32 OR X | r3 | r4 | 0 | 0 | Or W32 | `Palu OR W32` |
| 66 | `0c` | ALU32 ADD X | r2 | r3 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 67 | `71` | LDX B | r3 | r8 | 24 | 0 | reject class | `Pload Byte` |
| 68 | `64` | ALU32 LSH K | r3 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 69 | `71` | LDX B | r4 | r8 | 25 | 0 | reject class | `Pload Byte` |
| 70 | `4c` | ALU32 OR X | r3 | r4 | 0 | 0 | Or W32 | `Palu OR W32` |
| 71 | `0c` | ALU32 ADD X | r2 | r3 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 72 | `71` | LDX B | r4 | r8 | 26 | 0 | reject class | `Pload Byte` |
| 73 | `64` | ALU32 LSH K | r4 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 74 | `71` | LDX B | r3 | r8 | 27 | 0 | reject class | `Pload Byte` |
| 75 | `4c` | ALU32 OR X | r4 | r3 | 0 | 0 | Or W32 | `Palu OR W32` |
| 76 | `71` | LDX B | r3 | r8 | 32 | 0 | reject class | `Pload Byte` |
| 77 | `64` | ALU32 LSH K | r3 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 78 | `71` | LDX B | r5 | r8 | 33 | 0 | reject class | `Pload Byte` |
| 79 | `4c` | ALU32 OR X | r3 | r5 | 0 | 0 | Or W32 | `Palu OR W32` |
| 80 | `71` | LDX B | r5 | r8 | 30 | 0 | reject class | `Pload Byte` |
| 81 | `64` | ALU32 LSH K | r5 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 82 | `71` | LDX B | r0 | r8 | 31 | 0 | reject class | `Pload Byte` |
| 83 | `4c` | ALU32 OR X | r5 | r0 | 0 | 0 | Or W32 | `Palu OR W32` |
| 84 | `0c` | ALU32 ADD X | r2 | r4 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 85 | `71` | LDX B | r4 | r8 | 29 | 0 | reject class | `Pload Byte` |
| 86 | `71` | LDX B | r0 | r8 | 28 | 0 | reject class | `Pload Byte` |
| 87 | `64` | ALU32 LSH K | r0 | 0 | 0 | 8 | Lsh W32 | `Palu LSH W32` |
| 88 | `4c` | ALU32 OR X | r0 | r4 | 0 | 0 | Or W32 | `Palu OR W32` |
| 89 | `0c` | ALU32 ADD X | r2 | r0 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 90 | `0c` | ALU32 ADD X | r2 | r5 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 91 | `0c` | ALU32 ADD X | r2 | r3 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 92 | `bc` | ALU32 MOV X | r3 | r2 | 0 | 0 | Mov W32 | `Palu MOV W32` |
| 93 | `74` | ALU32 RSH K | r3 | 0 | 0 | 16 | Rsh W32 | `Palu RSH W32` |
| 94 | `54` | ALU32 AND K | r2 | 0 | 0 | `0xffff` | And W32 | `Palu AND W32` |
| 95 | `0c` | ALU32 ADD X | r2 | r3 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 96 | `bc` | ALU32 MOV X | r3 | r2 | 0 | 0 | Mov W32 | `Palu MOV W32` |
| 97 | `74` | ALU32 RSH K | r3 | 0 | 0 | 16 | Rsh W32 | `Palu RSH W32` |
| 98 | `0c` | ALU32 ADD X | r3 | r2 | 0 | 0 | Add W32 | `Palu ADD W32` |
| 99 | `a4` | ALU32 XOR K | r3 | 0 | 0 | -1 | Xor W32 | `Palu XOR W32` |
| 100 | `dc` | ALU32 END BE | r3 | 0 | 0 | 16 | reject ALU `0xd0` | `Palu (END BE32 S16) W32` |
| 101 | `6b` | STX H | r6 | r3 | 10 | 0 | reject class | `Pstore HalfWord` |
| 102 | `6b` | STX H | r7 | r1 | 6 | 0 | reject class | `Pstore HalfWord` |
| 103 | `b4` | ALU32 MOV K | r0 | 0 | 0 | 3 | Mov W32 | `Palu MOV W32` |
| 104 | `95` | EXIT | r0 | 0 | 0 | 0 | Exit | `Pret` |

`ebpf_test.cpp` `reject_unknown` already requires `decode_ebpf` to throw on `0x61`, `0x63`, `0x18`, `0x85`, and on `END` opcode `0xd4`. Slot 100 is `0xdc` (same `0xd0` code nibble, source bit set). The switch in `ebpf_decode.cpp` has no `0xd0` arm, so it takes the unsupported-ALU path. That test was read; it was not executed in this pass.

## Real disassembly

`llvm-objdump -d` disassembled section `xdp1` only. It did not disassemble empty `.text`.

```
0000000000000000 <xdp_prog1>:
       0:	w0 = 0x1
       1:	w2 = *(u32 *)(r1 + 0x4)
       2:	w8 = *(u32 *)(r1 + 0x0)
       3:	r6 = r8
       4:	r6 += 0xe
       5:	if r6 > r2 goto +0x62 <L1>
       6:	w1 = *(u16 *)(r8 + 0xc)
       7:	if w1 != 0x8 goto +0x60 <L1>
       8:	r7 = r8
       9:	r7 += 0x22
      10:	if r7 > r2 goto +0x5d <L1>
      11:	w1 = *(u8 *)(r6 + 0x9)
      12:	if w1 != 0x11 goto +0x5b <L1>
      13:	r1 = r8
      14:	r1 += 0x2a
      15:	if r1 > r2 goto +0x58 <L1>
      16:	w1 = 0x11
      17:	*(u32 *)(r10 - 0x4) = w1
      18:	r2 = r10
      19:	r2 += -0x4
      20:	r1 = 0x0 ll
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
      39:	w1 = 0x4d7100cb
      40:	*(u32 *)(r6 + 0x10) = w1
      41:	w1 = 0x0
      42:	*(u16 *)(r6 + 0xa) = w1
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
     102:	*(u16 *)(r7 + 0x6) = w1
     103:	w0 = 0x3
<L1>:
     104:	exit
```

What that program is, tied to the C that was read, not to a new ISA:

- Slot 0 plants `XDP_DROP` (1). Slot 103 plants `XDP_TX` (3) only if every bounds/type jump falls through.
- Slots 1–2 load `xdp_md.data_end` (`u32` at +4) into `r2` and `xdp_md.data` (`u32` at +0) into `r8`. Both loads are 32-bit, then used as 64-bit pointers. BTF calls those fields `__u32`.
- Slots 3–5: `eth+1` (`data+14`) `>` `data_end` → drop. Equality is not taken (`JGT`, not `JGE`).
- Slot 6–7: `eth->h_proto` as a host `u16`. On this little-endian object the compare immediate is `8`, which is `bpf_htons(0x0800)`, not `0x0800`. Do not bswap this load.
- Slots 8–10: `ip+1` (`data+0x22`) `>` `data_end` → drop. Again strict.
- Slots 11–12: `ip->protocol` byte at `data+14+9` against `17` (`IPPROTO_UDP`).
- Slots 13–15: `udp+1` (`data+0x2a`) `>` `data_end` → drop. A 42-byte packet is in range.
- Slots 16–19: spill key `u32 0x11` at `r10-4`, and point `r2` at that slot.
- Slots 20–22: relocated LDDW of map `rxcnt`, then helper id 1 (`bpf_map_lookup_elem(r1=map, r2=key)`). The C call is `bpf_map_lookup_elem(&rxcnt, &proto)`.
- Slots 23–26: if the returned pointer is non-null, `*value += 1` as a plain 64-bit load/add/store, not an atomic.
- Slots 27–38: `swap_mac`. Six host `u16` loads and six `u16` stores at `data+0,2,4,6,8,10`. Byte order is not swapped; the halves move as they were loaded.
- Slots 39–40: store `0x4d7100cb` as `u32` at `data+14+16` (`ip->daddr`). The C macro `MARK_DST` is `0xcb00714d`; `bpf_htonl` on a little-endian target is already applied by the compiler into this immediate. Do not bswap it again. Bytes on the wire are `cb 00 71 4d` (203.0.113.77).
- Slots 41–42: store `u16 0` at `ip->check` (`data+14+10`).
- Slots 43–100: one's-complement sum of the 20 header bytes as big-endian pairs `(b[i]<<8)|b[i+1]`, two folds `(sum & 0xffff) + (sum >> 16)`, then `xor -1`, then `be16`. Pairs are bytes `[0..13]`, `[18..19]`, `[16..17]`, `[14..15]`, which is the header with the checksum field (bytes 10–11) included after it was zeroed. Slot 100 is the only byte-swap in the object.
- Slot 101: store that `u16` back to `ip->check`.
- Slot 102: store `u16 0` at `udp->check` (`data+0x22+6`). IPv4 allows a zero UDP checksum; the C function does not recompute it.
- `r6`, `r7`, `r8` are live across the helper. `r1`–`r5` are arguments and are dead after the call until rewritten. `r10` is only used for the key spill.

`ebpf_file.cpp` reads the whole file and passes those bytes to `execute_ebpf`. This object is an ELF, not a raw instruction image. Feeding it `bpf.o` would decode the ELF header. The bytes to decode are the 840 bytes of `xdp1`.

## Semantic rules that were read

C++ decoder (`alive2/src/ebpf_decode.cpp`): classes ALU `0x4`, ALU64 `0x7`, JMP `0x5`, JMP32 `0x6` only. Anything else throws `unsupported class`. Inside ALU, `END` (`code == 0xd0`) is not a named arm and throws `unsupported ALU opcode` when the offset is 0. Inside JMP, `CALL` (`code == 0x80`) is not a named arm and throws `unsupported jump opcode`. `EXIT` (`0x90`) requires class JMP, no source bit, dst=src=0, off=0, and ignores the immediate only in the sense that the check does not read it: the malformed-EXIT test is `cls != JMP || reg_src || disp != 0 || src != 0 || dst != 0`. Slot 104 matches. There is no LDDW pairing: slot 20 would throw before slot 21 is looked at.

C++ lifter, only for encodings the decoder returns (`alive2/src/ebpf_lift.cpp`):

- ALU32: truncate both operands to `i32`, operate, `zext` back to `i64`. Immediate is zero-extended to `i64` then truncated (`sign_imm` is false for W32). Shifts are `Shl` / `LShr` with the amount masked by 31 unless `LiftBug::ShiftWithoutMask`.
- ALU64: `i64` ops. Immediate is sign-extended (`imm64(..., true)`), which matters for slot 19 (`-4`). `Mov` W64 is a value copy (`bare_mov`).
- `JGT` → `ICmp::UGT`. `JNE` → `ICmp::NE`. `JEQ` → `ICmp::EQ`. Width follows the jump class. A taken edge is `jump_target`; the other edge is the next block. `EXIT` is `Return` of `r0` as `i64`.
- `build_blocks` sets `loop` only when a target index is `<=` the jump index. Not true here.
- `pointer_alu` / `pointer_jmp` only record `EbSite::pointer_use`. `emit_alu` still emits integer binops. `LiftInit::Rocq` makes initial `r1` and `r10` `PoisonValue` with origin `Pointer`; `LiftInit::Zero` makes them integer 0 unless named inputs. Neither is a stack or a packet.
- The concrete walker (`Lifter::concrete`) evaluates `BinOp` Add/Sub/And/UDiv/SDiv and `ICmp` EQ/UGT only. `Or`, `Shl`, `LShr`, `Xor`, `NE`, `Trunc`, and `ZExt` hit `stop_unsupported`. A `MemInstr` is marked `MemorySummary::Changed` and then unsupported. The lifter never emits `MemInstr`.

Rocq decoder (`ebpfDecoder.v`), for the opcodes in this object:

- ALU32/ALU64 codes `0x0, 0x4, 0x5, 0x6, 0x7, 0xa, 0xb` match the arithmetic above, including MOV with offset 0.
- Code `0xd` with the source bit set and class ALU32 is `END BE32`, and imm `0x10` selects `S16`. That is slot 100. Imm `0x20` / `0x40` are the other sizes; this object uses 16 only.
- JMP64 code `0x8`, source bit clear, `src_reg = R0`, offset 0 → `Pcall CallByStaticID imm`. Slot 22 is helper id 1, not `CallInternal` (that is `src_reg = R1`) and not `CallByBTF` (`src_reg = R2`).
- JMP64 `0x9` → `Pret`. Conditional codes `0x1` EQ, `0x2` unsigned GT, `0x5` NE. No JSET in this object.
- LDX/STX with mode bits `0x60` → unsigned `Pload` / `Pstore` at sizes Word / HalfWord / Byte / DBWord. Every memory op in this object is that mode. No sign-extending load (`0x80`), no probe, no atomic (`0xc0`), no `ST` immediate store.
- `find_instr` on opcode `0x18` reads the next word, requires its low 32 bits to be 0, and calls `decode_lddw_insn`. `src_reg = R0` yields `PSEUDO_Constant`. The relocation is not an input to this function.

Rocq step rules that were read (`ebpfBinSem.v`):

- `eval_alu32` takes the low 32 bits, then `Val.longofintu`, except `END`, which returns `eval_end` directly. `eval_alu64` sign-extends immediates via `int64_of_int` (`Int.signed`). Shifts go through `eval_shift_mask` (31 or 63). The shifts in this object are immediates 8 and 16.
- `eval_end` for `BE32`: if `Archi.big_endian` then `eval_end_trunction` (zero-extend, no swap); else `swab16` / `swab32` / `swab64`. `Extraction.v` extracts `Archi.big_endian` as false and `Archi.ptr64` as true. Under that extraction, slot 100 swaps. `swab16` exchanges the low two bytes. A big-endian `Archi` would not swap, which disagrees with this little-endian object.
- `exec_jmpcmp` uses unsigned `Val.cmplu_bool` / `Val.cmpu_bool` for `GT Unsigned` and `NE` / `EQ`. The static folder (`eval_cmp_static`) does not decide the comparisons in this object (`JGT` of two different registers; `JNE` against 8 or 17; `JEQ` against 0 is not in the static imm table). Comparison failure is `Stuck`, not a fall-through.
- `exec_load`: a `Vptr` address is `offset_ptr`; a `Vlong` address is `cast_i2p` through `addr_map`, then `loadv_unaligned` (`Mint8unsigned` / `Mint16unsigned` / `Mint32` / `Mint64`). The loaded `Vint` is zero-extended to `Vlong`. `exec_store` only calls `Val.offset_ptr` on the address register. It does not call `cast_i2p`. `Val.offset_ptr` itself was not read. The packet pointer in this program is produced by a `u32` load (`Vlong` after `load_value_casting`), then `ADD`. Stores of that pointer therefore do not take the `cast_i2p` path that loads take. That asymmetry is in the definitions that were read.
- `exec_lddw` of `PSEUDO_Constant` writes `Int64.ofwords hi lo` and advances PC twice. Any other pseudo type goes through `cast_i2p` and is `Stuck` on `None`. Ignoring `.relxdp1` therefore means `r1 = 0`, not "map 0".
- `exec_instr` implements `Pcall` only for `CallInternal`. `CallByStaticID` falls through to `Stuck` there. The external rule is separate: `exec_step_external` requires `ebpf_call_function imm r1 r2 r3 r4 r5 state = Some (res, m')`, then sets `r0 = res`, undefines `r1`–`r5`, and sets PC to current+1. `ebpf_call_function` is an uninterpreted parameter. No equation for id 1 was read. `exec_instr_event` records `eBPF_vload` / `eBPF_vstore` only; the external step hard-wires the trace event `eBPF_ext_call`. A map increment is an ordinary `Pload`/`Pstore`, not a `MapWrite` constructor in this semantics.
- `initial_lst_state` sets PC at the code block, `R10` to a stack pointer at offset `bpf_stack_size` (512), `R1` to a context pointer, other registers `Vundef`, and requires the stack bytes `[0, 512)` to be `Mint8unsigned`-accessible. It does not build an `xdp_md` or a packet. `exec_ret` on an empty call stack sets PC to `Vnullptr` and leaves `R0`. `final_lst_state` accepts `R0` as `Vlong` or `Vptr`.

`doc/观察.md` names the observations a matcher wants: `Helper`, `Branch`, `Return`, `MapWrite`, `PacketWrite`. Stack spills are explicitly not `MapWrite` or `PacketWrite`. Proposition 2 is stated there as unfinished. This program needs all five kinds. `doc/局限.md` says pointer-versus-counter loops are not matched strictly; this object has no back edge, so that limitation is not why conversion fails.

## IR mapping against the existing C++ lifter only

The lifter never sees this section. `decode_ebpf` throws at slot 1 (`0x61`). The rows below are the IR that the functions which were read would emit for the same `EbAlu` / `EbJmp` values, if the memory, LDDW, call, and `END` slots were not in the stream. They are not a translation of `bpf.o`.

| encodings present | IR from `emit_alu` / `emit_cmp` / `emit` |
| --- | --- |
| `b4` MOV32 K, `bc` MOV32 X | `trunc` to `i32`, copy, `zext` to `i64`. High 32 bits become 0. |
| `0c` ADD32 X | `trunc` both, `BinOp::Add` on `i32`, `zext`. |
| `4c` OR32 X | `BinOp::Or` on `i32`, `zext`. |
| `64` LSH32 K (imm 8 only) | `BinOp::Shl` on `i32`, amount `And` 31, `zext`. |
| `74` RSH32 K (imm 16 only) | `BinOp::LShr`, amount `And` 31, `zext`. |
| `54` AND32 K `0xffff` | `BinOp::And` on `i32`, `zext`. |
| `a4` XOR32 K `-1` | `BinOp::Xor` with `i32` `0xffffffff`, `zext`. This is a 32-bit not, not a 64-bit not. |
| `bf` MOV64 X | copy the `i64` value. No trunc. |
| `07` ADD64 K | `BinOp::Add` on `i64`. Imm sign-extended. `+14`, `+34`, `+42`, `-4`, `+1` all fit. |
| `2d` JGT64 X | `ICmp::UGT` on `i64`, branch to target or fall-through. |
| `56` JNE32 K | `trunc` dst, `i32` immediate, `ICmp::NE`. |
| `15` JEQ64 K 0 | `ICmp::EQ` against `i64` 0. |
| `95` EXIT | `Return` of the `i64` in `r0`. |

No IR exists in this lifter for:

- any `Pload` / `Pstore` (slots 1, 2, 6, 11, 17, 24, 26, 27–38, 40, 42, 43, 45, 47, 49, 52, 54, 57, 59, 62, 64, 67, 69, 72, 74, 76, 78, 80, 82, 85, 86, 101, 102)
- LDDW slots 20–21, and the `R_BPF_64_64` against `rxcnt`
- `call 1` (slot 22), including the clobber of `r1`–`r5` and the `r0` result
- `be16` (slot 100)

`r10-4` would be integer arithmetic on whatever `r10` was initialized to. The lifter does not allocate a 512-byte stack. Calling the missing rows "unsupported" inside a successful lift would be wrong: the decoder aborts the whole section.

## Memory, helper, map, loop

- Loop: no. Every jump target is strictly after the jump. One join at slot 27 (`L0`) and one join at slot 104 (`L1`). No call-internal frame (`exec_call_internal` is not the call in this object).
- Helper: yes, one. Static id 1, arguments `r1` = relocated map, `r2` = pointer to the `u32` key at `fp-4`. Key value is the constant 17. `r3`–`r5` are not set up by this program. Result in `r0`. Rocq's external step undefines `r1`–`r5` and keeps `r6`–`r9` and `r10`. The C++ lifter has no call.
- Map: yes, one array `rxcnt`, 256 × 8-byte values, 4-byte key. The only update is a non-atomic `u64` increment at offset 0 of the looked-up value, skipped when `r0` is 0. There is no `map_update_elem`, no delete, no syscall helper besides id 1. The key slot is a stack spill, not a map write.
- Packet / context memory: yes.
  - Context reads: `u32` at `r1+0` and `r1+4` only.
  - Packet reads that the bounds checks establish before use: 14 bytes to pass slot 5, then `u16` at +12; 34 bytes to pass slot 10, then the protocol byte; 42 bytes to pass slot 15. The checksum then reads `data+14` through `data+33` (the 20-byte IPv4 header). MAC swap reads `data+0` through `data+11`.
  - Packet writes: six `u16` MAC slots at `data+0..+10`; `u32` at `data+30` (`daddr`); `u16` at `data+24` twice (`check`, zero then final); `u16` at `data+40` (`udp->check = 0`).
  - Stack write: one `u32` at `r10-4`. Initial Rocq `R10` is `Vptr` at offset 512, so the address is offset 508, inside the `[0, 512)` region named by `initial_lst_state`. This report did not read a proof that `storebytes` of 4 bytes at 508 succeeds.
- Endianness: the ELF and the BPF immediates are little endian. Packet fields are network order only where the compiler already folded `htons`/`htonl` into an immediate (`h_proto` compare `8`, `daddr` immediate `0x4d7100cb`) or where slot 100 does `be16`. Ordinary loads and stores are not byte swaps.

## Conversion result

**NOT CONVERTED.**

`decode_ebpf` cannot return an `EbInsn` vector for section `xdp1`. `lift_ebpf` is only defined on that vector. `alive2_trace` calls `decode_ebpf` first. No Alive function was built. No `.alive` text is written.

## Proof coverage

Nothing read is a proof that this object matches its C source, an XDP action, or a checksum identity.

- Decoder and `exec_*` are definitions. The only `Lemma` hit in `ebpfBinSem.v` is inside a comment. `Validation.v` had no theorem heading in a search; its body was not read.
- `step` does not contain helper 1. `exec_instr` returns `Stuck` for `CallByStaticID`. The external rule quantifies over an arbitrary `ebpf_call_function`.
- `exec_lddw` of the raw word is the constant 0. The map binding is an ELF relocation the decoder does not take.
- `exec_store` and `exec_load` do not treat integer packet pointers the same way. No `xdp_md` layout is constructed by `initial_lst_state`.
- `eval_end` depends on `Archi.big_endian`. The extraction file sets it false. A proof that does not fix that flag does not fix slot 100.
- The C++ concrete interpreter does not evaluate the ALU ops this program uses most (`Or`, shifts, `Xor`, `NE`, trunc/zext), and it has no memory instruction to evaluate.
- `doc/观察.md` says the observation bijection is not proved. Even a future lift would still owe `Helper(1)`, the six `Branch`es, one `Return`, one `MapWrite` of an 8-byte counter at key 17, and the `PacketWrite`s listed above. Stack slot `fp-4` must not be reported as a map write.

## Counterexample idea

Do not compare return codes alone. A null lookup and a successful lookup both return 3 on a 42-byte UDP/IPv4 frame. The counter must include the map cell and two header bytes.

Packet, little endian in the BPF loads, network order on the wire:

- 14-byte Ethernet, ethertype bytes `08 00` (host `u16` load = 8).
- IPv4 header, `protocol = 17`, IHL such that the fixed 20-byte header is what the checksum walks (the object never reads `ihl`; it always sums 20 bytes and always treats UDP as starting at `data+34`).
- `data_end - data = 42`. Slot 15 is `JGT`, so 42 is accepted. A model that branches on `>=` drops this packet and returns 1. That is the wrong action.
- Map `rxcnt` key 17 holds `u64 0`, and the lookup returns that cell.

Expected, if relocation and helper 1 are real: the cell becomes 1; `ip->daddr` bytes are `cb 00 71 4d`; `udp->check` is `00 00`; `ip->check` is `htons` of the one's complement of that 20-byte header after `daddr` was written and `check` was cleared. MAC halves are swapped as raw `u16`s.

Divergences that must not pass:

- Decode the LDDW as the constant 0 and let helper 1 return null. `r0` is still 3, but `rxcnt[17]` stays 0. An `r0`-only check misses it.
- Treat slot 20 as `PSEUDO_MAP_IDX` with immediate 0. That is a different encoding (`src=5`). It happens to name the only map today. It is not what `.relxdp1` says.
- Drop slot 100, or run `eval_end` with `Archi.big_endian = true`. `swab16` of the low half changes the stored checksum. Concrete witness on the register alone: low 16 bits `0xabcd` become `0xcdab` under the `swab16` definition that was read (`i0` bits 0..7, `i1` bits 8..15, insert `i0` at bit 8). Identity or "zero-extend only" leaves `0xabcd`.
- Bswap the ethertype load, or bswap the `daddr` store. The immediates are already in host order (`8`) and network order (`0x4d7100cb`).
- Give the helper the `CallInternal` rule (`exec_call_internal` allocates a new stack and jumps by the immediate). Imm 1 is not a PC displacement.

## Gaps that set the status

1. `decode_ebpf` rejects the first memory opcode and also rejects LDDW, `call`, and `be16`. The section is not an input to `lift_ebpf`.
2. The raw LDDW immediate is 0. The map is only `R_BPF_64_64` against `rxcnt`. No code that was read applies that relocation.
3. Helper id 1 has no definition, and `exec_instr` is `Stuck` on `CallByStaticID`.
4. Packet stores and packet loads are not the same pointer case in `exec_store` / `exec_load`, and the C++ lifter has neither.
5. Checksum `be16` is `Archi.big_endian`-dependent. The object was built for little endian.

STATUS: ISSUES
