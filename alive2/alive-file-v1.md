# Alive file v1

A `.alive` file contains one program in text form. The loader reconstructs the pinned Alive2 `Function`, `BasicBlock`, and `Instr` objects. It does not use an LLVM frontend or a source-to-target transform. Origin metadata and evidence reports are separate files.

## Header and module

Every file requires these exact lines before its declarations and definition:

```text
; alive-file v1
; alive2-pin adacbd5180ccf95075e9867c4f0c259f59c9fef2
; rocq-pin 78d65a77592aae84b31f86385f8be4ab83b45ccb
```

Other `;` comments and blank lines are ignored. Unsupported versions and mismatched pins are errors. The body contains optional declarations followed by exactly one definition and its closing brace. Globals, multiple definitions, varargs, and content after the definition are unsupported.

```text
declare ptr bpf_map_lookup_elem(ptr, ptr) memory(argmem: read, inaccessiblemem: readwrite)
define i64 @example(ptr %ctx, ptr %pkt, i64 %pkt_base) memory(argmem: readwrite, inaccessiblemem: readwrite) {
entry:
  %a = add i64 1, 2
  ret i64 %a
}
```

Declaration and call names may have a leading `@`. The pinned printers omit it for these names. The definition name requires `@`; SSA inputs and results require `%`. Block labels omit `%`, while references retain it. Commas, parentheses, and whitespace separate tokens. `--normalize` writes the exact header followed by the pinned `Function::print` output.

Memory attributes are required on declarations and definitions. Supported locations are `argmem`, `globals`, `inaccessiblemem`, `errno`, and `other`; modes are `read`, `write`, and `readwrite`. The aggregate forms `memory(none)`, `memory(read)`, and `memory(write)` are supported. Calls inherit their declaration attributes. An explicit call memory attribute must match the declaration, so printing and reading preserve effects.

## Instruction subset

Types are `i1`, `i8`, `i16`, `i32`, `i64`, and address-space-zero `ptr`. Constants are decimal integers. Result types, operand types, conversion widths, and literal ranges are checked.

| Form | Accepted spelling |
| --- | --- |
| Integer arithmetic | `%r = add i64 %a, %b`; `sub`, `mul`, `udiv`, `sdiv`, `urem`, `srem`, `shl`, `lshr`, `ashr`, `and`, `or`, `xor` |
| Integer comparison | `%c = icmp ult i64 %a, %b`; also `eq`, `ne`, signed and unsigned `lt`, `le`, `gt`, `ge` |
| Integer conversion | `%r = trunc i64 %a to i32`; `zext`, `sext` |
| Pointer conversion | `%r = ptrtoint ptr %p to i64` |
| Allocation | `%stack = alloca i64 512, align 8` |
| Pointer offset | `%p = gep ptr %base, 1 x i64 %offset` |
| Load | `%r = load i32, ptr %p, align 4` |
| Store | `store i32 %r, ptr %p, align 4` |
| Phi | `%r = phi i64 [ %a, %left ], [ %b, %right ]` |
| Branch | `br label %next`; `br i1 %c, label %yes, label %no` |
| Return | `ret i64 %r` |
| Declared call | `%r = call ptr bpf_map_lookup_elem(ptr %map, ptr %key)` |

The loader rejects unsupported opcodes and flags. Alignments must be nonzero powers of two. Branch conditions must be `i1`; memory addresses must be pointers. A declared call must match its return type, argument count, and argument types. Void calls and void returns are unsupported.

Blocks must be reachable and terminate with `br` or `ret`. The entry block has no predecessors. Duplicate definitions, duplicate labels, unresolved names, instructions after terminators, and phis after ordinary instructions are errors. Phi incoming labels must match the actual predecessor set exactly. Values must dominate their uses, including uses on phi incoming edges. Non-phi operands are resolved in source order; forward value references are supported only by phis. Instruction diagnostics include the source line; module-level checks identify the failed invariant.

The pinned printers are in `third_party/alive2/ir/function.cpp` and `third_party/alive2/ir/instr.cpp`. The file subset deliberately excludes other forms those printers can produce.

## Compiler representation

The Rust compiler preserves source loops as CFG backedges. It masks shift counts and lowers division and remainder corner cases into explicit branches and phis. Extra division blocks use their actual outgoing labels in later phi inputs.

Register facts distinguish scalar integers, context pointers, packet addresses, stack pointers, map handles, and map-value pointers. Packet addresses have an integer representation tied to `%pkt_base`; ordinary scalar integers cannot be dereferenced as packets. Stack pointer spills retain their kind and known offset. Partial or incompatible pointer-slot reloads are rejected. Unsupported function ranges, ambiguous entries, relocation kinds, and pointer flows fail conversion.

The current context layout assumes the XDP data/data_end fields at offsets 0 and 4. Helper lookup is represented by a declared external call with memory effects. These choices need source-to-target relation proofs. Successful parsing and execution do not establish that relation.

## Commands and evidence

```sh
cargo build --manifest-path tooling/Cargo.toml -p ebpf-to-alive2
cmake --build alive2/build --target alive2-load -j8

tooling/target/debug/ebpf-to-alive2 compile INPUT.o \
  --out OUTPUT.alive --origin OUTPUT.origin.json --report compile-report.toml

tooling/target/debug/ebpf-to-alive2 compile-corpus \
  --index alive2/corpus/snapshot.toml --out-dir /path/outside/input-tree

alive2/build/alive2-load --inspect OUTPUT.alive
alive2/build/alive2-load --normalize OUTPUT.alive
alive2/build/alive2-load --smoke OUTPUT.alive
alive2/build/alive2-load --smoke LOOP.alive --unroll 1
alive2/build/alive2-load --self-test
```

`--inspect` reports instruction kinds, types, operands, branch targets, and the pinned instruction text, including predicates, offsets, alignments, callee names, phi edges, and memory effects. `--smoke` calls the existing upstream symbolic executor. It uses a local memory-size configuration derived from the loaded function. Cyclic CFGs require an explicit positive unroll bound, passed to the existing upstream unroller. Smoke completion checks construction of a symbolic return state; it neither solves equivalence nor proves source safety or termination.

The compiler checks the snapshot's input SHA-256 and size. It stages the three outputs, publishes `.alive` and origin, and renames the conversion report last. A caught failure removes that invocation's outputs. Batch conversion writes `corpus-outputs.json` with the program names it owns. On subsequent runs it removes those programs' old completion reports before parsing the manifest, and removes their `.alive` and origin files if a valid manifest no longer includes them. It preserves unrelated files. The index and raw input files must be outside the output directory. Directories unlisted in both the manifest and the ownership file are not swept. The report is the completion marker; publication is not a crash-safe multi-file transaction. Concurrent writers to the same output paths are unsupported.

Origin schema v1 records ELF and Alive hashes, selected function/section, raw instruction bytes, source slots, and the actual generated SSA definitions. Block-entry phi definitions are attached to the first source instruction in that block; target setup definitions are listed separately in `prologue_ir`. Tests check complete definition coverage in both directions. Branch instructions and complete LDDW pairs are included. IR loading has no dependency on origin. Full R0–R10/RAX/PC/stack/code-id/tail-call checkpoint expressions and a source-view consumer remain incomplete. The loader has no source-view mode, so it cannot validate or present those mappings yet.

`compile-report.toml` says `status = "converted"` and `implementation_proof = "not_proven"`. The snapshot records 17 observed raw BPF objects. The Task A `index.toml` is unavailable; the snapshot does not fulfill that upstream manifest contract. `profile.toml` explicitly selects `legacy-dual-arch`, retaining the old page's interpretation of native ELF/BPF outcomes. Raw BPF conversion reports have a separate contract and are not interpreted as those legacy outcomes.

Run the reproducible file integration gate with Python 3.11 or newer:

```sh
python3 alive2/tests/run-rust-file-e2e.py \
  --compiler tooling/target/debug/ebpf-to-alive2 \
  --loader alive2/build/alive2-load \
  --index alive2/corpus/snapshot.toml \
  --out-dir /path/outside/input-tree
```

It compiles and reads all 17 programs in a separate loader process, checks parser/printer self-consistency after normalization (including declaration input types), recorded hashes, origin definition coverage, and IR loading independent of origin. It runs three symbolic-execution smoke cases, including `helper_loop` with unroll 1 and rejection of that loop without an explicit bound. The round trip uses the same loader and pinned printer; it is not an independent semantic oracle. Its `verification.json` is test evidence and an artifact index. It records implementation and artifact proofs as `not_proven`. The older C++/Rocq checks do not prove this Rust implementation. The PR remains Draft until the actual implementation connection and remaining contract gaps are resolved.
