# Classifier repository guide for AI agents

Host-side classifier for BPF and RV32IMC XDP programs. The active pipeline is
**prefixgen** then **pathgen**: extract partitioned machine code from ELF →
structured `Insn = (machine, Prefix)` → expand forward `IfGoto` into `Assert`
syntax paths (`docs/SMT/` T0). Stack normalization, pruning, SMT, and
cross-ISA equivalence are not the current task.

## Working conventions

- Use concise prose or lists, not tables, when writing Markdown plans for this user.
- Ground implementation details in the checked-out source and tests. Target IR and
  solver boundaries live in `docs/SMT/`; historical T0–T5 stage prose remains under
  `docs/Theorem/`. Distinguish intended behavior from implemented behavior when they differ.
- Keep changes scoped to the requested task. Preserve existing user changes under
  `config/` and `example/`; do not treat those locked inputs as disposable.
- Rocq models the predicate IR, prefixgen machine-preservation, and pathgen
expand obligations; it does not verify the Rust implementation. Do not
describe `Parameter`/`Axiom` or `Admitted` statements as completed proofs.

## Layout

```text
src/lib.rs          public API
src/main.rs         CLI (`bpf` / `rv32`; bare run = prefixgen + pathgen → out/)
src/predicate/      Insn / Prefix / Predicate IR + canonical printer
src/prefixgen/      ELF extract + decode → Insn
src/pathgen/        Insn → Path (IfGoto → Assert); task name `pathgen`
src/emit.rs         out/<arch>/prefixgen/ and pathgen/
src/load.rs         legacy toml asm helper
src/rv32/           decode / lower / environment (used by RV prefixgen)
src/bpf/            legacy string T0–T5 (not the CLI default)
rocq/               Predicate / Raw / Prefixgen theories
docs/SMT/           predicate IR + solver design
docs/Theorem/       historical stage specs
example/bpf.o       default BPF relocatable input (section `xdp*`)
example/just_tx.elf default RV32 xpost ELF (section `.xpost.image`)
example/            fixtures (elf / object)
config/             esp32c3.environment.toml
tests/              integration checks
```

## Active pipeline: prefixgen → pathgen

```text
BPF:  example/bpf.o → extract u64 words (xdp*) → decode → Insn → Paths
RV32: example/just_tx.elf → extract .xpost.image → split/lower → Insn → Paths
     → out/<arch>/prefixgen/prog.txt
     → out/<arch>/pathgen/{code}.txt
```

- Relocations in `bpf.o` are **not** applied; unresolved map `lddw` immediates stay 0
  in both `machine` and Prefix (explicit zeros, not silent drops of the reloc record).
- Machine hex is little-endian **memory order** (matches `objdump` byte listing).
- Pathgen replaces forward `IfGoto` with `assert (…) == true|false` on the same
  index/machine; backward `IfGoto` kept; BPF vs RV32 `Goto` rules differ (see
  `docs/Theorem/*/t0.md`). No SMT pruning.
- Path file names are Huffman-style branch codes (not ordinal indices): start at
  `0`; each forward conditional appends `1` (taken) or `0` (fallthrough). Example:
  `0.txt`, `01.txt`, `00.txt`, `011.txt`. Goto / backward if do not change the code.

Output layout:

```text
out/
  bpf/prefixgen/prog.txt
  bpf/pathgen/0.txt | 01.txt | 00.txt | …
  rv32imc/prefixgen/prog.txt
  rv32imc/pathgen/…
```

Each line: `<index>: <machine>, <prefix>` (`<index>` right-aligned to the program's max index width)

- **rv32imc** `<machine>`: width 8; compressed = 4 hex + 4 spaces
- **bpf** `<machine>`: 16 hex digits per `u64` slot
- `<prefix>`: BPF-asm-style predicates; immediates use `0x` with leading zeros
  stripped (`0x1`), so patterns like `0xfffffff0` stay full-width naturally.

Task names are `prefixgen` and `pathgen`. Do not introduce new runtime `t0`/`t1`
task names.

## Deferred

- stack `wsN`, prune, solver, equiv
- applying BPF map relocations into immediates

## Build & run

```bash
cargo test
cargo run              # example/just_tx.elf then example/bpf.o → out/
cargo run -- rv32
cargo run -- bpf
make -C rocq
```

## Rocq proof boundary

Rocq **models the Rust pipeline**, not a freestanding ISA spec. Stay
behaviorally consistent with the checked-out Rust (`src/`); expand Rocq
decode/lower only as far as Rust’s prefixgen path actually exercises
(e.g. just_tx IMC forms). Full ISA coverage is out of scope.

**Rocq input starts after instruction partitioning.** Executable theories
take already-split raw words (`BpfRawProgram` / `Rv32RawProgram` in
`Raw.v`), not ELF bytes or a flat image. ELF extract and RV byte-stream
split stay `Parameter` in `Extract.v`; fixtures mirror the machine column
of `out/<arch>/prefixgen/prog.txt`.

Sources in `rocq/theories/`; build artifacts in `rocq/build/` (not beside `.v`).

| Rust | Rocq |
|------|------|
| `src/predicate/` | `Predicate.v` |
| `prefixgen/extract.rs` | `prefixgen/Extract.v` |
| `prefixgen/bpf_decode.rs` + `rv32.rs` | `prefixgen/Base.v` (`Module Bpf` / `Module Rv32`) |
| `prefixgen/mod.rs` | `prefixgen/Prefixgen.v` |
| `src/pathgen/` | `pathgen/Base.v` / `pathgen/Pathgen.v` |

BPF and RV32IMC machine-preservation are proved from `Base.Bpf` /
`Base.Rv32`. Pathgen proves path `machine` preservation (under unique
indices) and Huffman codes starting with `0`; no full path-family restore
or prune proofs in tree.
