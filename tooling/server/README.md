# Server

[项目入口](../../README.md) · [文档索引](../../doc/README.md)

The server accepts xpost Compact ELF V0 containers. `xpost-elf` validates the
container and image digest, then supplies the image range, `slot_address`, and
`helper_address`. RV32 execution starts at the image's first instruction.
`slot_address` is the actual code base; the format's zero `e_entry` is not used.

Lean produces the graph, register expressions, and predicates through
`lean_rv32_expand_bound_words_snapshot`. Rust owns session identifiers, replay
step counts, focus, logs, and instruction text. The server depends on the sibling
`../../../xpost/xpost-elf` checkout and its `xpost-macros` dependency.

The default `tooling/fixtures/just_tx.elf` is a copy of
`/Volumes/SSD/bs/build/just_tx/just_tx.elf`. Its image base is `0x40380200` and
its dispatcher address is `0x40380000`. With budget 512 the current analysis
fails with `UndefinedSrc` after substantial expansion. The firewall fixture
`tooling/fixtures/xdp.elf` remains available for helper-completion regressions.

## Run

From the repository root:

```bash
lake run dev
```

To run only the server from the repository root:

```bash
lake build server
lake env cargo run --manifest-path tooling/Cargo.toml -p server
```

The process listens on `http://127.0.0.1:8788` by default. Set `PORT` to override.

## Routes

`POST /api/session` accepts:

```json
{
  "arch": "rv32imc",
  "budget": 512,
  "name": "just_tx.elf",
  "image_b64": null
}
```

- `arch` is currently only `rv32imc` (alias `esp32c3` accepted). Default `rv32imc`.
- `budget` defaults to 512.
- `name` is a display label; default `just_tx.elf`.
- `image_b64` contains a base64 Compact XDP ELF. Omitted, null, or an empty
  string uses `tooling/fixtures/just_tx.elf`. Decoded uploads must be nonempty and
  at most 256 KiB.

Malformed profiles, truncated containers, invalid image digests, trailing
bytes, raw BIN files, and empty instruction prefixes return HTTP 400. The server
also rejects overflowing RV32 image extents and conflicting helper or wrapper
bindings. The analysis uses the synthetic wrapper return address `0x2000`;
this address is not read from the ELF.

`POST /api/session/<id>/step` advances the Lean step counter by one and refreshes.

`POST /api/session/<id>/run` steps until status is `complete` or `fail` (cap `budget+1`).

`GET /api/session/<id>` returns the current snapshot.

## Helper effects

Lean intercepts calls to the ELF's exact dispatcher address. Supported call
forms are JAL with `rd=ra`, C.JAL, JALR with `rd=ra`, and C.JALR. It preserves
the call's link-register update and resumes at the next instruction. Tail jumps
and unrelated external targets remain failures.

The dispatcher receives the helper ID in `a0` and arguments in `a1` through
`a5`. IDs 1, 2, 3, 5, 6, 28, and 65 produce per-invocation opaque return
expressions in `a0`. Checksum results retain their 16-bit range. Other concrete
IDs return `0xffffffff`, matching the firmware's unsupported-helper fallback.
Symbolic helper IDs are not supported.

The helper value projection currently writes only `a0` (plus the lookup Map-word
binding). Other registers, including caller-saved ones and the bound `data_end`
field, retain their pre-call bindings; full caller-saved and resource-effect
contracts remain unfinished. Context loads use the fixed entry context identity,
so a helper return value cannot become the context pointer.

Lean emits a typed `helper` Predicate on each summarized call. The snapshot JSON
carries `kind`, `event` (dynamic source-node identity), `helperId`, and `args`
(term strings). Lookup also introduces `map32:α = regVar{event}(real32:10)` for
the first Map word. Map memory beyond that word, pointed buffers, helper safety
obligations, and complete helper correctness remain outside this slice. A program
that dereferences a map lookup result can still fail at that later access.

## Image and regression limits

Instruction text uses `riscv-isa` to decode a mixed 2-byte and 4-byte prefix of
the extracted image. The current decoder stops at the first `GPL\0` marker or
undecodable instruction. This is a prefix heuristic, not an ELF executable-section
proof. Container parsing and helper binding use `xpost-elf` independently.

`tooling/fixtures/esp32c3.bin` supplies the generated
`RV32IMC/Esp32c3Program.lean`. Its analysis now rejects the symbolic packet offset
at position 25 before the queued out-of-image jump at position 36. It remains a
partial-graph rejection regression. Regenerate those words with:

```bash
UPDATE_ESP32C3_LEAN=1 lake env cargo test --manifest-path tooling/Cargo.toml -p server lean_words
```
