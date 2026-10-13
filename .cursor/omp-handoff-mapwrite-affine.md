# Handoff → omp (MapWrite / affineAddress / just_tx)

**Branch:** `agent/cursor-mapwrite-emit` (HEAD was `0bd62cc` when Cursor last checked `.git/HEAD`).
**Repo:** `/Volumes/SSD/bs/classifier`
**From:** Cursor harness (tooling-only). Lean/`doc/` changes below were made out of Cursor freeze — please review and own.

**Status:** landed in `49a7776`; kept as the tooling-side record.

## Ask omp (dispatcher → `spec-author`)

1. **Review** Cursor’s Lean patch in `RV32IMC/Expr.lean`: peel `id32` in `affineAddress` (mirror `lookupAddress`), plus `#guard`.
2. Confirm it is the right fix for lookup key freeze via `readStackBytes` when helper args keep `id32(add32(sp,-16))`.
3. Align `doc/` if MapWrite / stack freeze prose needs the `id` peel invariant.
4. Do **not** edit `tooling/` (Cursor owns it). Leave commits to the operator.

## Why this patch exists

- `just_tx.c` (`libbpf-mcu/tests/xdp/just_tx.c`): `bpf_map_lookup_elem(&rxcnt, &ipproto)` then `*value += 1`.
- Fixture ELF `tooling/fixtures/just_tx.elf`: map @ `0x403802e8`, key 4, value 8; after lookup, LW/ADDI/SW lo + carry SW hi (u64 += 1).
- Freeze path: `Helper.freezeLookupArgs` → `readStackBytes` → `affineAddress`. Without peeling `.id`, stack key bytes never freeze → MapWrite SW hits `UndefinedSrc`.
- After peel + Meta.maps from ELF: expand emits `helper`(lookup+frozen keys), `mapWrite`, `packetWrite`, `ret`, `branch`. Measured (Cursor, not committed as Lean proof):
  - budget 512: LimitExceeded, nodes=549, exits=17, mapWrite present
  - budget 1024: complete, fuel=187, nodes=882, exits=45, map_exit=21, reuse=0

## Cursor tooling status (do not touch from omp)

- `tooling/server`: Meta.maps wired via `with_maps(program.maps)`; just_tx expand assertions updated (512→549 nodes / 1024→fuel 187, 882 nodes); dump test removed.
- Cursor verified (2026-10-13): `lake build RV32IMC`; `cargo test -p server just_tx` (2 ok); `cargo test -p lean-binding --test helper_calls` (15 ok).

## Review checklist for omp

- [ ] `affineAddress` id peel sound / documented
- [ ] MapWrite observation vs dual SW (offset 0 and 4) matches value_size=8
- [ ] Frozen key bytes vs ARRAY u32 ipproto / packet extracts
- [ ] Any `#guard` / Expand unit tests for freeze+MapWrite still green (`lake build` / Lean tests)
- [ ] Doc sync under `doc/Predicate/MapWrite谓词.md` (and related) if needed
