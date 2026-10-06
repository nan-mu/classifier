# Classifier Rocq proofs (prefixgen + pathgen)

Sources live under `theories/`; compiled artifacts go to `build/theories/`
(`make` uses `rocq c -o …`). Do not commit `build/`.

## Layout

```text
theories/
  Predicate.v           shared IR + Module Tests
  Raw.v                 raw programs + Module Tests
  prefixgen/
    Extract.v           ELF extract interface
    Base.v              Module Bpf | Module Rv32 (concrete decode);
                        Tests from out/*/prefixgen/prog.txt
    Prefixgen.v         facade + Module Tests
  pathgen/
    Base.v              expand IfGoto→Assert + machine/code theorems
    Pathgen.v           facade
  Theorems.v
build/theories/         .vo / .glob (generated)
```

Unit tests live next to the code as `Module Tests` with **input → output**
`Example`s. BPF/RV fixtures and expected Prefix values are taken from
`out/<arch>/prefixgen/prog.txt` (regenerate lists via `gen_rv32_base.py`).

| Rust | Rocq |
|------|------|
| `src/predicate/` | `Predicate.v` |
| `prefixgen/extract.rs` | `prefixgen/Extract.v` |
| `prefixgen/bpf_decode.rs` | `prefixgen/Base.v` → `Module Bpf` |
| `prefixgen/rv32.rs` | `prefixgen/Base.v` → `Module Rv32` |
| `prefixgen/mod.rs` | `prefixgen/Prefixgen.v` |
| `src/pathgen/` | `pathgen/Base.v` + `pathgen/Pathgen.v` |

## Build

```bash
make -C rocq          # writes build/theories/**
make -C rocq clean    # removes build/ and stray in-tree .vo
```

## Status

- `Base.Bpf`: executable word→Prefix + machine-preservation proof
- `Base.Rv32`: IMC decode used by just_tx fixtures
- `Extract`: parametric (host ELF outside TCB)
- `Pathgen`: fuel-bounded expand; `pathgen_preserves_machines` /
  `pathgen_codes_start_with_zero` (no path-family restore / prune)
