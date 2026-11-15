# Concrete step check

This checks three eBPF programs against the Rocq semantics in `upstream/`. It does not prove the lifter. It compares one concrete input at a time.

The semantics commit is `78d65a77592aae84b31f86385f8be4ab83b45ccb`, recorded in `PIN`. The theories are unmodified. Build them with Coq 8.19.0, OCaml 4.14.2, and CompCert 3.15 from the opam switch `linux-ebpf`.

```sh
cmake --build alive2/build --target ebpf-concrete
./alive2/build/ebpf-concrete --out /tmp/ebpf-concrete
```

A good run prints five `comparator=PASS` rows and one `FAIL` row, `pc 1 status alive2=UB rocq=NEXT`, then `suite=PASS`. The process exits 0. Each row writes `rocq.trace.json` and `alive2.trace.json`.

`r0` through `r9` are compared when both sides hold a 64-bit value. `UNDEF` is not treated as zero. `r10` is not in the file. The Rocq initial state leaves `r10` as a stack pointer. The lifter leaves an omitted register as zero. Memory stays empty on these programs. Fuel running out is `INCOMPLETE`, not a pass.

The negative row lifts DIV64 with `LiftBug::DivZeroAsUb`. The default guard in the lifter stays in place.

## Symbolic check

`ebpf-exhibit --check` is a different claim from the concrete suite. It reads per-instruction expressions from Alive2 `sym_exec` and compares them with a projection of `eval_alu64`, `eval_div_u64`, and `exec_jmpcmp`. That projection is not native Rocq symbolic execution. The supported opcodes are MOV64, ADD64, SUB64, DIV64, JGT64, JA, and EXIT. Anything else is `UNSUPPORTED`, which is not a pass.

On this path an unseeded r0 or r2–r9 is undef, not zero. Unseeded r1 and r10 stay pointers and are not compared as bitvectors. `execute_ebpf` and the concrete suite still use the zero init. `EQUIVALENT` means the inequality is unsat assuming each named input is not undef and not poison. The divide-by-zero mutation is `COUNTEREXAMPLE`.

```sh
cmake --build alive2/build --target ebpf-exhibit
./alive2/build/ebpf-exhibit --check
alive2/exhibit/regen.sh
```

`alive2/exhibit/regen.sh` rewrites `alive2/exhibit/EXHIBIT.md` from the JSON result. Concrete steps in that page are a sanity section. They are not the symbolic path condition.

