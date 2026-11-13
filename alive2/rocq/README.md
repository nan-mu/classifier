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
