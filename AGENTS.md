# Classifier repository guide for AI agents

## Architecture

The project is a Lean-based symbolic program-analysis prototype with a Rust
API and a web graph viewer. Its mathematical specification is broader than its
current executable instruction coverage. Do not describe it as a complete ISA
interpreter or a verified cross-ISA equivalence checker.

`CommonMath` owns architecture-independent registers, numeric operations,
terms, expression sets, predicates, semantic states, paths, budgeted expansion,
history structures, rendering, and shared FFI exports. Read
`doc/common-math.md`, `doc/registers.md`, and the relevant source before changing
shared math. Executable `RegKind` contains real, stack, map, and packet.
Packet identities pair a resource namespace with a canonical byte offset; each
byte uses a 32-bit term. `CommonMath/Virtual.lean` owns resolved Stack/Map field
accesses and 32/64-bit Packet assembly/splitting. Address classification remains
in the ISA layer; a resolved Map cell does not establish an ELF Map binding.

`RV32IMC` and `EBPF` are ISA layers that reuse `CommonMath.Reg`, `Term`,
`ExprSet`, `SemState`, and expansion. Keep shared math and register ADTs in
`CommonMath`. Do not add Sail execute stubs to `RV32IMC`.

In RV32, `encode` / `encodeCompressed` decode bits into `Insn`, despite their
names. `expr` / `step` produce local updates, not a complete successor state.
The ISA expansion adapter binds control-flow targets and supplies candidates
to the shared expansion engine. Rust manages sessions and presents Lean
snapshots; it must not become a second implementation of instruction semantics.

## Semantic invariants

- `SemState` contains expressions and predicates. Static program layout and
  wrapper return bindings belong to the ISA step closure.
- `ExprEffect.inputs` materializes untouched Packet bytes and later Map words;
  `updates` contains instruction writes. RV32 `expr` returns writes, while `step`
  transports both in a delta. Previously written bytes and words must never
  revert to their input content.
- Expression keys are `(Reg, Rel)`. Apply a local update by replacing the
  matching global keys, preserving other bindings. Validate key uniqueness;
  the list-backed representation does not enforce it by construction.
- A node at a program position contains the state before its instruction.
  An Exit node contains the resulting state and return observation.
- Every candidate arrival creates a fresh node. Expansion does not merge
  states at a shared program position or compute a fixed point.
- Concrete RV32 branches choose the feasible side. Symbolic branches retain
  both sides with complementary predicates. Predicate merging removes
  structural duplicates; it does not solve path feasibility or contradictions.
- Prepare all successors before appending any nodes or edges. A rejected step
  preserves the graph and reports failure. An unknown target or missing source
  must not silently become Exit, completion, or an empty successful update.
- Fuel bounds node expansion, not graph size. Exhaustion with pending work is
  failure; an empty work queue is completion, including when fuel is zero.
- `eval` is partial and `solve` only folds evaluable closed terms. Packet-byte
  and external-event operations remain uninterpreted even with closed arguments.
- A helper result is identified by its dynamic source node, not only its
  instruction position or arguments. The private RV32 snapshot runner owns
  this identity; keep shared expansion and `SemState` independent of helpers.
- ELF context loads use the fixed entry context binding, not mutable `a0`.

## Current executable scope

### CommonMath

The shared core provides 32/64-bit numeric terms, expression overwrite,
comparison and return predicates, candidate transitions, and finite-budget
path expansion. History data structures exist, but a full history-analysis
pipeline is not exposed by the current API.

`CommonMath/Term.lean` proves `solve_idempotent` in Lean. Other propositions
and proofs in `doc/` are mathematical prose unless backed by a source theorem.
Compilation guards and runtime tests are examples and regressions, not general
semantic correctness proofs. Do not equate `solve` with an SMT solver.

### RV32IMC

The executable slice includes mixed 16/32-bit decoding, arithmetic and bitwise
updates, direct branches and jumps, bound concrete indirect targets, wrapper
returns, selected context and stack loads, byte/halfword/word stack stores,
subword extraction, Packet byte/halfword/word reads and writes, compressed packet
word accesses, event-local Map byte/halfword/word reads and writes through lookup
return aliases, and ELF-bound helper call summaries. High-half
multiplication and division/remainder currently require evaluable operands.

Packet loads assemble current canonical bytes in little-endian order. Fresh
input bytes remain symbolic; Packet stores overwrite only their addressed bytes.
Constant affine offsets normalize to the same identity across aliases. Symbolic
offsets reject without a unique binding. Known concrete lengths reject overrun;
symbolic bounds, permissions, and machine alignment remain unproved premises.
Stack subword writes preserve the rest of their canonical word and require its
old value; cross-word stack accesses reject. Map accesses require one lookup
return event, its helper-introduced word-zero equality, and a concrete affine
displacement. Each access must fit within a canonical four-byte word and uses
CommonMath CellAccess. Loads write only the real destination. Untouched later
words materialize in `ExprEffect.inputs` as opaque
`externalResult event (1 + wordBase / 4) [C32 1]` content terms. Subword stores
materialize old content before preserving other bits; aligned full-word stores
create or overwrite a word without reading old content. Updates always take
precedence over inputs, so later reads observe current writes. Word zero keeps
the helper's `regVar` convention. Copies and constant add/subtract aliases retain
that identity after a0 changes. Null/numeric pointers, non-lookup returns,
symbolic offsets and cross-word accesses reject. Concrete displacements normalize
modulo 32 bits; no ELF value size is inferred. This event-local association does
not prove lookup success, actual Map contents, ELF value size, or alias consistency
between separate lookups. General heap/ELF Map binding,
complete helper contracts, symbolic indirect-target resolution, and path
constraint solving are unfinished.

`RV32IMC/Helper.lean` follows xpost's dispatcher ABI. It reads helper ID from
`a0`, validates the required argument equalities, and creates a typed helper
Predicate with the dynamic source-node identity and captured arguments. Its
current value projection writes only `a0`; lookup additionally introduces the
first Map-word relation to an event-bound `Term.regVar` of the return register.
Unsupported concrete IDs return max32. Calls
must target the exact ELF dispatcher binding and write `ra`; tail jumps are
not summarized as fallthrough. Preserve the original link update.
`RV32IMC.inferStep` is the public single-step entry for bound helper calls and
ordinary instruction candidates. Full caller-saved-register and resource-effect
contracts, broader Map address classification, and buffer memory semantics remain
unfinished; the return-only projection does not establish resource preservation.

The old raw 48-instruction ESP32-C3 fixture is an unbound analysis regression.
With budget 512 it performs 38 successful expansions and reaches 43 nodes before
failing at position 25 (`UndefinedSrc`): its packet offset depends on a packet
byte and has no unique canonical byte binding. An earlier branch reaches Exit
with return value 2. The queued position 36 `C_JAL` still targets outside the
image (byte offset 104, displacement -616, `UnboundTarget`). Neither extra fuel
nor arbitrary fresh packet names resolve these missing bindings. See
`RV32IMC/Expand.lean` and `tooling/lean-binding/tests/lean_modules.rs`.

The default Compact XDP ELF is `tooling/fixtures/just_tx.elf` (copied from
`/Volumes/SSD/bs/build/just_tx/just_tx.elf`). Its decoded prefix has 79
instructions. The HTTP and WebUI default budget is 1024. With that budget the
bound snapshot completes with 882 nodes, 881 edges and 45 Exits, including 21
carrying lookup-region Map updates. Budget 512 still exhausts fuel after the
Map loads/stores (`LimitExceeded`, 552 nodes, 10 Exits, 30 pending) and remains
a fuel regression. Compressed LW/SW use matching word-offset decoding, so
position 54 updates the same offset-4 word loaded at 49.
The firewall fixture `tooling/fixtures/xdp.elf` is retained for helper-call regressions; full-program
completion additionally requires all resource offsets and accesses to be bound.
Helper-effect unit coverage also lives in
`tooling/lean-binding/tests/helper_calls.rs`.

### EBPF

The executable slice decodes and evaluates MOV and ADD, each in ALU32/ALU64
forms with immediate or register sources, plus outer EXIT. Entry state binds
only `r1` to the context input and `r10` to the stack input. ALU32 results are
zero-extended, `r10` is read-only, and EXIT observes defined `r0`.

Loads/stores, branches, LDDW, calls, atomics, and the broader functions described
in `doc/ebpf-expr-value-functions.md` are not implemented in this slice. There
is no established RV32/eBPF input correspondence or equivalence theorem.
The Rust API and web viewer expose RV32IMC expand over an uploaded Compact XDP
ELF (default `tooling/fixtures/just_tx.elf`). Rust parses it through the sibling
`xpost-elf` crate and passes its `slot_address` and `helper_address` to Lean.
Raw BIN uploads are rejected. The synthetic wrapper return is `0x2000`, not an
ELF field. Check container extent and binding collisions before analysis.
eBPF analysis is not wired through the HTTP session API yet.

Expand graph ownership: Lean exports `lean_rv32_expand_create` for an initial
snapshot String and `lean_rv32_expand_step` for stateless head expansion. Rust
passes the program bindings, dynamic source event, instruction position, fuel,
and expression/predicate JSON arrays; Lean returns already applied successor
states or a rejection. Rust `rv32::ExpandSession` owns all nodes, edges, work,
fuel, and status. No expand object remains in the Lean heap across FFI calls.
Rejected head calls echo input fuel; Rust applies diagnostic work/fuel rules.
All Lean calls serialize on a process mutex. The HTTP server keeps per-session
locks and runs `/step` and `/run` on `spawn_blocking`.
Legacy `expand_bound_words_snapshot(steps, budget)` keeps an ephemeral WorkState
inside one call for regression replay. Builtin fixture replay C export is
`lean_rv32_expand_builtin_snapshot`.

## Documentation policy

`doc/` is for paper readers and must focus on mathematical definitions,
assumptions, expressions, propositions, derivations, and proofs. Keep programming
details, build commands, APIs, FFI, fixture diagnostics, and implementation-status
reports in this guide, source comments, or the root/tooling READMEs.

Use `doc/README.md` as the mathematical reading index. Preserve existing document
filenames. State proof assumptions and distinguish proved results from open proof
obligations. A mathematical specification must not imply executable support or
a Lean formalization that does not exist.

For substantial documentation work, use the project-local
`.agents/skills/doc-coauthoring/SKILL.md`: gather context, rewrite and refine,
then check the result from an independent reader's perspective. Follow the
user's established audience and scope without asking for the same preferences
again. Use concise prose or lists, not tables, for Markdown plans.

## Layout

The repository root is the Lean workspace. Non-Lean tools live in `tooling/`.

```text
CommonMath.lean                 shared math root reexports
CommonMath/                     shared math, states, paths, expansion, rendering, FFI
CommonMath/Parse.lean           JSON term/expr/predicate parsers for head-step FFI
CommonMath/Virtual.lean         resolved cell fields, Packet bytes, input/write effects
RV32IMC.lean                    imports Insn + Encode + Expr + Initial + Expand
RV32IMC/Insn.lean               decoded instructions and field tags
RV32IMC/Encode.lean             encode / encodeCompressed
RV32IMC/Expr.lean               expr / step and FFI smoke exports
RV32IMC/Initial.lean            EntryParams + E0 (real ∪ xdp_md SW slots)
RV32IMC/Helper.lean             helper Predicate generation and result/Map Expr projections
RV32IMC/RegisterFfi.lean        local register-effect probes for binding unit tests
RV32IMC/Expand.lean             inferStep / stateless create·head-step JSON FFI
RV32IMC/Esp32c3Program.lean     generated instruction words for the ESP32-C3 fixture
EBPF.lean                      reexports the executable eBPF slice
EBPF/Insn.lean                 MOV / ADD / EXIT instruction types
EBPF/Encode.lean               strict 8-byte-slot decoding
EBPF/Expr.lean                 local MOV / ADD updates
EBPF/Initial.lean              logical context and stack entry bindings
EBPF/Expand.lean               shared expansion adapter and compilation guards
lakefile.lean, lean-toolchain   Lean package and pinned toolchain
doc/                           mathematical specifications and proofs
.agents/skills/doc-coauthoring/ project-local documentation skill
tooling/Cargo.toml              Rust workspace, with one shared Cargo.lock
tooling/lean-binding/           Rust FFI binding to Lean exports
tooling/lean-binding/tests/     Lean export and snapshot regression tests
tooling/server/                 axum Expand API, instruction text via riscv-isa
tooling/web/                    Vite, Kuma UI, and xyflow canvas
tooling/scripts/dev.py          development service lifecycle, invoked by Lake
tooling/fixtures/just_tx.elf    default Compact XDP ELF (from bs/build/just_tx)
tooling/fixtures/xdp.elf        firewall Compact XDP ELF helper-completion fixture
tooling/fixtures/esp32c3.bin    raw unbound regression and generated Lean words input
tooling/scripts/smoke.py        live API checks and migration snapshot comparison
```

## Build and check

Run these commands from the repository root.

```bash
lake build
lake test
```

Start both services from the repository root.

```bash
lake run dev
```

For local register-effect checks without integration tests:

```bash
lake build CommonMath RV32IMC EBPF
lake env cargo test --manifest-path tooling/Cargo.toml -p lean-binding --lib register_tests
```

`lake build` builds all three Lean shared libraries, the Rust server, and the
web app. Lean `#guard` checks execute when their modules compile.
`lake test` builds the server and web app, runs Rust workspace tests, runs web
Vitest unit checks (`tooling/web`), and runs live API smoke checks against an
isolated server. Its server dependency covers CommonMath and RV32IMC, so run
`lake build` as well when changing EBPF.
`lake run dev` builds the server, installs frontend dependencies, and starts
the API on `8788` (overridable with `PORT`) and Vite on `5173`. The development
supervisor checks ports and cleans up service process groups on shutdown.
Ctrl-C stops both services.
Use Lake as the project entrypoint. Cargo and npm are component build tools.

The server executable path comes from Cargo's artifact output; do not hard-code
`tooling/target/debug/server` in Lake or lifecycle scripts. Keep the single Rust
workspace lockfile. Do not hand-edit `RV32IMC/Esp32c3Program.lean`; regenerate
fixture words using the command documented in `tooling/server/README.md`.
The server requires the adjacent `../xpost/xpost-elf` checkout. Validate ELF
uploads with that library rather than duplicating metadata and digest parsing.

Toolchain is `leanprover/lean4:v4.29.0`. After Lean layout changes, run
**Lean 4: Restart Server** in the editor.

Before reporting completion, inspect `git status` and `git diff`, preserve
pre-existing changes, and run checks appropriate to the edited files. Do not
commit unless asked. `.codex/` contains ignored local working material and
must never be committed.

## Codex model policy

Use only `gpt-6.1-sol` for all agent tasks and subagents, including Codex,
Cursor delegation, and pstack profiles.
Use only `low`, `medium`, or `high` reasoning effort. Keep a lower effort when
suitable. Do not use `xhigh`, `max`, `ultra`, the Fast speed tier, or automatic
model fallback. If the permitted model is unavailable, report the limitation.

Preserve this policy when updating or reinstalling pstack custom-agent profiles.
Change it only when the user explicitly revises it.

## Optional Cursor MCP workflow

This section describes an optional delegation path in Cursor. It does not
require native Codex sessions to invoke MCP or delegate Lean work. Native
Codex sessions may edit Lean and FFI sources and run builds directly under
the architecture and model policies above.

- The model policy above also applies to Cursor delegation. Use an inherited
  model only when it resolves to `gpt-6.1-sol`; do not configure automatic
  selection that can choose another model.
- For Lean work, prefer the Cursor MCP namespace `user-codex-subagent` with
  `gpt-6.1-sol`. This includes Lean sources, Lake configuration, theorem work,
  builds, and FFI that exposes Lean exports.
- Defaults are maintained in `~/.codex/config.toml` and
  `~/.cursor/rules/model-access.mdc`. Do not reset settings to bypass caps.

When using this MCP delegation path:

1. Write a self-contained brief to `.codex/lean-handoff.md`. This directory is
   gitignored. Never commit `.codex/`.
2. Include the absolute repository root and cwd, goal, architecture constraints,
   files to read first, pass/fail checks, and deliverables. Do not commit unless
   asked. Do not include unrelated refactors.
3. Call `user-codex-subagent` → `spawn_agent` with the brief as `prompt`.
   For independent Lean tasks, use `spawn_agents_parallel` with one prompt per
   task. Give each writer separate file ownership.
4. Inspect `git status` and `git diff`, then run the brief's build and test
   checks. Continue from that evidence. Rust, TS, and documentation work can
   proceed independently when it does not depend on unfinished Lean APIs.

If this MCP is unavailable in Cursor, report the limitation and use an available
execution path within the user's authorization and model policy. The file-backed
MCP brief replaces the older copy-paste or operator-reported completion handoff
for this workflow.
