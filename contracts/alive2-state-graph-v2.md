# Native State graph protocol (v2)

This protocol is implemented by `alive2-explore` in PR8. It does not come from an earlier design attachment. The JSON Schema and `validate_state_graph.py` describe the serialized shape and relational checks respectively. The Python validator still reads v1 graphs.

## Execution and snapshots

The executable shares `alive_file.cpp` with `alive2-load`. There is one alive-file parser and verifier. The Loader's self-test, inspect, normalize, smoke, strict pins, attributes, helper signatures, Phi and dominance checks remain in use.

Execution uses Alive2's `sym_exec_init`, `Function::unroll`, `topSort`, `State::startBB` and `State::exec`. There is no second interpreter or unroller. This is an observer of native *merged symbolic State*, not a separate path-enumerating executor. Native predecessor alternatives, Phi expressions and domains remain in the expression DAG. The observer does not coalesce instruction snapshots.

Each ordinary node is the native State after one executed IR instruction. The initial node is after native input/constant/initializer setup. A boundary node copies the actual native predecessor snapshot with its native jump guard; it is tagged `snapshot_kind: native_predecessor_at_boundary`. It does not claim that an instruction executed in the empty `#sink` block. Separate boundary predecessors get separate nodes. Native loop clone names and their numeric `#N` suffixes are retained as block and unroll fields. Native bookkeeping blocks such as `#exit` have no numeric clone suffix.

`ir_state.values` contains the native cache entries available at that point, including each entry's type, non-poison condition and execution domain. An entry from another predecessor is not an assertion that its definition dominates every current path: use its domain. `current_value` is the executed instruction's native value; void instructions have an explicitly unsupported/no-value term. The initial and boundary nodes have no value-producing instruction.

`returned_values` and `memories[].returned` retain native disjoint return accumulators, including each alternative's domain. They are cumulative at that observation point. They are **not** restricted to the most recent return instruction. Calling `returnVal()` or `returnMemory()` during the walk would finalize these accumulators and prevent later native returns; the observer instead reads them without mutation.

## Conditions and edges

- `path_condition` is `State::getPath(bb)`: the accumulated native predecessor path, including native predecessor merges.
- `definedness` is the executed instruction's recorded native domain, separately from path reachability.
- `preconditions`, `axioms` and `call_preconditions` retain the native constraints. A consumer must not interpret a value or path independently of these constraints and non-poison conditions.
- CFG guards are captured from `State::getJumpCond(src,dst)` immediately after the native Branch executes. `guard_scope: native_predecessor_path_and_ub` identifies this accumulated guard. It is **not** merely the branch's local comparison. A separate local Bool guard is not currently exported.
- Within-block step edges are unconditional observation links. Unconditional CFG inputs to a native join are tagged `merge`; conditional inputs retain `taken`/`not_taken`.
- Only syntactically false native jumps are omitted. There is no SMT feasibility query and no proof of infeasibility for remaining paths.
- `ir_span` references observed source/destination instruction IDs. `changed` lists cache bindings, memory and conditions that actually differ between the two exported snapshots.
- `events_status: not_observed` means the empty events array does not establish that no source ISA or external event occurred.

Normal return, native unroll sink and instruction-budget exhaustion are distinct. Coverage lists return observations, sink observations and a frontier. Resource truncation also records unobserved targets as assumptions; it is not a complete source-machine scheduler frontier. `all_inputs_covered` remains `not_established`. Completion of the finite walk is not input-space coverage.

## Typed expression DAG and memory

Terms are read from the native Z3 AST, with Bool, bitvector and array sorts, recursive argument references, numerals, symbols and declaration parameters. Quantifiers/lambdas retain their body and bound-sort parameters; bound variables use de Bruijn indices. Structural interning includes complete sort and width. Native AST references are retained while IDs are cached. Z3's native declaration spelling is preserved, e.g. `if` for ITE. Rewrites such as subtraction to addition or masks to extracts are native simplifications.

IDs are deterministic for repeat runs with the same artifacts, configuration, pins and native library versions. They are not cross-version semantic equivalence IDs. Display strings are not the representation: recursively printing every native subexpression caused exponential expansion on real programs. Unsupported sorts/AST parameters have an explicit reason and native identity rather than pretending to be an opaque but complete DAG.

Memory uses `representation: alive2-native-arrays`. Each materialized block retains its local/nonlocal identity, native byte encoding, array (or native compact bitvector), undef terms, size, alignment, alive/writable and allocation-type terms. Return alternatives retain their separate blocks. Empty active arrays after a return do not discard returned memory. This is native Alive2 memory, **not** a CompCert byte-memory embedding. It is not a serialization of all private allocator, alias-analysis or native solver bookkeeping.

## Initial and environment inputs

Every function input must have exactly one explicit binding. Unknown, duplicate, missing, mistyped or malformed bindings fail before graph publication. No missing input is defaulted to zero.

```json
{"inputs":[
  {"name":"%x","type":"i64","kind":"concrete","value":"7"},
  {"name":"%p","type":"ptr","kind":"symbolic"}
]}
```

Bindings support `concrete` integers through 64 bits (decimal strings, checked width), `symbolic`, `undefined`, and `poison`. Symbolic denotes a stable, defined native input: Alive2's native disable-undef/disable-poison input configuration is enabled. Explicit undef/poison bindings remain native UndefValue/PoisonValue constants. Concrete values specialize uses with native `Function::rauw`; all arithmetic still runs in Alive2.

Symbolic pointer inputs are supported. Concrete pointer/object binding, initialized input-memory objects, map contents and an explicit `--environment` file are **unsupported and rejected**. No memory is implicitly initialized to zero. The generic native function declaration contract is not a fixed concrete helper implementation. An experiment replacing a pointer input by a global object returned the expected byte while its definedness was false: replacing the pointer changed argmem ownership. That approach was rejected rather than weakening memory attributes. A correct initializer must preserve input-object identity and native memory ownership; it remains work to do.

## Origin and Rocq boundary

`--origin` accepts existing `classifier-alive-origin-v1` files and verifies their Alive2 digest. The optional `register-bindings-v1` extension adds original decoded instructions, before/after R0–R10 static bindings, generated IR and Phi source information. Existing fields remain intact. Bindings are metadata from the Rust lifter, not a dynamic eBPF execution.

The observer maps exact declared SSA definitions and uniquely matching compiler-recorded IR statements; ambiguous or cloned/unmapped definitions remain unmapped. It never guesses a register from an SSA name. The source ELF digest is a declaration in Origin: the CLI does not require an ELF and cannot independently verify that declaration. The graph retains the complete Origin metadata and its file digest.

Full checkpoint embedding is **not implemented**. RAX, source PC embedding, stack frames, code_id, tail_call_count, source memory and events remain explicitly unmapped. All exported `rocq_ebpf` fields are null with an unsupported reason. There is no full concrete correspondence result and no full Rocq state example in this delivery.

The existing independent Rocq executable builds from the pinned ISA and runs its own `exec_instr`. Its current driver exports R0–R9, a memory-effect summary and a limited trace. It supplies an empty stack/None code_id/zero tail count on each step instead of threading complete TLS_State; it cannot serve as the full-state oracle required by this task. Its DIV64 self-check is reported separately and is not PR8 source-state correspondence.

The observer, serializer, checkpoint metadata and native observation accessors are implementation trust boundaries. The pin identifies the upstream semantics; local read-only accessor additions are disclosed in the diff. There are no new axioms or Admitted declarations. No model, artifact, implementation or symbolic-correspondence proof is claimed.
