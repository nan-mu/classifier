# Independent review and disposition

Reviewer: fresh read-only `poteto-agent`, requested model `magpie/group/qwen4`, runtime agent `3e4dc1b2-b466-422`, resolved type `poteto-agent`. It rebuilt native libraries and both CLIs in separate external directories, read the actual diff and audit, ran actual graphs and the validator, and reported without editing source. The underlying model vendor was not independently exposed. No final acceptance approval was exercised.

The review confirmed native `State::exec`, read-only cache/return-accumulator observation, one shared parser, preserved native memory/returns, and explicit absence of a full Rocq embedding or proof. It reproduced 15 of the then-recorded 16 graph hashes and found a real determinism defect in the remaining program.

| Finding | Disposition and evidence |
|---|---|
| Native commutative argument ordering made `just_drop` graph hashes vary | Fixed typed structural SHA256 IDs, canonical commutative operands and sorted term table. Repeated complete `just_drop` graph regression passes. |
| Missing returned-memory, merge-kind and boundary-content assertions | Added assertions against actual native output. Boundary values, constraints and memory match its predecessor while location/status differ deliberately. |
| Missing Origin hash/duplicate-slot negatives | Both CLI rejection cases added and pass. |
| Brittle `stoull` diagnostic | Strict `from_chars` parsing and explicit initial-state diagnostic now tested. |
| Server test could use stale v1 binary | `ALIVE2_EXPLORE` selects the fresh executable; integration asserts schema version 2. |
| Blocking HTTP work, leaked directories, unbounded retention, incorrect error status | Execution uses `spawn_blocking`, RAII directory cleanup, retention limit 64 and 422 mapping for unsupported inputs. Local integration and clippy pass. |
| Dead `bb_term` and protocol wording | Removed/fixed. |
| Graph artifacts missing from archive | Actual JSON, inputs, four real IR/Origin bundles and screenshots now archived. SHA256 verification covers every archived graph. |
| Recursive cycle checker, empty corpus endpoint | Remaining limitations documented. |
| Concrete initialized memory, full checkpoint embedding and Rocq correspondence absent | Remain acceptance blockers. No state or proof was fabricated. |

The reviewer's Rust-test total was not adopted: the delivery report uses the main session's directly recorded 37 passing tests. Final authoritative test counts are 34 Explorer cases, 18 validator unit tests, 17 corpus structural round-trips, 3 native smokes, 7 independent compiler-structure fixtures and 1 fresh-v2 HTTP integration. See adjacent logs and reports.

These fixes were checked by rerunning the affected real commands. The review does not turn incomplete requirements into accepted ones. Full concrete Rocq state correspondence remains unimplemented.
