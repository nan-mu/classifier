# Exhibit

The Rocq side is a projection of the vendored instruction rules. It is not native Rocq symbolic execution. EQUIVALENT means the value inequality is unsat under the listed input assumptions and Alive2 non_poison is true under those assumptions. Rocq has no poison bit. Undef is not proved by matching tags. If definedness cannot be stated to the solver, the verdict is UNSUPPORTED. Poison is not undef. UNKNOWN and UNSUPPORTED are not passes. A concrete trace agreement is not a symbolic proof.

Run `alive2/exhibit/regen.sh` from the repository root.

Each SMT cell is EQUIVALENT, COUNTEREXAMPLE, UNKNOWN, or UNSUPPORTED. UNKNOWN and UNSUPPORTED are not passes.

## JGT64

Bytes `bf10000000000000250002000a0000001700000001000000050001000000000007000000010000009500000000000000`.

Bug flag is none.

Input assumptions.

r1 is not undef and not poison.

SMT assumption is `(and np_r1 (= #b0 isundef_r1))`.

### pc 0 alu64 mov r0, r1

Rules `exec_alu`, `eval_alu64`, `nextinstr`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `const 1`.

Rocq projection path is `true [nextinstr]`.

Alive2 smt path is `true`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var undef!0`.

r0 Rocq projection is `undef [create_initial_state]`.

r0 Alive2 smt is `undef!0`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | input | input | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var r1`.

r0 Rocq projection is `var r1 [Vlong]`.

r0 Alive2 smt is `r1`.

Successors.

This instruction has no successor edge.

### pc 1 jmp jgt r0, 10, 2

Rules `exec_jmpcmp`, `eval_cmp_static`, `eval_cmp64`, `nextinstr`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `const 1`.

Rocq projection path is `true [nextinstr]`.

Alive2 smt path is `true`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | input | input | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var r1`.

r0 Rocq projection is `var r1 [Vlong]`.

r0 Alive2 smt is `r1`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | input | input | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var r1`.

r0 Rocq projection is `var r1 [Vlong]`.

r0 Alive2 smt is `r1`.

Successors.

Edge to pc 4 block `%b2` is EQUIVALENT.

Alive2 jump condition is `and(bvule(const 11, var r1), and(=(const 0, var isundef_r1), var np_r1))`.

Rocq projection condition is `ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64])`.

Alive2 smt condition is `(and (bvule #x000000000000000b r1) (= #b0 isundef_r1) np_r1)`.

Edge to pc 2 block `%b1` is EQUIVALENT.

Alive2 jump condition is `and(not(bvule(const 11, var r1)), and(=(const 0, var isundef_r1), var np_r1))`.

Rocq projection condition is `not [exec_jmpcmp](ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64]))`.

Alive2 smt condition is `(and (not (bvule #x000000000000000b r1)) (= #b0 isundef_r1) np_r1)`.

### pc 2 alu64 sub r0, 1

Rules `exec_alu`, `eval_alu64`, `nextinstr`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `not(bvule(const 11, var r1))`.

Rocq projection path is `not [exec_jmpcmp](ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64]))`.

Alive2 smt path is `(not (bvule #x000000000000000b r1))`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | input | input | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var r1`.

r0 Rocq projection is `var r1 [Vlong]`.

r0 Alive2 smt is `r1`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `add(var r1, const 18446744073709551615)`.

r0 Rocq projection is `sub [eval_alu64](var r1 [Vlong], const 1 [eval_alu64])`.

r0 Alive2 smt is `(bvadd r1 #xffffffffffffffff)`.

Successors.

This instruction has no successor edge.

### pc 3 jmp ja 1

Rules `exec_jmp64`, `nextinstr`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `not(bvule(const 11, var r1))`.

Rocq projection path is `not [exec_jmpcmp](ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64]))`.

Alive2 smt path is `(not (bvule #x000000000000000b r1))`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `add(var r1, const 18446744073709551615)`.

r0 Rocq projection is `sub [eval_alu64](var r1 [Vlong], const 1 [eval_alu64])`.

r0 Alive2 smt is `(bvadd r1 #xffffffffffffffff)`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `add(var r1, const 18446744073709551615)`.

r0 Rocq projection is `sub [eval_alu64](var r1 [Vlong], const 1 [eval_alu64])`.

r0 Alive2 smt is `(bvadd r1 #xffffffffffffffff)`.

Successors.

Edge to pc 5 block `%b3` is EQUIVALENT.

Alive2 jump condition is `and(not(bvule(const 11, var r1)), and(=(const 0, var isundef_r1), var np_r1))`.

Rocq projection condition is `not [exec_jmpcmp](ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64]))`.

Alive2 smt condition is `(and (not (bvule #x000000000000000b r1)) (= #b0 isundef_r1) np_r1)`.

### pc 4 alu64 add r0, 1

Rules `exec_alu`, `eval_alu64`, `nextinstr`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `bvule(const 11, var r1)`.

Rocq projection path is `ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64])`.

Alive2 smt path is `(bvule #x000000000000000b r1)`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | input | input | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var r1`.

r0 Rocq projection is `var r1 [Vlong]`.

r0 Alive2 smt is `r1`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `add(const 1, var r1)`.

r0 Rocq projection is `add [eval_alu64](var r1 [Vlong], const 1 [eval_alu64])`.

r0 Alive2 smt is `(bvadd #x0000000000000001 r1)`.

Successors.

Edge to pc 5 block `%b3` is EQUIVALENT.

Alive2 jump condition is `and(bvule(const 11, var r1), and(=(const 0, var isundef_r1), var np_r1))`.

Rocq projection condition is `ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64])`.

Alive2 smt condition is `(and (bvule #x000000000000000b r1) (= #b0 isundef_r1) np_r1)`.

### pc 5 jmp exit

Rules `exec_ret`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `const 1`.

Rocq projection path is `or [exec_jmpcmp](not [exec_jmpcmp](ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64])), ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64]))`.

Alive2 smt path is `true`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `ite(bvule(const 11, var r1), add(const 1, var r1), add(var r1, const 18446744073709551615))`.

r0 Rocq projection is `ite [exec_jmpcmp](not [exec_jmpcmp](ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64])), sub [eval_alu64](var r1 [Vlong], const 1 [eval_alu64]), add [eval_alu64](var r1 [Vlong], const 1 [eval_alu64]))`.

r0 Alive2 smt is `(ite (bvule #x000000000000000b r1)
     (bvadd #x0000000000000001 r1)
     (bvadd r1 #xffffffffffffffff))`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `ite(bvule(const 11, var r1), add(const 1, var r1), add(var r1, const 18446744073709551615))`.

r0 Rocq projection is `ite [exec_jmpcmp](not [exec_jmpcmp](ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64])), sub [eval_alu64](var r1 [Vlong], const 1 [eval_alu64]), add [eval_alu64](var r1 [Vlong], const 1 [eval_alu64]))`.

r0 Alive2 smt is `(ite (bvule #x000000000000000b r1)
     (bvadd #x0000000000000001 r1)
     (bvadd r1 #xffffffffffffffff))`.

Successors.

Edge to exit is EQUIVALENT.

Alive2 jump condition is `const 1`.

Rocq projection condition is `or [exec_jmpcmp](not [exec_jmpcmp](ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64])), ugt [eval_cmp64] (eval_cmp_static not applied)(var r1 [Vlong], const 10 [eval_cmp64]))`.

Alive2 smt condition is `true`.

Phi inputs.

r0 from `%b1` is EQUIVALENT.

Alive2 incoming expression is `add(var r1, const 18446744073709551615)`.

Rocq projection arm is `sub [eval_alu64](var r1 [Vlong], const 1 [eval_alu64])`.

Alive2 smt incoming is `(bvadd r1 #xffffffffffffffff)`.

r0 from `%b2` is EQUIVALENT.

Alive2 incoming expression is `add(const 1, var r1)`.

Rocq projection arm is `add [eval_alu64](var r1 [Vlong], const 1 [eval_alu64])`.

Alive2 smt incoming is `(bvadd #x0000000000000001 r1)`.

Concrete trace comparison against rocq-step. Agreement here is not a symbolic proof.

| input | projection return | rocq-step return | agree |
| --- | --- | --- | --- |
| jgt64-11 | 000000000000000c | 000000000000000c | yes |
| jgt64-10 | 0000000000000009 | 0000000000000009 | yes |

jgt64-11.

pc 0 projection NEXT to pc 1, rocq-step NEXT to pc 1.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | undef | undef | agree |
| r1 | 000000000000000b | 000000000000000b | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000b | 000000000000000b | agree |
| r1 | 000000000000000b | 000000000000000b | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 1 projection NEXT to pc 4, rocq-step NEXT to pc 4.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000b | 000000000000000b | agree |
| r1 | 000000000000000b | 000000000000000b | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000b | 000000000000000b | agree |
| r1 | 000000000000000b | 000000000000000b | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 4 projection NEXT to pc 5, rocq-step NEXT to pc 5.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000b | 000000000000000b | agree |
| r1 | 000000000000000b | 000000000000000b | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000c | 000000000000000c | agree |
| r1 | 000000000000000b | 000000000000000b | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 5 projection EXIT to exit, rocq-step EXIT to exit.

Exit return projection `000000000000000c` rocq-step `000000000000000c` is agree.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000c | 000000000000000c | agree |
| r1 | 000000000000000b | 000000000000000b | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000c | 000000000000000c | agree |
| r1 | 000000000000000b | 000000000000000b | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

jgt64-10.

pc 0 projection NEXT to pc 1, rocq-step NEXT to pc 1.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | undef | undef | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000a | 000000000000000a | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 1 projection NEXT to pc 2, rocq-step NEXT to pc 2.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000a | 000000000000000a | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000a | 000000000000000a | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 2 projection NEXT to pc 3, rocq-step NEXT to pc 3.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 000000000000000a | 000000000000000a | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000009 | 0000000000000009 | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 3 projection NEXT to pc 5, rocq-step NEXT to pc 5.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000009 | 0000000000000009 | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000009 | 0000000000000009 | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 5 projection EXIT to exit, rocq-step EXIT to exit.

Exit return projection `0000000000000009` rocq-step `0000000000000009` is agree.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000009 | 0000000000000009 | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000009 | 0000000000000009 | agree |
| r1 | 000000000000000a | 000000000000000a | agree |
| r2 | undef | undef | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

## DIV64

Bytes `bf100000000000003f200000000000009500000000000000`.

Bug flag is none.

Input assumptions.

r1 is not undef and not poison.

r2 is not undef and not poison.

SMT assumption is `(and np_r1 (= #b0 isundef_r1) np_r2 (= #b0 isundef_r2))`.

### pc 0 alu64 mov r0, r1

Rules `exec_alu`, `eval_alu64`, `nextinstr`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `const 1`.

Rocq projection path is `true [nextinstr]`.

Alive2 smt path is `true`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var undef!114`.

r0 Rocq projection is `undef [create_initial_state]`.

r0 Alive2 smt is `undef!114`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | input | input | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var r1`.

r0 Rocq projection is `var r1 [Vlong]`.

r0 Alive2 smt is `r1`.

Successors.

This instruction has no successor edge.

### pc 1 alu64 div r0, r2

Rules `exec_alu`, `eval_div_u64`, `nextinstr`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `const 1`.

Rocq projection path is `true [nextinstr]`.

Alive2 smt path is `true`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | input | input | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var r1`.

r0 Rocq projection is `var r1 [Vlong]`.

r0 Alive2 smt is `r1`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `ite(=(var r2, const 0), const 0, bvudiv(var r1, var r2))`.

r0 Rocq projection is `ite [eval_div_u64](eq [eval_div_u64](var r2 [Vlong], const 0 [eval_div_u64]), const 0 [eval_div_u64], udiv [eval_div_u64](var r1 [Vlong], var r2 [Vlong]))`.

r0 Alive2 smt is `(ite (= r2 #x0000000000000000) #x0000000000000000 (bvudiv r1 r2))`.

Successors.

This instruction has no successor edge.

Phi inputs.

r0 from `%1` is EQUIVALENT.

Alive2 incoming expression is `const 0`.

Rocq projection arm is `const 0 [eval_div_u64]`.

Alive2 smt incoming is `#x0000000000000000`.

r0 from `%2` is EQUIVALENT.

Alive2 incoming expression is `bvudiv(var r1, var r2)`.

Rocq projection arm is `udiv [eval_div_u64](var r1 [Vlong], var r2 [Vlong])`.

Alive2 smt incoming is `(bvudiv r1 r2)`.

### pc 2 jmp exit

Rules `exec_ret`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `const 1`.

Rocq projection path is `true [nextinstr]`.

Alive2 smt path is `true`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `ite(=(var r2, const 0), const 0, bvudiv(var r1, var r2))`.

r0 Rocq projection is `ite [eval_div_u64](eq [eval_div_u64](var r2 [Vlong], const 0 [eval_div_u64]), const 0 [eval_div_u64], udiv [eval_div_u64](var r1 [Vlong], var r2 [Vlong]))`.

r0 Alive2 smt is `(ite (= r2 #x0000000000000000) #x0000000000000000 (bvudiv r1 r2))`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `ite(=(var r2, const 0), const 0, bvudiv(var r1, var r2))`.

r0 Rocq projection is `ite [eval_div_u64](eq [eval_div_u64](var r2 [Vlong], const 0 [eval_div_u64]), const 0 [eval_div_u64], udiv [eval_div_u64](var r1 [Vlong], var r2 [Vlong]))`.

r0 Alive2 smt is `(ite (= r2 #x0000000000000000) #x0000000000000000 (bvudiv r1 r2))`.

Successors.

Edge to exit is EQUIVALENT.

Alive2 jump condition is `const 1`.

Rocq projection condition is `true [nextinstr]`.

Alive2 smt condition is `true`.

Phi inputs.

r0 from `%1` is EQUIVALENT.

Alive2 incoming expression is `const 0`.

Rocq projection arm is `const 0 [eval_div_u64]`.

Alive2 smt incoming is `#x0000000000000000`.

r0 from `%2` is EQUIVALENT.

Alive2 incoming expression is `bvudiv(var r1, var r2)`.

Rocq projection arm is `udiv [eval_div_u64](var r1 [Vlong], var r2 [Vlong])`.

Alive2 smt incoming is `(bvudiv r1 r2)`.

Concrete trace comparison against rocq-step. Agreement here is not a symbolic proof.

| input | projection return | rocq-step return | agree |
| --- | --- | --- | --- |
| div64-7-2 | 0000000000000003 | 0000000000000003 | yes |
| div64-7-0 | 0000000000000000 | 0000000000000000 | yes |

div64-7-2.

pc 0 projection NEXT to pc 1, rocq-step NEXT to pc 1.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | undef | undef | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000002 | 0000000000000002 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000007 | 0000000000000007 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000002 | 0000000000000002 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 1 projection NEXT to pc 2, rocq-step NEXT to pc 2.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000007 | 0000000000000007 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000002 | 0000000000000002 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000003 | 0000000000000003 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000002 | 0000000000000002 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 2 projection EXIT to exit, rocq-step EXIT to exit.

Exit return projection `0000000000000003` rocq-step `0000000000000003` is agree.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000003 | 0000000000000003 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000002 | 0000000000000002 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000003 | 0000000000000003 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000002 | 0000000000000002 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

div64-7-0.

pc 0 projection NEXT to pc 1, rocq-step NEXT to pc 1.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | undef | undef | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000000 | 0000000000000000 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000007 | 0000000000000007 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000000 | 0000000000000000 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 1 projection NEXT to pc 2, rocq-step NEXT to pc 2.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000007 | 0000000000000007 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000000 | 0000000000000000 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000000 | 0000000000000000 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000000 | 0000000000000000 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

pc 2 projection EXIT to exit, rocq-step EXIT to exit.

Exit return projection `0000000000000000` rocq-step `0000000000000000` is agree.

Pre-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000000 | 0000000000000000 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000000 | 0000000000000000 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

Post-state comparison.

| reg | projection | rocq-step | comparison |
| --- | --- | --- | --- |
| r0 | 0000000000000000 | 0000000000000000 | agree |
| r1 | 0000000000000007 | 0000000000000007 | agree |
| r2 | 0000000000000000 | 0000000000000000 | agree |
| r3 | undef | undef | agree |
| r4 | undef | undef | agree |
| r5 | undef | undef | agree |
| r6 | undef | undef | agree |
| r7 | undef | undef | agree |
| r8 | undef | undef | agree |
| r9 | undef | undef | agree |

## DIV64 div-zero-as-ub

Bytes `bf100000000000003f200000000000009500000000000000`.

Bug flag is div-zero-as-ub.

Input assumptions.

r1 is not undef and not poison.

r2 is not undef and not poison.

SMT assumption is `(and np_r1 (= isundef_r1 #b0) np_r2 (= #b0 isundef_r2))`.

### pc 0 alu64 mov r0, r1

Rules `exec_alu`, `eval_alu64`, `nextinstr`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `const 1`.

Rocq projection path is `true [nextinstr]`.

Alive2 smt path is `true`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var undef!216`.

r0 Rocq projection is `undef [create_initial_state]`.

r0 Alive2 smt is `undef!216`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | input | input | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var r1`.

r0 Rocq projection is `var r1 [Vlong]`.

r0 Alive2 smt is `r1`.

Successors.

This instruction has no successor edge.

### pc 1 alu64 div r0, r2

Rules `exec_alu`, `eval_div_u64`, `nextinstr`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `const 1`.

Rocq projection path is `true [nextinstr]`.

Alive2 smt path is `true`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | input | input | EQUIVALENT | EQUIVALENT |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `var r1`.

r0 Rocq projection is `var r1 [Vlong]`.

r0 Alive2 smt is `r1`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | COUNTEREXAMPLE |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `bvudiv(var r1, var r2)`.

r0 Rocq projection is `ite [eval_div_u64](eq [eval_div_u64](var r2 [Vlong], const 0 [eval_div_u64]), const 0 [eval_div_u64], udiv [eval_div_u64](var r1 [Vlong], var r2 [Vlong]))`.

r0 Alive2 smt is `(bvudiv r1 r2)`.

r0 model is `np_r2 -> true
r2 -> #x0000000000000000
r1 -> #x0000000000000000
isundef_r2 -> #b0
np_r1 -> true
isundef_r1 -> #b0
`.

Successors.

This instruction has no successor edge.

### pc 2 jmp exit

Rules `exec_ret`.

Symbolic path condition is EQUIVALENT.

Alive2 path is `const 1`.

Rocq projection path is `true [nextinstr]`.

Alive2 smt path is `true`.

Pre-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | COUNTEREXAMPLE |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `bvudiv(var r1, var r2)`.

r0 Rocq projection is `ite [eval_div_u64](eq [eval_div_u64](var r2 [Vlong], const 0 [eval_div_u64]), const 0 [eval_div_u64], udiv [eval_div_u64](var r1 [Vlong], var r2 [Vlong]))`.

r0 Alive2 smt is `(bvudiv r1 r2)`.

r0 model is `isundef_r2 -> #b0
r1 -> #x0000000000400000
r2 -> #x0000000000000000
isundef_r1 -> #b0
np_r1 -> true
np_r2 -> true
`.

Post-state.

| reg | alive tag | rocq tag | definedness | value |
| --- | --- | --- | --- | --- |
| r0 | bits | bits | EQUIVALENT | COUNTEREXAMPLE |
| r1 | input | input | EQUIVALENT | EQUIVALENT |
| r2 | input | input | EQUIVALENT | EQUIVALENT |
| r3 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r4 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r5 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r6 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r7 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r8 | undef | undef | UNSUPPORTED | UNSUPPORTED |
| r9 | undef | undef | UNSUPPORTED | UNSUPPORTED |

r0 Alive2 expression is `bvudiv(var r1, var r2)`.

r0 Rocq projection is `ite [eval_div_u64](eq [eval_div_u64](var r2 [Vlong], const 0 [eval_div_u64]), const 0 [eval_div_u64], udiv [eval_div_u64](var r1 [Vlong], var r2 [Vlong]))`.

r0 Alive2 smt is `(bvudiv r1 r2)`.

r0 model is `np_r2 -> true
r2 -> #x0000000000000000
r1 -> #x0000000000400000
isundef_r2 -> #b0
np_r1 -> true
isundef_r1 -> #b0
`.

Successors.

Edge to exit is EQUIVALENT.

Alive2 jump condition is `const 1`.

Rocq projection condition is `true [nextinstr]`.

Alive2 smt condition is `true`.

## Concrete sanity

These edges are concrete traces. They are not a symbolic proof.

### jgt64-11

The concrete traces agree.

pc 0 NEXT to pc1, r0 000000000000000b.

pc 1 NEXT to pc4, r0 000000000000000b.

pc 4 NEXT to pc5, r0 000000000000000c.

pc 5 EXIT to exit, r0 000000000000000c.

### jgt64-10

The concrete traces agree.

pc 0 NEXT to pc1, r0 000000000000000a.

pc 1 NEXT to pc2, r0 000000000000000a.

pc 2 NEXT to pc3, r0 0000000000000009.

pc 3 NEXT to pc5, r0 0000000000000009.

pc 5 EXIT to exit, r0 0000000000000009.

### div64-7-0-div-zero-as-ub

Divergence is pc 1 status alive2=UB rocq=NEXT.

pc 0 NEXT to pc1, r0 0000000000000007.

pc 1 NEXT to pc2, r0 0000000000000000.

pc 2 EXIT to exit, r0 0000000000000000.

### div64-7-2

The concrete traces agree.

pc 0 NEXT to pc1, r0 0000000000000007.

pc 1 NEXT to pc2, r0 0000000000000003.

pc 2 EXIT to exit, r0 0000000000000003.

### sdiv64-min--1

The concrete traces agree.

pc 0 NEXT to pc1, r0 8000000000000000.

pc 1 NEXT to pc2, r0 8000000000000000.

pc 2 EXIT to exit, r0 8000000000000000.

### div64-7-0

The concrete traces agree.

pc 0 NEXT to pc1, r0 0000000000000007.

pc 1 NEXT to pc2, r0 0000000000000000.

pc 2 EXIT to exit, r0 0000000000000000.

