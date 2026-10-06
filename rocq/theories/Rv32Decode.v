(** * RV32 raw → Prefix — mirrors [src/prefixgen/rv32.rs].

    Concrete IMC decode + [Op]→[Predicate] will land here later; the
    interface matches Rust so BPF/RV32 theorems share [Prefixgen]. *)

From Stdlib Require Import List NArith.
Import ListNotations.
From Classifier Require Import Predicate Raw.

Module Rv32Decode.
Import Predicate Raw.

(** Annotate an already-split RV32IMC word list.
    [None] = unsupported / environment mismatch (as in Rust [Result]). *)
Parameter prefixgen_rv32_words : Rv32RawProgram -> option Program.

Axiom prefixgen_rv32_preserves_machine :
  forall raw prog,
    prefixgen_rv32_words raw = Some prog ->
    map insn_machine prog = rv32_machines raw.

End Rv32Decode.
