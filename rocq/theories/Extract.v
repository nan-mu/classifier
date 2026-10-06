(** * Host ELF extraction — mirrors [src/prefixgen/extract.rs].

    Parsing object files is outside the classifier TCB for now: we only
    fix the raw-program interface that decode consumes. *)

From Stdlib Require Import List NArith.
Import ListNotations.
From Classifier Require Import Predicate Raw.

Module Extract.
Import Predicate Raw.

(** Flat file bytes. *)
Definition Bytes := list N. (* each [N] is a byte 0..255; WF separate *)

Parameter extract_bpf_words : Bytes -> option BpfRawProgram.
Parameter extract_rv32_image : Bytes -> option Bytes.

(** Split a flat RV32IMC image into 16/32-bit words (mirrors [split_rv32imc]). *)
Parameter split_rv32imc : Bytes -> option Rv32RawProgram.

End Extract.
