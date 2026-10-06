(** * Host ELF extraction — mirrors [src/prefixgen/extract.rs]. *)

From Stdlib Require Import List NArith.
Import ListNotations.
From Classifier Require Import Predicate Raw.

Module Extract.
Import Predicate Raw.

Definition Bytes := list N.

Parameter extract_bpf_words : Bytes -> option BpfRawProgram.
Parameter extract_rv32_image : Bytes -> option Bytes.
Parameter split_rv32imc : Bytes -> option Rv32RawProgram.

End Extract.
