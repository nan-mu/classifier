(** * Partitioned raw programs — mirrors raw types in [src/prefixgen/mod.rs]. *)

From Stdlib Require Import List NArith.
Import ListNotations.
From Classifier Require Import Predicate.

Module Raw.
Import Predicate.

(** One BPF encoding slot ([u64] LE numeric). *)
Definition Word64 := N.
Definition BpfRawProgram := list Word64.

Inductive U32OrU16 :=
| U32w : N -> U32OrU16
| U16w : N -> U32OrU16.

Definition Rv32RawProgram := list U32OrU16.

Definition bpf_machines (raw : BpfRawProgram) : list Machine :=
  map MBpf raw.

Definition rv32_machine (w : U32OrU16) : Machine :=
  match w with
  | U32w v => MRv32 v
  | U16w v => MRv16 v
  end.

Definition rv32_machines (raw : Rv32RawProgram) : list Machine :=
  map rv32_machine raw.

Module Tests.
Example bpf_machines_io :
  let input : BpfRawProgram := [1; 2] in
  let output := [MBpf 1; MBpf 2] in
  bpf_machines input = output.
Proof. reflexivity. Qed.

Example rv32_machines_io :
  let input : Rv32RawProgram := [U32w 10; U16w 20] in
  let output := [MRv32 10; MRv16 20] in
  rv32_machines input = output.
Proof. reflexivity. Qed.
End Tests.

End Raw.
