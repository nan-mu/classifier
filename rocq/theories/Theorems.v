(** * Prefixgen and pathgen theorems. *)

From Stdlib Require Import List NArith.
Import ListNotations.
From Classifier Require Import Predicate Raw.
From Classifier Require Import prefixgen.Base prefixgen.Prefixgen.
From Classifier Require Import pathgen.Base.

Module Theorems.
Import Predicate Raw.
Import Base.
Import Prefixgen.

Theorem prefixgen_bpf_preserves_machine :
  forall raw prog,
    prefixgen_bpf raw = Some prog ->
    machines_of prog = bpf_machines raw.
Proof.
  exact Bpf.prefixgen_bpf_preserves_machine.
Qed.

Lemma prefixgen_bpf_length :
  forall raw prog,
    prefixgen_bpf raw = Some prog ->
    length prog = length raw.
Proof.
  intros raw prog H.
  pose proof (prefixgen_bpf_preserves_machine raw prog H) as Heq.
  unfold machines_of, bpf_machines in Heq.
  assert (Hlen : length (map insn_machine prog) = length (map MBpf raw))
    by (rewrite Heq; reflexivity).
  rewrite !length_map in Hlen.
  exact Hlen.
Qed.

Theorem prefixgen_rv32_preserves_machine :
  forall raw prog,
    prefixgen_rv32 raw = Some prog ->
    machines_of prog = rv32_machines raw.
Proof.
  exact Rv32.prefixgen_rv32_preserves_machine.
Qed.

Lemma prefixgen_rv32_length :
  forall raw prog,
    prefixgen_rv32 raw = Some prog ->
    length prog = length raw.
Proof.
  intros raw prog H.
  pose proof (prefixgen_rv32_preserves_machine raw prog H) as Heq.
  unfold machines_of, rv32_machines in Heq.
  assert (Hlen : length (map insn_machine prog) = length (map rv32_machine raw))
    by (rewrite Heq; reflexivity).
  rewrite !length_map in Hlen.
  exact Hlen.
Qed.

Theorem pathgen_preserves_machines :
  forall prog policy entry fuel paths,
    Pathgen.unique_indices prog ->
    Pathgen.pathgen prog policy entry fuel = Some paths ->
    Pathgen.path_machines_ok prog paths.
Proof.
  exact Pathgen.pathgen_preserves_machines.
Qed.

Theorem pathgen_codes_start_with_zero :
  forall prog policy entry fuel paths,
    Pathgen.pathgen prog policy entry fuel = Some paths ->
    Pathgen.codes_start_with_zero paths.
Proof.
  exact Pathgen.pathgen_codes_start_with_zero.
Qed.

End Theorems.
