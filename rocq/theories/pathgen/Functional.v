(** * Pathgen functional correctness.

    This file contains properties of the path generator as a program:
    source-machine preservation and path-code shape.  It deliberately does
    not state cross-ISA or predicate-semantic equivalence.  Those obligations
    live in [PredicateEquiv.v]. *)

From Stdlib Require Import List.

From Classifier Require Import Predicate.
From Classifier Require Import pathgen.Base.

Module PathgenFunctional.
Import Predicate.
Import Pathgen.

(** Every emitted instruction carries the machine word of the source
    instruction with the same index. *)
Theorem preserves_machines :
  forall prog policy entry fuel paths,
    unique_indices prog ->
    pathgen prog policy entry fuel = Some paths ->
    path_machines_ok prog paths.
Proof.
  exact pathgen_preserves_machines.
Qed.

(** The initial [false] bit is a file-name/code convention, independent of
    the semantics of predicates on the path. *)
Theorem codes_start_with_zero :
  forall prog policy entry fuel paths,
    pathgen prog policy entry fuel = Some paths ->
    Pathgen.codes_start_with_zero paths.
Proof.
  exact pathgen_codes_start_with_zero.
Qed.

(** The local forward-branch rewrite preserves source identity.  This is a
    functional fact about [assert_insn], not a claim that [PIfGoto] and
    [PAssert] have equivalent machine semantics. *)
Theorem assert_rewrite_preserves_source :
  forall i c expected id,
    (assert_insn i c expected id).(insn_index) = i.(insn_index) /\
    (assert_insn i c expected id).(insn_machine) = i.(insn_machine).
Proof.
  exact assert_insn_index_machine.
Qed.

End PathgenFunctional.
