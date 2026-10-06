(** * Pathgen facade — mirrors [src/pathgen/mod.rs]. *)

From Stdlib Require Import List.
Import ListNotations.
From Classifier Require Import Predicate.
From Classifier Require Import pathgen.Base.

Module PathgenFacade.
Import Predicate.
Import Pathgen.

Definition pathgen_bpf_prog := pathgen_bpf.
Definition pathgen_rv32_prog := pathgen_rv32.

Module Tests.
Example facade_bpf_alias :
  pathgen_bpf_prog = pathgen_bpf.
Proof. reflexivity. Qed.
End Tests.

End PathgenFacade.
