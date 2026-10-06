(** * T0Input: legal programs for the T0 left-inverse theorem.

    [wf_prog] covers targets / fallthrough.
    [covers_all] requires every instruction to appear on some expanded path
    (no dead code skipped only by forward [goto]). Coverage is expressed via
    the expansion relation in [T0], so here we only package [wf_prog] plus a
    placeholder predicate filled in [T0]/[Theorems].
*)

From Coq Require Import List.
Import ListNotations.
From Classifier Require Import Syntax Prog.

Module T0Input.
Import Syntax Prog.

(** Structural input predicate (computable). *)
Definition T0Input_struct (p : prog) : Prop :=
  wf_prog p = true.

End T0Input.
