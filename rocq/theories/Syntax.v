(** * Syntax: structured AST for T0 path classification.

    Jump targets are instruction indices (BPF slots), not bpftool offset strings.
    Condition expressions are opaque strings; T0 does not interpret them.
*)

From Coq Require Import Arith Bool List String.
Import ListNotations.

Module Syntax.

Definition index := nat.
Definition exp := string.

Inductive insn : Type :=
| IOther (body : string)
| IExit
| ICond (e : exp) (tgt : index)
| IGoto (tgt : index).

Inductive path_line : Type :=
| LInsn (i : index) (ins : insn)
| LAssert (i : index) (e : exp) (b : bool).

Definition prog := list (index * insn).
Definition path := list path_line.
Definition paths := list path.

Definition string_eqb (a b : string) : bool :=
  if string_dec a b then true else false.

Lemma string_eqb_eq : forall a b, string_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold string_eqb.
  destruct (string_dec a b); split; intros H; congruence.
Qed.

Definition insn_eqb (a b : insn) : bool :=
  match a, b with
  | IOther ba, IOther bb => string_eqb ba bb
  | IExit, IExit => true
  | ICond ea ta, ICond eb tb => string_eqb ea eb && Nat.eqb ta tb
  | IGoto ta, IGoto tb => Nat.eqb ta tb
  | _, _ => false
  end.

Lemma insn_eqb_eq : forall a b, insn_eqb a b = true <-> a = b.
Proof.
  intros a b. split.
  - destruct a, b; simpl; try discriminate; intros H.
    + apply string_eqb_eq in H. congruence.
    + reflexivity.
    + apply andb_prop in H as [H1 H2].
      apply string_eqb_eq in H1. apply Nat.eqb_eq in H2. congruence.
    + apply Nat.eqb_eq in H. congruence.
  - intros ->. destruct b; simpl.
    + unfold string_eqb. destruct (string_dec body body); congruence.
    + reflexivity.
    + rewrite (proj2 (string_eqb_eq e e) eq_refl), Nat.eqb_refl. reflexivity.
    + apply Nat.eqb_refl.
Qed.

Definition path_line_eqb (a b : path_line) : bool :=
  match a, b with
  | LInsn ia insa, LInsn ib insb => Nat.eqb ia ib && insn_eqb insa insb
  | LAssert ia ea ba, LAssert ib eb bb =>
      Nat.eqb ia ib && string_eqb ea eb && Bool.eqb ba bb
  | _, _ => false
  end.

Lemma path_line_eqb_eq : forall a b, path_line_eqb a b = true <-> a = b.
Proof.
  intros a b. split.
  - destruct a, b; simpl; try discriminate; intros H.
    + apply andb_prop in H as [H1 H2].
      apply Nat.eqb_eq in H1. apply insn_eqb_eq in H2. congruence.
    + apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 H3].
      apply Nat.eqb_eq in H1. apply string_eqb_eq in H3.
      destruct b0, b1; simpl in H2; try discriminate; congruence.
  - intros ->. destruct b; simpl.
    + rewrite Nat.eqb_refl, (proj2 (insn_eqb_eq _ _) eq_refl). reflexivity.
    + rewrite Nat.eqb_refl, (proj2 (string_eqb_eq _ _) eq_refl).
      destruct b; reflexivity.
Qed.

Lemma path_line_eq_dec : forall a b : path_line, {a = b} + {a <> b}.
Proof.
  intros a b. destruct (path_line_eqb a b) eqn:E.
  - left. apply path_line_eqb_eq. exact E.
  - right. intros Heq. apply path_line_eqb_eq in Heq. congruence.
Qed.

Definition path_line_index (l : path_line) : index :=
  match l with
  | LInsn i _ => i
  | LAssert i _ _ => i
  end.

End Syntax.
