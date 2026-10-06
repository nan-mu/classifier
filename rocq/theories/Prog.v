(** * Prog: entry lookup, sequential successor, basic well-formedness. *)

From Coq Require Import Arith Bool List Lia.
Import ListNotations.
From Classifier Require Import Syntax.

Module Prog.
Import Syntax.

(** Position of index [i] in [p], if any. *)
Fixpoint find_pos (p : prog) (i : index) : option nat :=
  match p with
  | [] => None
  | (j, _) :: rest =>
      if Nat.eqb j i then Some 0
      else match find_pos rest i with
           | None => None
           | Some n => Some (S n)
           end
  end.

Lemma find_pos_Some_nth :
  forall p i pos,
    find_pos p i = Some pos ->
    exists ins, nth_error p pos = Some (i, ins).
Proof.
  induction p as [| [j ins] rest IH]; intros i pos H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb j i) eqn:Ej.
    + inversion H; subst. apply Nat.eqb_eq in Ej. subst.
      exists ins. reflexivity.
    + destruct (find_pos rest i) as [n|] eqn:F; try discriminate.
      inversion H; subst.
      apply IH in F as [ins' Hn].
      exists ins'. simpl. exact Hn.
Qed.

(** Sequential successor position. *)
Definition next_pos (p : prog) (pos : nat) : option nat :=
  let n := S pos in
  if Nat.ltb n (List.length p) then Some n else None.

Lemma next_pos_lt :
  forall p pos n,
    next_pos p pos = Some n ->
    n = S pos /\ S pos < List.length p.
Proof.
  intros p pos n H. unfold next_pos in H.
  destruct (Nat.ltb (S pos) (List.length p)) eqn:L; try discriminate.
  inversion H; subst. apply Nat.ltb_lt in L. split; auto.
Qed.

Lemma next_pos_S :
  forall p pos,
    S pos < List.length p ->
    next_pos p pos = Some (S pos).
Proof.
  intros p pos H. unfold next_pos. apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

(** Strictly increasing indices. *)
Fixpoint strictly_increasing (p : prog) : bool :=
  match p with
  | [] => true
  | [_] => true
  | (i, _) :: ((j, _) :: _) as rest =>
      Nat.ltb i j && strictly_increasing rest
  end.

Lemma strictly_increasing_tail :
  forall i ins p,
    strictly_increasing ((i, ins) :: p) = true ->
    strictly_increasing p = true.
Proof.
  intros i ins p H. destruct p as [| [j ins'] rest]; simpl in *; auto.
  apply andb_prop in H as [_ H]. exact H.
Qed.

(** Every index in the tail is strictly greater than [i]. *)
Lemma strictly_increasing_gt :
  forall i ins p pos j ins',
    strictly_increasing ((i, ins) :: p) = true ->
    nth_error p pos = Some (j, ins') ->
    i < j.
Proof.
  intros i ins p pos j ins' Hsi Hnth.
  revert i ins j ins' Hsi Hnth.
  induction p as [| [k insk] rest IH]; intros i ins j ins' Hsi Hnth.
  - destruct pos; discriminate.
  - simpl in Hsi. apply andb_prop in Hsi as [Hik Hrest].
    apply Nat.ltb_lt in Hik.
    destruct pos as [| pos'].
    + simpl in Hnth. inversion Hnth; subst. exact Hik.
    + simpl in Hnth.
      (* rest is strictly increasing and k < later *)
      assert (Hsi' : strictly_increasing ((k, insk) :: rest) = true).
      { simpl. destruct rest as [| [? ?] ?]; simpl in *; auto. }
      eapply Nat.lt_trans; [exact Hik|].
      eapply IH; eauto.
Qed.

Lemma strictly_increasing_unique :
  forall p pos1 pos2 i ins1 ins2,
    strictly_increasing p = true ->
    nth_error p pos1 = Some (i, ins1) ->
    nth_error p pos2 = Some (i, ins2) ->
    pos1 = pos2 /\ ins1 = ins2.
Proof.
  induction p as [| [j ins0] rest IH]; intros pos1 pos2 i ins1 ins2 Hsi H1 H2.
  - destruct pos1; discriminate.
  - destruct pos1 as [| p1]; destruct pos2 as [| p2]; simpl in *.
    + inversion H1; inversion H2; subst. split; auto.
    + inversion H1; subst.
      pose proof (strictly_increasing_gt _ _ _ _ _ _ Hsi H2) as Hlt.
      lia.
    + inversion H2; subst.
      pose proof (strictly_increasing_gt _ _ _ _ _ _ Hsi H1) as Hlt.
      lia.
    + apply strictly_increasing_tail in Hsi.
      eapply IH; eauto.
Qed.

Lemma find_pos_nth :
  forall p pos i ins,
    strictly_increasing p = true ->
    nth_error p pos = Some (i, ins) ->
    find_pos p i = Some pos.
Proof.
  induction p as [| [j ins0] rest IH]; intros pos i ins Hsi H; simpl in *.
  - destruct pos; discriminate.
  - destruct pos as [| pos'].
    + inversion H; subst. rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb j i) eqn:Ej.
      * apply Nat.eqb_eq in Ej. subst.
        pose proof (strictly_increasing_gt _ _ _ _ _ _ Hsi H) as Hlt. lia.
      * apply strictly_increasing_tail in Hsi.
        apply IH with (ins := ins) in H; auto. rewrite H. reflexivity.
Qed.

Definition lookup (p : prog) (i : index) : option insn :=
  match find_pos p i with
  | None => None
  | Some pos =>
      match nth_error p pos with
      | Some (_, ins) => Some ins
      | None => None
      end
  end.

Definition in_prog (p : prog) (i : index) : bool :=
  match find_pos p i with
  | Some _ => true
  | None => false
  end.

Lemma lookup_nth :
  forall p pos i ins,
    strictly_increasing p = true ->
    nth_error p pos = Some (i, ins) ->
    lookup p i = Some ins.
Proof.
  intros p pos i ins Hsi Hnth.
  unfold lookup. rewrite (find_pos_nth _ _ _ _ Hsi Hnth). rewrite Hnth. reflexivity.
Qed.

(** Basic structural well-formedness (targets exist; forward cond has fallthrough). *)
Definition wf_insn (p : prog) (pos : nat) (i : index) (ins : insn) : bool :=
  match ins with
  | IOther _ | IExit => true
  | ICond _ tgt =>
      if Nat.ltb i tgt then
        match find_pos p tgt with
        | None => false
        | Some _ =>
            match next_pos p pos with
            | Some _ => true
            | None => false
            end
        end
      else true
  | IGoto tgt =>
      if Nat.ltb i tgt then
        match find_pos p tgt with
        | None => false
        | Some _ => true
        end
      else true
  end.

Fixpoint wf_from (p : prog) (pos : nat) (fuel : nat) : bool :=
  match fuel with
  | 0 => true
  | S fuel' =>
      match nth_error p pos with
      | None => true
      | Some (i, ins) =>
          wf_insn p pos i ins &&
          match next_pos p pos with
          | None => true
          | Some n => wf_from p n fuel'
          end
      end
  end.

Definition wf_prog (p : prog) : bool :=
  match p with
  | [] => false
  | _ => strictly_increasing p && wf_from p 0 (List.length p)
  end.

Lemma wf_prog_increasing :
  forall p, wf_prog p = true -> strictly_increasing p = true.
Proof.
  intros p H. unfold wf_prog in H. destruct p; try discriminate.
  apply andb_prop in H as [H _]. exact H.
Qed.

Lemma wf_prog_nonempty :
  forall p, wf_prog p = true -> p <> [].
Proof.
  intros p H. unfold wf_prog in H. destruct p; discriminate || congruence.
Qed.

End Prog.
