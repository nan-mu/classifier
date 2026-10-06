(** * Restore: proof-only inverse of T0 expansion.

    - Merge every [LInsn i ins] across paths (copies must agree).
    - Rebuild each forward [ICond] from [LAssert i e true] using the next
      path-line index as [tgt] (spec [t0.md]).
    - [LAssert _ _ false] is ignored for reconstruction (pairing is a
      [T0Output] concern for the right inverse).
*)

From Coq Require Import Arith Bool List Lia.
Import ListNotations.
From Classifier Require Import Syntax Prog.

Module Restore.
Import Syntax Prog.

Definition alist := list (index * insn).

Fixpoint alist_insert (a : alist) (i : index) (ins : insn) : option alist :=
  match a with
  | [] => Some [(i, ins)]
  | (j, ins') :: rest =>
      if Nat.eqb j i then
        if insn_eqb ins' ins then Some a else None
      else
        match alist_insert rest i ins with
        | None => None
        | Some rest' => Some ((j, ins') :: rest')
        end
  end.

Fixpoint alist_lookup (a : alist) (i : index) : option insn :=
  match a with
  | [] => None
  | (j, ins) :: rest =>
      if Nat.eqb j i then Some ins else alist_lookup rest i
  end.

Lemma alist_insert_lookup :
  forall a i ins a',
    alist_insert a i ins = Some a' ->
    alist_lookup a' i = Some ins.
Proof.
  induction a as [| [j insj] rest IH]; intros i ins a' H; simpl in *.
  - inversion H; subst. simpl. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb j i) eqn:Ej.
    + destruct (insn_eqb insj ins) eqn:Eins; try discriminate.
      inversion H; subst. simpl. rewrite Ej.
      apply insn_eqb_eq in Eins. subst. reflexivity.
    + destruct (alist_insert rest i ins) as [rest'|] eqn:Hi; try discriminate.
      inversion H; subst. simpl. rewrite Ej.
      eapply IH; eauto.
Qed.

Lemma alist_insert_preserves :
  forall a i ins a' k insk,
    alist_insert a i ins = Some a' ->
    k <> i ->
    alist_lookup a k = Some insk ->
    alist_lookup a' k = Some insk.
Proof.
  induction a as [| [j insj] rest IH]; intros i ins a' k insk H Hneq Hl; simpl in *.
  - discriminate.
  - destruct (Nat.eqb j i) eqn:Ej.
    + destruct (insn_eqb insj ins) eqn:Eins; try discriminate.
      inversion H; subst. simpl.
      destruct (Nat.eqb j k) eqn:Ek; auto.
    + destruct (alist_insert rest i ins) as [rest'|] eqn:Hi; try discriminate.
      inversion H; subst. simpl.
      destruct (Nat.eqb j k) eqn:Ek; auto.
      eapply IH; eauto.
Qed.

Fixpoint collect_path (ph : path) (a : alist) : option alist :=
  match ph with
  | [] => Some a
  | LInsn i ins :: rest =>
      match alist_insert a i ins with
      | None => None
      | Some a' => collect_path rest a'
      end
  | LAssert i e true :: rest =>
      match rest with
      | [] => None
      | l :: _ =>
          match alist_insert a i (ICond e (path_line_index l)) with
          | None => None
          | Some a' => collect_path rest a'
          end
      end
  | LAssert _ _ false :: rest =>
      collect_path rest a
  end.

Fixpoint collect_paths (ps : paths) (a : alist) : option alist :=
  match ps with
  | [] => Some a
  | ph :: rest =>
      match collect_path ph a with
      | None => None
      | Some a' => collect_paths rest a'
      end
  end.

Fixpoint insert_sorted (i : index) (ins : insn) (p : prog) : prog :=
  match p with
  | [] => [(i, ins)]
  | (j, ins') :: rest =>
      if Nat.ltb i j then (i, ins) :: p
      else (j, ins') :: insert_sorted i ins rest
  end.

Fixpoint sort_prog (a : alist) : prog :=
  match a with
  | [] => []
  | (i, ins) :: rest => insert_sorted i ins (sort_prog rest)
  end.

Definition t0_restore (ps : paths) : option prog :=
  match collect_paths ps [] with
  | None => None
  | Some a => Some (sort_prog a)
  end.

Definition t0_restore_def (ps : paths) : prog :=
  match t0_restore ps with
  | Some p => p
  | None => []
  end.

Lemma insert_sorted_In :
  forall i ins p k insk,
    In (k, insk) (insert_sorted i ins p) <->
    (k = i /\ insk = ins) \/ In (k, insk) p.
Proof.
  intros i ins p. induction p as [| [j insj] rest IH]; intros k insk; simpl.
  - firstorder. inversion H; subst; auto. contradiction.
  - destruct (Nat.ltb i j) eqn:Hlt; simpl.
    + split; intros H.
      * destruct H as [H|H]; [inversion H; subst; auto|auto].
      * destruct H as [[-> ->]|H]; auto.
    + split; intros H.
      * destruct H as [H|H].
        -- inversion H; subst. right. left. reflexivity.
        -- apply IH in H. destruct H as [[-> ->]|H]; auto. right. right. exact H.
      * destruct H as [[-> ->]|H].
        -- (* i = k, need to insert into rest *)
           right. apply IH. left; auto.
        -- destruct H as [H|H].
           ++ inversion H; subst. left. reflexivity.
           ++ right. apply IH. right. exact H.
Qed.

Lemma sort_prog_In :
  forall a i ins,
    In (i, ins) (sort_prog a) <-> In (i, ins) a.
Proof.
  induction a as [| [j insj] rest IH]; intros i ins; simpl.
  - split; contradiction.
  - rewrite insert_sorted_In, IH. firstorder.
Qed.

Lemma alist_lookup_In :
  forall a i ins,
    alist_lookup a i = Some ins -> In (i, ins) a.
Proof.
  induction a as [| [j insj] rest IH]; intros i ins H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb j i) eqn:Ej.
    + inversion H; subst. apply Nat.eqb_eq in Ej. subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

Lemma alist_lookup_complete :
  forall a i ins,
    (forall j ins1 ins2, In (j, ins1) a -> In (j, ins2) a -> ins1 = ins2) ->
    In (i, ins) a ->
    alist_lookup a i = Some ins.
Proof.
  induction a as [| [j insj] rest IH]; intros i ins Huniq Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin|Hin].
    + inversion Hin; subst. rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb j i) eqn:Ej.
      * apply Nat.eqb_eq in Ej. subst.
        assert (insj = ins) by (apply (Huniq i); [left; reflexivity|right; exact Hin]).
        subst. reflexivity.
      * apply IH; auto.
        intros j' ins1 ins2 H1 H2. apply (Huniq j'); simpl; auto.
Qed.

End Restore.
