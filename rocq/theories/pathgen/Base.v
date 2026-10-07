(** * Pathgen — mirrors [src/pathgen/]: forward [PIfGoto] → [PAssert].

    Input is an already-annotated [Program] (post-prefixgen).
    Path codes: start [[false]] (= "0"); forward taken appends [true] (= "1"),
    fallthrough appends [false] (= "0"). *)

From Stdlib Require Import List Arith Lia ZArith Bool.
Import ListNotations.

From Classifier Require Import Predicate.

Module Pathgen.
Import Predicate.
Local Open Scope nat_scope.

(** false = bit '0', true = bit '1'. *)
Definition PathCode := list bool.

Record Path := {
  path_code : PathCode;
  path_insns : list Insn
}.

Inductive GotoPolicy := GotoBpf | GotoRv32.

Inductive Ctrl :=
| CtrlCond : Condition -> nat -> Ctrl
| CtrlGoto : nat -> Ctrl
| CtrlExit : Ctrl
| CtrlTrap : Ctrl
| CtrlOther : Ctrl.

Definition resolve_target (index : nat) (off : JumpOff) : option nat :=
  let t := (Z.of_nat index + 1 + off)%Z in
  if Z.ltb t 0%Z then None else Some (Z.to_nat t).

Definition classify_prefix (index : nat) (pfx : Prefix) : option Ctrl :=
  fold_left
    (fun acc n =>
       match n.(node_pred) with
       | PIfGoto c off =>
           match resolve_target index off with
           | Some tgt => Some (CtrlCond c tgt)
           | None => None
           end
       | PGoto off =>
           match resolve_target index off with
           | Some tgt => Some (CtrlGoto tgt)
           | None => None
           end
       | PExit => Some CtrlExit
       | PTrap => Some CtrlTrap
       | _ => acc
       end)
    pfx
    (Some CtrlOther).

Definition classify (i : Insn) : option Ctrl :=
  classify_prefix i.(insn_index) i.(insn_prefix).

Fixpoint find_pos_from (prog : Program) (idx pos : nat) : option nat :=
  match prog with
  | [] => None
  | i :: rest =>
      if Nat.eqb i.(insn_index) idx then Some pos
      else find_pos_from rest idx (S pos)
  end.

Definition find_pos (prog : Program) (idx : nat) : option nat :=
  find_pos_from prog idx 0%nat.

Definition nth_insn (prog : Program) (pos : nat) : option Insn :=
  nth_error prog pos.

Definition next_pos (prog : Program) (pos : nat) : option nat :=
  let n := S pos in
  if Nat.ltb n (length prog) then Some n else None.

(** Mirror Rust's [replace_if_with_assert]: preserve non-control predicates,
    replace the first [PIfGoto], discard any later [PIfGoto], and append an
    assertion when no conditional was present. *)
Fixpoint replace_if_with_assert
  (prefix : Prefix) (c : Condition) (expected : bool) (id : PredicateId)
  (replaced : bool) : Prefix :=
  match prefix with
  | [] =>
      if replaced then []
      else [{| node_id := id; node_pred := PAssert c expected |}]
  | node :: rest =>
      match node.(node_pred) with
      | PIfGoto _ _ =>
          if replaced then
            replace_if_with_assert rest c expected id true
          else
            {| node_id := id; node_pred := PAssert c expected |}
              :: replace_if_with_assert rest c expected id true
      | _ =>
          node :: replace_if_with_assert rest c expected id replaced
      end
  end.

Definition assert_insn
  (i : Insn) (c : Condition) (expected : bool) (id : PredicateId) : Insn :=
  {| insn_index := i.(insn_index);
     insn_machine := i.(insn_machine);
     insn_prefix :=
       replace_if_with_assert i.(insn_prefix) c expected id false |}.

Definition machine_at_index (prog : Program) (idx : nat) : option Machine :=
  match find_pos prog idx with
  | None => None
  | Some pos =>
      match nth_insn prog pos with
      | None => None
      | Some i => Some i.(insn_machine)
      end
  end.

Fixpoint expand_fuel
  (fuel : nat)
  (prog : Program)
  (policy : GotoPolicy)
  (pos : nat)
  (code : PathCode)
  (acc : list Insn)
  (next_id : PredicateId)
  : option (list Path) :=
  match fuel with
  | O => None
  | S fuel' =>
      match nth_insn prog pos with
      | None => None
      | Some insn =>
          match classify insn with
          | None => None
          | Some CtrlExit =>
              Some [{| path_code := code; path_insns := acc ++ [insn] |}]
          | Some CtrlTrap => None
          | Some (CtrlCond c target) =>
              if Nat.ltb insn.(insn_index) target then
                match find_pos prog target with
                | None => None
                | Some taken_pos =>
                    match
                      expand_fuel fuel' prog policy taken_pos
                        (code ++ [true])
                        (acc ++ [assert_insn insn c true next_id])
                        (S next_id)
                    with
                    | None => None
                    | Some taken_paths =>
                        match next_pos prog pos with
                        | None => None
                        | Some fall_pos =>
                            match
                              expand_fuel fuel' prog policy fall_pos
                                (code ++ [false])
                                (acc ++ [assert_insn insn c false (S next_id)])
                                (S (S next_id))
                            with
                            | None => None
                            | Some fall_paths =>
                                Some (taken_paths ++ fall_paths)
                            end
                        end
                    end
                end
              else
                match next_pos prog pos with
                | None =>
                    Some [{| path_code := code; path_insns := acc ++ [insn] |}]
                | Some npos =>
                    expand_fuel fuel' prog policy npos code
                      (acc ++ [insn]) next_id
                end
          | Some (CtrlGoto target) =>
              match policy with
              | GotoBpf =>
                  if Nat.ltb insn.(insn_index) target then
                    match find_pos prog target with
                    | None => None
                    | Some tgt =>
                        expand_fuel fuel' prog policy tgt code
                          (acc ++ [insn]) next_id
                    end
                  else
                    match next_pos prog pos with
                    | None =>
                        Some [{| path_code := code;
                                 path_insns := acc ++ [insn] |}]
                    | Some npos =>
                        expand_fuel fuel' prog policy npos code
                          (acc ++ [insn]) next_id
                    end
              | GotoRv32 =>
                  match find_pos prog target with
                  | None => None
                  | Some tgt =>
                      expand_fuel fuel' prog policy tgt code
                        (acc ++ [insn]) next_id
                  end
              end
          | Some CtrlOther =>
              match next_pos prog pos with
              | None =>
                  Some [{| path_code := code; path_insns := acc ++ [insn] |}]
              | Some npos =>
                  expand_fuel fuel' prog policy npos code
                    (acc ++ [insn]) next_id
              end
          end
      end
  end.

Definition pathgen
  (prog : Program) (policy : GotoPolicy) (entry_pos : nat) (fuel : nat)
  : option (list Path) :=
  match prog with
  | [] => None
  | _ =>
      if Nat.ltb entry_pos (length prog) then
        expand_fuel fuel prog policy entry_pos [false] [] 0
      else None
  end.

Definition pathgen_bpf (prog : Program) (fuel : nat) : option (list Path) :=
  pathgen prog GotoBpf 0 fuel.

Definition pathgen_rv32 (prog : Program) (entry_pos : nat) (fuel : nat)
  : option (list Path) :=
  pathgen prog GotoRv32 entry_pos fuel.

(** Well-formed program table: unique instruction indices. *)
Definition unique_indices (prog : Program) : Prop :=
  forall i j a b,
    nth_error prog i = Some a ->
    nth_error prog j = Some b ->
    a.(insn_index) = b.(insn_index) ->
    i = j.

Definition insn_from_prog (prog : Program) (i : Insn) : Prop :=
  machine_at_index prog i.(insn_index) = Some i.(insn_machine).

Definition path_machines_ok (prog : Program) (paths : list Path) : Prop :=
  forall p, In p paths ->
  forall i, In i p.(path_insns) ->
    insn_from_prog prog i.

Definition codes_start_with_zero (paths : list Path) : Prop :=
  forall p, In p paths ->
    exists rest, p.(path_code) = false :: rest.

Lemma assert_insn_index_machine :
  forall i c e id,
    (assert_insn i c e id).(insn_index) = i.(insn_index)
    /\ (assert_insn i c e id).(insn_machine) = i.(insn_machine).
Proof. intros; split; reflexivity. Qed.

Lemma assert_insn_from_prog :
  forall prog i c e id,
    insn_from_prog prog i ->
    insn_from_prog prog (assert_insn i c e id).
Proof.
  intros prog i c e id H.
  unfold insn_from_prog in *.
  destruct (assert_insn_index_machine i c e id) as [Hi Hm].
  rewrite Hi, Hm. exact H.
Qed.

Lemma find_pos_eq : forall prog idx,
  find_pos prog idx = find_pos_from prog idx 0.
Proof. reflexivity. Qed.

(** Direct characterization kept as [find_pos_from]; [find_pos] is the entry. *)

Lemma find_pos_from_nth :
  forall prog idx pos0 pos insn,
    unique_indices prog ->
    nth_error prog pos = Some insn ->
    insn.(insn_index) = idx ->
    find_pos_from prog idx pos0 = Some (pos0 + pos).
Proof.
  intros prog idx pos0 pos insn Huniq.
  revert prog pos0 pos insn Huniq.
  induction prog as [|a rest IH]; intros pos0 pos insn Huniq Hn Hi.
  - destruct pos; simpl in Hn; discriminate.
  - destruct pos as [|pos']; simpl in Hn.
    + inversion Hn; subst a; clear Hn.
      simpl. rewrite Hi. rewrite Nat.eqb_refl.
      rewrite Nat.add_0_r. reflexivity.
    + simpl.
      destruct (Nat.eqb a.(insn_index) idx) eqn:Heq.
      * apply Nat.eqb_eq in Heq.
        (* a and insn share index but different positions → contradict uniqueness *)
        assert (0 = S pos').
        {
          eapply Huniq.
          - simpl; reflexivity.
          - simpl; exact Hn.
          - rewrite Heq, Hi; reflexivity.
        }
        discriminate.
      * replace (pos0 + S pos') with (S pos0 + pos') by lia.
        eapply IH; [|exact Hn|exact Hi].
        intros i j x y Hx Hy Heqidx.
        assert (S i = S j).
        {
          eapply Huniq.
          - simpl; exact Hx.
          - simpl; exact Hy.
          - exact Heqidx.
        }
        lia.
Qed.

Lemma nth_insn_from_prog :
  forall prog pos insn,
    unique_indices prog ->
    nth_error prog pos = Some insn ->
    insn_from_prog prog insn.
Proof.
  intros prog pos insn Huniq Hn.
  unfold insn_from_prog, machine_at_index, nth_insn.
  rewrite find_pos_eq.
  rewrite (find_pos_from_nth prog insn.(insn_index) 0%nat pos insn Huniq Hn eq_refl).
  rewrite Nat.add_0_l.
  rewrite Hn. reflexivity.
Qed.

Lemma in_acc_cons_app :
  forall (A : Type) (acc : list A) (x : A) (y : A),
    In y (acc ++ [x]) -> In y acc \/ y = x.
Proof.
  intros A acc x y H.
  apply in_app_or in H.
  destruct H as [H|[H|[]]]; auto.
Qed.

Lemma expand_fuel_machines :
  forall fuel prog policy pos code acc next_id paths,
    unique_indices prog ->
    expand_fuel fuel prog policy pos code acc next_id = Some paths ->
    (forall i, In i acc -> insn_from_prog prog i) ->
    path_machines_ok prog paths.
Proof.
  induction fuel as [|fuel IH];
    intros prog policy pos code acc next_id paths Huniq Hexp Hacc.
  - discriminate.
  - simpl in Hexp.
    destruct (nth_insn prog pos) as [insn|] eqn:Hinsn; [|discriminate].
    assert (Hinsn_ok : insn_from_prog prog insn)
      by (unfold nth_insn in Hinsn; eapply nth_insn_from_prog; eauto).
    destruct (classify insn) as [ctrl|] eqn:Hcls; [|discriminate].
    destruct ctrl as [c target|target| | |].
    + destruct (Nat.ltb insn.(insn_index) target) eqn:Hfwd.
      * destruct (find_pos prog target) as [taken_pos|] eqn:Htp; [|discriminate].
        destruct (expand_fuel fuel prog policy taken_pos (code ++ [true])
                    (acc ++ [assert_insn insn c true next_id]) (S next_id))
          as [taken_paths|] eqn:Htaken; [|discriminate].
        destruct (next_pos prog pos) as [fall_pos|] eqn:Hfp; [|discriminate].
        destruct (expand_fuel fuel prog policy fall_pos (code ++ [false])
                    (acc ++ [assert_insn insn c false (S next_id)]) (S (S next_id)))
          as [fall_paths|] eqn:Hfall; [|discriminate].
        inversion Hexp; subst paths; clear Hexp.
        unfold path_machines_ok.
        intros p Hinp i Hini.
        apply in_app_or in Hinp; destruct Hinp as [Hinp|Hinp].
        -- eapply IH with (acc := acc ++ [assert_insn insn c true next_id]); eauto.
           intros j Hj. apply in_acc_cons_app in Hj.
           destruct Hj as [Hj|Hj]; [apply Hacc; exact Hj|].
           subst j. apply assert_insn_from_prog; exact Hinsn_ok.
        -- eapply IH with (acc := acc ++ [assert_insn insn c false (S next_id)]); eauto.
           intros j Hj. apply in_acc_cons_app in Hj.
           destruct Hj as [Hj|Hj]; [apply Hacc; exact Hj|].
           subst j. apply assert_insn_from_prog; exact Hinsn_ok.
      * destruct (next_pos prog pos) as [npos|] eqn:Hn.
        -- eapply IH; [exact Huniq|exact Hexp|].
           intros j Hj. apply in_acc_cons_app in Hj.
           destruct Hj as [Hj|Hj]; [apply Hacc; exact Hj|subst j; exact Hinsn_ok].
        -- inversion Hexp; subst paths.
           unfold path_machines_ok.
           intros p Hinp i Hini.
           destruct Hinp as [Hinp|[]]; subst p; simpl in Hini.
           apply in_acc_cons_app in Hini.
           destruct Hini as [Hini|Hini]; [apply Hacc; exact Hini|subst i; exact Hinsn_ok].
    + destruct policy.
      * destruct (Nat.ltb insn.(insn_index) target) eqn:Hfwd.
        -- destruct (find_pos prog target) as [tgt|] eqn:Ht; [|discriminate].
           eapply IH; [exact Huniq|exact Hexp|].
           intros j Hj. apply in_acc_cons_app in Hj.
           destruct Hj as [Hj|Hj]; [apply Hacc; exact Hj|subst j; exact Hinsn_ok].
        -- destruct (next_pos prog pos) as [npos|] eqn:Hn.
           ++ eapply IH; [exact Huniq|exact Hexp|].
              intros j Hj. apply in_acc_cons_app in Hj.
              destruct Hj as [Hj|Hj]; [apply Hacc; exact Hj|subst j; exact Hinsn_ok].
           ++ inversion Hexp; subst paths.
              unfold path_machines_ok.
              intros p Hinp i Hini.
              destruct Hinp as [Hinp|[]]; subst p; simpl in Hini.
              apply in_acc_cons_app in Hini.
              destruct Hini as [Hini|Hini]; [apply Hacc; exact Hini|subst i; exact Hinsn_ok].
      * destruct (find_pos prog target) as [tgt|] eqn:Ht; [|discriminate].
        eapply IH; [exact Huniq|exact Hexp|].
        intros j Hj. apply in_acc_cons_app in Hj.
        destruct Hj as [Hj|Hj]; [apply Hacc; exact Hj|subst j; exact Hinsn_ok].
    + inversion Hexp; subst paths.
      unfold path_machines_ok.
      intros p Hinp i Hini.
      destruct Hinp as [Hinp|[]]; subst p; simpl in Hini.
      apply in_acc_cons_app in Hini.
      destruct Hini as [Hini|Hini]; [apply Hacc; exact Hini|subst i; exact Hinsn_ok].
    + discriminate.
    + destruct (next_pos prog pos) as [npos|] eqn:Hn.
      * eapply IH; [exact Huniq|exact Hexp|].
        intros j Hj. apply in_acc_cons_app in Hj.
        destruct Hj as [Hj|Hj]; [apply Hacc; exact Hj|subst j; exact Hinsn_ok].
      * inversion Hexp; subst paths.
        unfold path_machines_ok.
        intros p Hinp i Hini.
        destruct Hinp as [Hinp|[]]; subst p; simpl in Hini.
        apply in_acc_cons_app in Hini.
        destruct Hini as [Hini|Hini]; [apply Hacc; exact Hini|subst i; exact Hinsn_ok].
Qed.

Lemma expand_fuel_codes_zero :
  forall fuel prog policy pos code acc next_id paths,
    expand_fuel fuel prog policy pos code acc next_id = Some paths ->
    (exists rest, code = false :: rest) ->
    codes_start_with_zero paths.
Proof.
  induction fuel as [|fuel IH];
    intros prog policy pos code acc next_id paths Hexp Hcode.
  - discriminate.
  - simpl in Hexp.
    destruct (nth_insn prog pos) as [insn|]; [|discriminate].
    destruct (classify insn) as [ctrl|]; [|discriminate].
    destruct ctrl as [c target|target| | |].
    + destruct (Nat.ltb insn.(insn_index) target).
      * destruct (find_pos prog target) as [taken_pos|]; [|discriminate].
        destruct (expand_fuel fuel prog policy taken_pos (code ++ [true])
                    (acc ++ [assert_insn insn c true next_id]) (S next_id))
          as [taken_paths|] eqn:Htaken; [|discriminate].
        destruct (next_pos prog pos) as [fall_pos|]; [|discriminate].
        destruct (expand_fuel fuel prog policy fall_pos (code ++ [false])
                    (acc ++ [assert_insn insn c false (S next_id)]) (S (S next_id)))
          as [fall_paths|] eqn:Hfall; [|discriminate].
        inversion Hexp; subst paths; clear Hexp.
        unfold codes_start_with_zero.
        intros p Hinp.
        apply in_app_or in Hinp; destruct Hinp as [Hinp|Hinp].
        -- eapply IH; [exact Htaken| |exact Hinp].
           destruct Hcode as [rest Hr]; subst code.
           exists (rest ++ [true]); reflexivity.
        -- eapply IH; [exact Hfall| |exact Hinp].
           destruct Hcode as [rest Hr]; subst code.
           exists (rest ++ [false]); reflexivity.
      * destruct (next_pos prog pos).
        -- eapply IH; eauto.
        -- inversion Hexp; subst paths.
           unfold codes_start_with_zero.
           intros p Hinp. destruct Hinp as [Hinp|[]]; subst p.
           simpl. exact Hcode.
    + destruct policy.
      * destruct (Nat.ltb insn.(insn_index) target).
        -- destruct (find_pos prog target); [|discriminate].
           eapply IH; eauto.
        -- destruct (next_pos prog pos).
           ++ eapply IH; eauto.
           ++ inversion Hexp; subst paths.
              unfold codes_start_with_zero.
              intros p Hinp. destruct Hinp as [Hinp|[]]; subst p.
              simpl. exact Hcode.
      * destruct (find_pos prog target); [|discriminate].
        eapply IH; eauto.
    + inversion Hexp; subst paths.
      unfold codes_start_with_zero.
      intros p Hinp. destruct Hinp as [Hinp|[]]; subst p.
      simpl. exact Hcode.
    + discriminate.
    + destruct (next_pos prog pos).
      * eapply IH; eauto.
      * inversion Hexp; subst paths.
        unfold codes_start_with_zero.
        intros p Hinp. destruct Hinp as [Hinp|[]]; subst p.
        simpl. exact Hcode.
Qed.

Theorem pathgen_preserves_machines :
  forall prog policy entry fuel paths,
    unique_indices prog ->
    pathgen prog policy entry fuel = Some paths ->
    path_machines_ok prog paths.
Proof.
  intros prog policy entry fuel paths Huniq H.
  unfold pathgen in H.
  destruct prog as [|i rest] eqn:Hp; [discriminate|].
  destruct (Nat.ltb entry (length (i :: rest))) eqn:He; [|discriminate].
  eapply expand_fuel_machines; [exact Huniq|exact H|].
  intros j Hj; destruct Hj.
Qed.

Theorem pathgen_codes_start_with_zero :
  forall prog policy entry fuel paths,
    pathgen prog policy entry fuel = Some paths ->
    codes_start_with_zero paths.
Proof.
  intros prog policy entry fuel paths H.
  unfold pathgen in H.
  destruct prog; [discriminate|].
  destruct (Nat.ltb entry (length (_ :: _))); [|discriminate].
  eapply expand_fuel_codes_zero; [exact H|].
  exists []; reflexivity.
Qed.

Module Tests.

Definition cond_eq0 : Condition :=
  {| cond_lhs := OReg (Rw 1);
     cond_op := CEq;
     cond_rhs := OImm (Bv32 0) |}.

Definition mk (idx : nat) (m : Machine) (p : Predicate) : Insn :=
  {| insn_index := idx;
     insn_machine := m;
     insn_prefix := singleton_prefix idx p |}.

(** Forward if at 0 → 2; taken then fallthrough. *)
Example forward_if_codes :
  let prog :=
    [mk 0 (MRv32 1) (PIfGoto cond_eq0 1%Z);
     mk 1 (MRv32 2) (PSet (Rw 0) (OImm (Bv32 1)));
     mk 2 (MRv32 3) PExit] in
  match pathgen_bpf prog 32 with
  | Some paths =>
      List.map path_code paths = [false :: [true]; false :: [false]]
      /\ List.length paths = 2%nat
  | None => False
  end.
Proof. simpl. split; reflexivity. Qed.

Example forward_if_machines :
  let prog :=
    [mk 0 (MRv32 1) (PIfGoto cond_eq0 1%Z);
     mk 1 (MRv32 2) (PSet (Rw 0) (OImm (Bv32 1)));
     mk 2 (MRv32 3) PExit] in
  match pathgen_bpf prog 32 with
  | Some paths =>
      match paths with
      | p0 :: p1 :: [] =>
          match p0.(path_insns), p1.(path_insns) with
          | a0 :: _, b0 :: _ =>
              a0.(insn_machine) = MRv32 1
              /\ b0.(insn_machine) = MRv32 1
              /\ match a0.(insn_prefix), b0.(insn_prefix) with
                 | [{| node_pred := PAssert _ true |}],
                   [{| node_pred := PAssert _ false |}] => True
                 | _, _ => False
                 end
          | _, _ => False
          end
      | _ => False
      end
  | None => False
  end.
Proof. simpl. repeat split. Qed.

Example forward_if_preserves_non_control_predicates :
  let set_node :=
    {| node_id := 7%nat;
       node_pred := PSet (Rw 0) (OImm (Bv32 1)) |} in
  let if_node :=
    {| node_id := 8%nat;
       node_pred := PIfGoto cond_eq0 1%Z |} in
  let input :=
    {| insn_index := 0%nat;
       insn_machine := MRv32 1;
       insn_prefix := [set_node; if_node] |} in
  (assert_insn input cond_eq0 true 9).(insn_prefix) =
    [set_node;
     {| node_id := 9%nat; node_pred := PAssert cond_eq0 true |}].
Proof. reflexivity. Qed.

Example no_branch_code_zero :
  let prog := [mk 0 (MBpf 9) PExit] in
  match pathgen_bpf prog 8 with
  | Some [p] => p.(path_code) = [false]
  | _ => False
  end.
Proof. reflexivity. Qed.

End Tests.

End Pathgen.
