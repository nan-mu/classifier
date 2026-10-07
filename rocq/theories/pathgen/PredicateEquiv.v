(** * Predicate-led path equivalence.

    This file is intentionally separate from [Functional.v].  It states the
    predicate-level proposition that the external QF_BV query must decide; it
    does not model an SMT solver, certificates, SMT-LIB parsing, or process
    invocation.  Those operational concerns belong to the Rust driver and the
    standalone CoqQFBV executable.

    Non-assert predicates remain available in [history] so a later symbolic
    evaluator can determine the value observed by an assertion.  They are not
    themselves declared to be cross-ISA observations here. *)

From Stdlib Require Import Bool List.
Import ListNotations.

From Classifier Require Import Predicate.
From Classifier Require Import pathgen.Base.

Module PredicateEquiv.
Import Predicate.
Import Pathgen.

Section PredicateBehavior.

  Context {Valuation : Type}.

  (** [history] is newest-first.  A concrete stage supplies the symbolic
      interpretation of the preceding predicates. *)
  Variable eval_condition :
    Prefix -> PredicateId -> Condition -> Valuation -> bool.

  Definition eval_assert_node
    (history : Prefix) (node : PredicateNode) (valuation : Valuation) : bool :=
    match node.(node_pred) with
    | PAssert condition expected =>
        Bool.eqb
          (eval_condition history node.(node_id) condition valuation)
          expected
    | _ => true
    end.

  Fixpoint eval_nodes_asserts
    (history nodes : Prefix) (valuation : Valuation) : bool :=
    match nodes with
    | [] => true
    | node :: rest =>
        andb (eval_assert_node history node valuation)
             (eval_nodes_asserts (node :: history) rest valuation)
    end.

  Definition path_nodes (path : Path) : Prefix :=
    flat_map insn_prefix path.(path_insns).

  Definition eval_path_asserts (path : Path) (valuation : Valuation) : bool :=
    eval_nodes_asserts [] (path_nodes path) valuation.

  (** The reviewer-facing cross-ISA claim for this layer: under the shared
      input/environment contract, the selected assertion behavior agrees.
      It says nothing about unobserved machine effects. *)
  Definition path_assert_equiv
    (contract : Valuation -> bool) (left right : Path) : Prop :=
    forall valuation,
      contract valuation = true ->
      eval_path_asserts left valuation = eval_path_asserts right valuation.

  (** This is the Boolean counterexample expression that the Rust goal
      generator should serialize as QF_BV: contract /\ (left xor right). *)
  Definition inequivalence_obligation
    (contract : Valuation -> bool) (left right : Path)
    (valuation : Valuation) : bool :=
    andb (contract valuation)
      (xorb (eval_path_asserts left valuation)
            (eval_path_asserts right valuation)).

  Theorem no_counterexample_iff_path_assert_equiv :
    forall contract left right,
      (forall valuation,
         inequivalence_obligation contract left right valuation = false) <->
      path_assert_equiv contract left right.
  Proof.
    intros contract left right.
    split.
    - intros Hnone valuation Hcontract.
      specialize (Hnone valuation).
      unfold inequivalence_obligation in Hnone.
      rewrite Hcontract in Hnone.
      cbn in Hnone.
      destruct (eval_path_asserts left valuation),
               (eval_path_asserts right valuation);
        cbn in Hnone |-; try reflexivity; discriminate.
    - intros Hequiv valuation.
      unfold inequivalence_obligation.
      destruct (contract valuation) eqn:Hcontract; cbn; [|reflexivity].
      specialize (Hequiv valuation Hcontract).
      destruct (eval_path_asserts left valuation),
               (eval_path_asserts right valuation);
        cbn in Hequiv |-; try reflexivity; discriminate.
  Qed.

  (** XDP may strengthen the counterexample with differences in intermediate
      observations needed to justify an assertion (currently MapLookup map/key
      arguments).  Proving this larger disjunction impossible still proves the
      original assertion-only proposition. *)
  Definition strengthened_inequivalence_obligation
    (contract : Valuation -> bool) (left right : Path)
    (extra_difference : Valuation -> bool) (valuation : Valuation) : bool :=
    andb (contract valuation)
      (orb
        (xorb (eval_path_asserts left valuation)
              (eval_path_asserts right valuation))
        (extra_difference valuation)).

  Theorem no_strengthened_counterexample_implies_path_assert_equiv :
    forall contract left right extra_difference,
      (forall valuation,
         strengthened_inequivalence_obligation
           contract left right extra_difference valuation = false) ->
      path_assert_equiv contract left right.
  Proof.
    intros contract left right extra_difference Hnone.
    apply (proj1 (no_counterexample_iff_path_assert_equiv contract left right)).
    intros valuation.
    specialize (Hnone valuation).
    unfold strengthened_inequivalence_obligation in Hnone.
    unfold inequivalence_obligation.
    destruct (contract valuation); cbn in Hnone |-; [|reflexivity].
    destruct (xorb (eval_path_asserts left valuation)
                   (eval_path_asserts right valuation));
      cbn in Hnone |-; [discriminate|reflexivity].
  Qed.

  (** Equality of path codes is not part of the semantic claim.  Different
      compiler branch orders may assign different Huffman codes to paths with
      the same assertion behavior.  A proof artifact therefore carries an
      explicit, duplicate-free matching. *)
  Definition matching_shape
    (left right : list Path) (matching : list (Path * Path)) : Prop :=
    (forall l r, In (l, r) matching -> In l left /\ In r right) /\
    NoDup left /\
    NoDup right /\
    NoDup (map fst matching) /\
    NoDup (map snd matching) /\
    (forall l, In l left -> In l (map fst matching)) /\
    (forall r, In r right -> In r (map snd matching)).

  (** Path families agree as sets of selected assertion behaviors.  This is
      deliberately weaker than whole-program or whole-machine equivalence. *)
  Definition path_family_assert_equiv
    (contract : Valuation -> bool) (left right : list Path) : Prop :=
    (forall l, In l left ->
       exists r, In r right /\ path_assert_equiv contract l r) /\
    (forall r, In r right ->
       exists l, In l left /\ path_assert_equiv contract l r).

  (** Reviewer-facing composition theorem.  The structural matching is
      checkable without a solver; each semantic edge is justified by the
      absence of a valuation satisfying its inequivalence obligation. *)
  Theorem no_counterexample_matching_implies_family_equiv :
    forall contract left right matching,
      matching_shape left right matching ->
      (forall l r,
         In (l, r) matching ->
         forall valuation,
           inequivalence_obligation contract l r valuation = false) ->
      path_family_assert_equiv contract left right.
  Proof.
    intros contract left right matching Hshape Hnone.
    destruct Hshape as [Hmembers [_ [_ [_ [_ [Hleft Hright]]]]]].
    split.
    - intros l Hin.
      specialize (Hleft l Hin).
      apply in_map_iff in Hleft.
      destruct Hleft as [[l' r] [Heq Hpair]].
      cbn in Heq. subst l'.
      exists r.
      split.
      + exact (proj2 (Hmembers l r Hpair)).
      + apply (proj1 (no_counterexample_iff_path_assert_equiv contract l r)).
        exact (Hnone l r Hpair).
    - intros r Hin.
      specialize (Hright r Hin).
      apply in_map_iff in Hright.
      destruct Hright as [[l r'] [Heq Hpair]].
      cbn in Heq. subst r'.
      exists l.
      split.
      + exact (proj1 (Hmembers l r Hpair)).
      + apply (proj1 (no_counterexample_iff_path_assert_equiv contract l r)).
        exact (Hnone l r Hpair).
  Qed.

  Theorem no_strengthened_matching_implies_family_equiv :
    forall contract left right matching extra_difference,
      matching_shape left right matching ->
      (forall l r,
         In (l, r) matching ->
         forall valuation,
           strengthened_inequivalence_obligation
             contract l r (extra_difference l r) valuation = false) ->
      path_family_assert_equiv contract left right.
  Proof.
    intros contract left right matching extra_difference Hshape Hnone.
    apply (no_counterexample_matching_implies_family_equiv
             contract left right matching Hshape).
    intros l r Hpair valuation.
    pose proof
      (no_strengthened_counterexample_implies_path_assert_equiv
         contract l r (extra_difference l r) (Hnone l r Hpair)) as Hequiv.
    exact ((proj2 (no_counterexample_iff_path_assert_equiv contract l r))
             Hequiv valuation).
  Qed.

End PredicateBehavior.

End PredicateEquiv.
