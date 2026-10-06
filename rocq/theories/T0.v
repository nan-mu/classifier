(** * T0: forward control-path expansion.

    Matches [src/bpf/t0.rs]: taken paths before fallthrough; forward [ICond]
    becomes [LAssert]; backward control is kept and not followed.
*)

From Coq Require Import Arith Bool List Lia.
Import ListNotations.
From Classifier Require Import Syntax Prog T0Input.

Module T0.
Import Syntax Prog T0Input.

(** Append one line to a prefix. *)
Definition snoc (prefix : path) (l : path_line) : path :=
  prefix ++ [l].

(** Fuel-bounded expansion. Fuel decreases on every recursive call; callers
    pass [List.length p - pos] (or any larger amount). *)
Fixpoint expand (fuel : nat) (p : prog) (pos : nat) (prefix : path) : paths :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match nth_error p pos with
      | None => []
      | Some (i, ins) =>
          match ins with
          | IExit =>
              [snoc prefix (LInsn i IExit)]
          | IOther body =>
              let prefix' := snoc prefix (LInsn i (IOther body)) in
              match next_pos p pos with
              | None => [prefix']
              | Some n => expand fuel' p n prefix'
              end
          | IGoto tgt =>
              let prefix' := snoc prefix (LInsn i (IGoto tgt)) in
              if Nat.ltb i tgt then
                match find_pos p tgt with
                | None => [prefix']
                | Some tpos => expand fuel' p tpos prefix'
                end
              else
                match next_pos p pos with
                | None => [prefix']
                | Some n => expand fuel' p n prefix'
                end
          | ICond e tgt =>
              if Nat.ltb i tgt then
                (* forward conditional: assert true then false *)
                let taken_prefix := snoc prefix (LAssert i e true) in
                let fall_prefix := snoc prefix (LAssert i e false) in
                let taken_paths :=
                  match find_pos p tgt with
                  | None => []
                  | Some tpos => expand fuel' p tpos taken_prefix
                  end
                in
                let fall_paths :=
                  match next_pos p pos with
                  | None => []
                  | Some n => expand fuel' p n fall_prefix
                  end
                in
                taken_paths ++ fall_paths
              else
                (* backward: keep [if], linear next only *)
                let prefix' := snoc prefix (LInsn i (ICond e tgt)) in
                match next_pos p pos with
                | None => [prefix']
                | Some n => expand fuel' p n prefix'
                end
          end
      end
  end.

Definition t0 (p : prog) : paths :=
  expand (List.length p) p 0 [].

(** Inductive characterization (for proofs). *)
Inductive Expand (p : prog) : nat -> path -> paths -> Prop :=
| E_Exit :
    forall pos prefix i,
      nth_error p pos = Some (i, IExit) ->
      Expand p pos prefix [snoc prefix (LInsn i IExit)]
| E_Other_end :
    forall pos prefix i body,
      nth_error p pos = Some (i, IOther body) ->
      next_pos p pos = None ->
      Expand p pos prefix [snoc prefix (LInsn i (IOther body))]
| E_Other_step :
    forall pos prefix i body n ps,
      nth_error p pos = Some (i, IOther body) ->
      next_pos p pos = Some n ->
      Expand p n (snoc prefix (LInsn i (IOther body))) ps ->
      Expand p pos prefix ps
| E_Goto_fwd :
    forall pos prefix i tgt tpos ps,
      nth_error p pos = Some (i, IGoto tgt) ->
      i < tgt ->
      find_pos p tgt = Some tpos ->
      Expand p tpos (snoc prefix (LInsn i (IGoto tgt))) ps ->
      Expand p pos prefix ps
| E_Goto_bwd_end :
    forall pos prefix i tgt,
      nth_error p pos = Some (i, IGoto tgt) ->
      tgt <= i ->
      next_pos p pos = None ->
      Expand p pos prefix [snoc prefix (LInsn i (IGoto tgt))]
| E_Goto_bwd_step :
    forall pos prefix i tgt n ps,
      nth_error p pos = Some (i, IGoto tgt) ->
      tgt <= i ->
      next_pos p pos = Some n ->
      Expand p n (snoc prefix (LInsn i (IGoto tgt))) ps ->
      Expand p pos prefix ps
| E_Cond_fwd :
    forall pos prefix i e tgt tpos n ps_t ps_f,
      nth_error p pos = Some (i, ICond e tgt) ->
      i < tgt ->
      find_pos p tgt = Some tpos ->
      next_pos p pos = Some n ->
      Expand p tpos (snoc prefix (LAssert i e true)) ps_t ->
      Expand p n (snoc prefix (LAssert i e false)) ps_f ->
      Expand p pos prefix (ps_t ++ ps_f)
| E_Cond_bwd_end :
    forall pos prefix i e tgt,
      nth_error p pos = Some (i, ICond e tgt) ->
      tgt <= i ->
      next_pos p pos = None ->
      Expand p pos prefix [snoc prefix (LInsn i (ICond e tgt))]
| E_Cond_bwd_step :
    forall pos prefix i e tgt n ps,
      nth_error p pos = Some (i, ICond e tgt) ->
      tgt <= i ->
      next_pos p pos = Some n ->
      Expand p n (snoc prefix (LInsn i (ICond e tgt))) ps ->
      Expand p pos prefix ps.

(** Coverage for left inverse: each instruction is witnessed on some path
    in the form restore needs — [LInsn] for non-forward-cond, and
    [LAssert _ _ true] for forward [ICond] (so restore can rebuild [tgt]). *)
Definition covers_insn (ps : paths) (i : index) (ins : insn) : Prop :=
  match ins with
  | ICond e tgt =>
      if Nat.ltb i tgt then
        exists ph, In ph ps /\ In (LAssert i e true) ph
      else
        exists ph, In ph ps /\ In (LInsn i ins) ph
  | _ =>
      exists ph, In ph ps /\ In (LInsn i ins) ph
  end.

Definition covers_all (p : prog) (ps : paths) : Prop :=
  forall i ins, In (i, ins) p -> covers_insn ps i ins.

(** Legal T0 input for left inverse: structural WF + expansion covers all. *)
Definition T0Input (p : prog) : Prop :=
  T0Input_struct p /\
  covers_all p (t0 p).

End T0.
