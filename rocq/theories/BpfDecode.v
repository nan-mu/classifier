(** * BPF word → Prefix — mirrors [src/prefixgen/bpf_decode.rs]. *)

From Stdlib Require Import List NArith ZArith Bool Lia.
Import ListNotations.
Open Scope N_scope.

From Classifier Require Import Predicate Raw.

Module BpfDecode.
Import Predicate Raw.

Definition word_code (w : N) : N := N.land w 0xff.
Definition word_dst  (w : N) : N := N.land (N.shiftr w 8) 0xf.
Definition word_src  (w : N) : N := N.land (N.shiftr w 12) 0xf.
Definition word_off_u (w : N) : N := N.land (N.shiftr w 16) 0xffff.
Definition word_imm_u (w : N) : N := N.land (N.shiftr w 32) 0xffffffff.

Definition n_to_nat (n : N) : nat := N.to_nat n.

Definition to_u64 (z : Z) : N :=
  Z.to_N (Z.modulo z (Z.pow 2 64)).

Definition word_off_s (w : N) : Z :=
  let u := word_off_u w in
  if N.ltb u 0x8000 then Z.of_N u
  else (Z.of_N u - Z.pow 2 16)%Z.

Definition imm32_as_N (w : N) : N := word_imm_u w.

Definition imm32_as_u64_sext (w : N) : N :=
  let u := word_imm_u w in
  let z :=
    if N.ltb u 0x80000000 then Z.of_N u
    else (Z.of_N u - Z.pow 2 32)%Z
  in
  to_u64 z.

Definition class_of (code : N) : N := N.land code 0x07.
Definition op_of (code : N) : N := N.land code 0xf0.
Definition size_of (code : N) : N := N.land code 0x18.
Definition mode_of (code : N) : N := N.land code 0xe0.
Definition src_reg_bit (code : N) : bool := negb (N.eqb (N.land code 0x08) 0).

Definition mem_width (size : N) : option MemWidth :=
  if N.eqb size 0x00 then Some U32
  else if N.eqb size 0x08 then Some U16
  else if N.eqb size 0x10 then Some U8
  else if N.eqb size 0x18 then Some U64
  else None.

Definition reg_w (n : N) : Reg := Rw (n_to_nat n).
Definition reg_r (n : N) : Reg := Rr (n_to_nat n).

Definition dst_reg_load (n : N) (width : MemWidth) : Reg :=
  match width with
  | U64 => reg_r n
  | _ => reg_w n
  end.

Definition address (base : N) (off : Z) : Address :=
  {| addr_base := reg_r base;
     addr_offset :=
       if Z.eqb off 0 then None
       else Some (Bv64 (to_u64 off)) |}.

Definition alu_op (op : N) : option AluOp :=
  if N.eqb op 0x00 then Some AAdd
  else if N.eqb op 0x10 then Some ASub
  else if N.eqb op 0x20 then Some AMul
  else if N.eqb op 0x30 then Some ADivu
  else if N.eqb op 0x40 then Some AOr
  else if N.eqb op 0x50 then Some AAnd
  else if N.eqb op 0x60 then Some AShl
  else if N.eqb op 0x70 then Some ALshr
  else if N.eqb op 0x90 then Some ARemu
  else if N.eqb op 0xa0 then Some AXor
  else if N.eqb op 0xc0 then Some AAshr
  else None.

Definition cmp_op (op : N) : option CmpOp :=
  if N.eqb op 0x10 then Some CEq
  else if N.eqb op 0x20 then Some CGt
  else if N.eqb op 0x30 then Some CGe
  else if N.eqb op 0x50 then Some CNe
  else if N.eqb op 0x60 then Some CSgt
  else if N.eqb op 0x70 then Some CSge
  else if N.eqb op 0xa0 then Some CLt
  else if N.eqb op 0xb0 then Some CLe
  else if N.eqb op 0xc0 then Some CSlt
  else if N.eqb op 0xd0 then Some CSle
  else None.

Definition decode_alu (is64 : bool) (op code dst src : N) (immw : N)
  : option Predicate :=
  let src_reg := src_reg_bit code in
  let d := if is64 then reg_r dst else reg_w dst in
  let rhs :=
    if src_reg then
      OReg (if is64 then reg_r src else reg_w src)
    else if is64 then
      OImm (Bv64 (imm32_as_u64_sext immw))
    else
      OImm (Bv32 (imm32_as_N immw))
  in
  if N.eqb op 0xb0 then Some (PSet d rhs)
  else if N.eqb op 0x80 then
    Some (PAlu d ASub
            (OImm (if is64 then Bv64 0 else Bv32 0))
            (OReg d))
  else
    match alu_op op with
    | Some a => Some (PAluAssign d a rhs)
    | None => None
    end.

Definition decode_jmp (is64 : bool) (op code dst src : N) (immw : N) (off : Z)
  : option Predicate :=
  if N.eqb op 0x80 then Some (PCall (imm32_as_N immw))
  else if N.eqb op 0x90 then Some PExit
  else if N.eqb op 0x00 then Some (PGoto off)
  else if N.eqb op 0x40 then None
  else
    let src_reg := src_reg_bit code in
    let lhs := OReg (if is64 then reg_r dst else reg_w dst) in
    let rhs :=
      if src_reg then
        OReg (if is64 then reg_r src else reg_w src)
      else if is64 then
        OImm (Bv64 (imm32_as_u64_sext immw))
      else
        OImm (Bv32 (imm32_as_N immw))
    in
    match cmp_op op with
    | Some c =>
        Some (PIfGoto {| cond_lhs := lhs; cond_op := c; cond_rhs := rhs |} off)
    | None => None
    end.

Definition decode_insn (w : N) (next : option N) : option (option Predicate * nat) :=
  let code := word_code w in
  let dst := word_dst w in
  let src := word_src w in
  let off := word_off_s w in
  let class := class_of code in
  let op := op_of code in
  let size := size_of code in
  let mode := mode_of code in
  if N.eqb class 0x00 then
    if (N.eqb size 0x18) && (N.eqb mode 0x00) then
      match next with
      | None => None
      | Some hi =>
          let imm64 := N.lor (imm32_as_N w) (N.shiftl (word_imm_u hi) 32) in
          Some (Some (PSet (reg_r dst) (OImm (Bv64 imm64))), 2%nat)
      end
    else None
  else if N.eqb class 0x01 then
    if N.eqb mode 0x60 then
      match mem_width size with
      | None => None
      | Some mw =>
          Some (Some (PLoad (dst_reg_load dst mw) mw (address src off)), 1%nat)
      end
    else None
  else if (N.eqb class 0x02) || (N.eqb class 0x03) then
    if N.eqb mode 0x60 then
      match mem_width size with
      | None => None
      | Some mw =>
          let src_op :=
            if N.eqb class 0x02 then OImm (Bv32 (imm32_as_N w))
            else OReg (dst_reg_load src mw)
          in
          Some (Some (PStore mw (address dst off) src_op), 1%nat)
      end
    else None
  else if N.eqb class 0x04 then
    match decode_alu false op code dst src w with
    | None => None
    | Some p => Some (Some p, 1%nat)
    end
  else if N.eqb class 0x05 then
    match decode_jmp true op code dst src w off with
    | None => None
    | Some p => Some (Some p, 1%nat)
    end
  else if N.eqb class 0x06 then
    match decode_jmp false op code dst src w off with
    | None => None
    | Some p => Some (Some p, 1%nat)
    end
  else if N.eqb class 0x07 then
    match decode_alu true op code dst src w with
    | None => None
    | Some p => Some (Some p, 1%nat)
    end
  else None.

Definition mk_insn (idx : nat) (w : N) (pref : Prefix) : Insn :=
  {| insn_index := idx; insn_machine := MBpf w; insn_prefix := pref |}.

Definition next_pid (po : option Predicate) (pid : nat) : nat :=
  match po with None => pid | Some _ => S pid end.

Definition pref_of (po : option Predicate) (pid : nat) : Prefix :=
  match po with
  | None => []
  | Some p => singleton_prefix pid p
  end.

Fixpoint prefixgen_bpf_words (raw : BpfRawProgram) (idx pid : nat)
  : option Program :=
  match raw with
  | [] => Some []
  | w :: rest =>
      match decode_insn w (match rest with [] => None | h :: _ => Some h end) with
      | None => None
      | Some (po, 1%nat) =>
          match prefixgen_bpf_words rest (S idx) (next_pid po pid) with
          | None => None
          | Some ps => Some (mk_insn idx w (pref_of po pid) :: ps)
          end
      | Some (po, 2%nat) =>
          match rest with
          | [] => None
          | cont :: rest' =>
              match prefixgen_bpf_words rest' (S (S idx)) (next_pid po pid) with
              | None => None
              | Some ps =>
                  Some (mk_insn idx w (pref_of po pid)
                        :: mk_insn (S idx) cont []
                        :: ps)
              end
          end
      | Some (_, _) => None
      end
  end.

Definition prefixgen_bpf (raw : BpfRawProgram) : option Program :=
  prefixgen_bpf_words raw 0%nat 0%nat.

Lemma prefixgen_bpf_words_machines :
  forall raw idx pid prog,
    prefixgen_bpf_words raw idx pid = Some prog ->
    map insn_machine prog = map MBpf raw.
Proof.
  intros raw.
  induction raw as [raw IH] using (well_founded_induction
    (well_founded_ltof _ (@length Word64))).
  intros idx pid prog H.
  destruct raw as [| w rest]; simpl in H.
  - inversion H. reflexivity.
  - destruct (decode_insn w (match rest with
                             | [] => None
                             | h :: _ => Some h
                             end)) as [[po wd]|] eqn:Hd; try discriminate.
    destruct wd as [| wd1]; try discriminate.
    destruct wd1 as [| wd2].
    + (* width 1 *)
      destruct (prefixgen_bpf_words rest (S idx) (next_pid po pid))
        as [ps|] eqn:Hr; try discriminate.
      inversion H. subst. simpl. f_equal.
      eapply (IH rest); eauto.
      unfold ltof. simpl. lia.
    + destruct wd2 as [|?]; try discriminate.
      destruct rest as [| cont rest']; try discriminate.
      destruct (prefixgen_bpf_words rest' (S (S idx)) (next_pid po pid))
        as [ps|] eqn:Hr; try discriminate.
      inversion H. subst. simpl. f_equal. f_equal.
      eapply (IH rest'); eauto.
      unfold ltof. simpl. lia.
Qed.

Lemma prefixgen_bpf_preserves_machine :
  forall raw prog,
    prefixgen_bpf raw = Some prog ->
    map insn_machine prog = bpf_machines raw.
Proof.
  intros raw prog H.
  unfold prefixgen_bpf, bpf_machines in *.
  eapply prefixgen_bpf_words_machines; eauto.
Qed.

End BpfDecode.
