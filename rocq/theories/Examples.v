(** * Detailed [Check] + compute coverage for every public definition.

    - [Check] pins the type of each definition (including [Parameter]s).
    - [Example]s evaluate BPF field extractors, tables, and decode paths. *)

From Stdlib Require Import List NArith ZArith Bool.
Import ListNotations.
Open Scope N_scope.

From Classifier Require Import Predicate Raw.
From Classifier Require Import prefixgen.Base prefixgen.Extract prefixgen.Prefixgen.
From Classifier Require Import Theorems.

Module Examples.
Import Predicate Raw.
Import Base.
Import Extract.
Import Prefixgen.

(* -------------------------------------------------------------------- *)
(** * Predicate / Raw — [Check] every definition *)
(* -------------------------------------------------------------------- *)

Check Width.
Check width_bits : Width -> N.
Check BitVec.
Check Bv8.
Check Bv16.
Check Bv32.
Check Bv64.
Check MemWidth.
Check Reg.
Check Rw.
Check Rr.
Check Operand.
Check OReg.
Check OImm.
Check Address.
Check addr_base.
Check addr_offset.
Check CmpOp.
Check Condition.
Check AluOp.
Check JumpOff.
Check Predicate.Predicate.
Check PSet.
Check PAluAssign.
Check PAlu.
Check PLoad.
Check PStore.
Check PIfGoto.
Check PGoto.
Check PCall.
Check PExit.
Check PEmpty.
Check PredicateId.
Check PredicateNode.
Check Prefix.
Check singleton_prefix.
Check Machine.
Check MBpf.
Check MRv32.
Check MRv16.
Check Insn.
Check Program.
Check insn_keep_machine.

Check Word64.
Check BpfRawProgram.
Check U32OrU16.
Check U32w.
Check U16w.
Check Rv32RawProgram.
Check bpf_machines.
Check rv32_machine.
Check rv32_machines.

(* -------------------------------------------------------------------- *)
(** * Extract / Base.Rv32 / Prefixgen / Theorems — [Check] *)
(* -------------------------------------------------------------------- *)

Check Bytes.
Check extract_bpf_words : Bytes -> option BpfRawProgram.
Check extract_rv32_image : Bytes -> option Bytes.
Check split_rv32imc : Bytes -> option Rv32RawProgram.

Check Rv32.prefixgen_rv32_words : Rv32RawProgram -> option Program.
Check Rv32.prefixgen_rv32_preserves_machine.

Check Bpf.word_code.
Check Bpf.word_dst.
Check Bpf.word_src.
Check Bpf.word_off_u.
Check Bpf.word_imm_u.
Check Bpf.n_to_nat.
Check Bpf.to_u64.
Check Bpf.word_off_s.
Check Bpf.imm32_as_N.
Check Bpf.imm32_as_u64_sext.
Check Bpf.class_of.
Check Bpf.op_of.
Check Bpf.size_of.
Check Bpf.mode_of.
Check Bpf.src_reg_bit.
Check Bpf.mem_width.
Check Bpf.reg_w.
Check Bpf.reg_r.
Check Bpf.dst_reg_load.
Check Bpf.address.
Check Bpf.alu_op.
Check Bpf.cmp_op.
Check Bpf.decode_alu.
Check Bpf.decode_jmp.
Check Bpf.decode_insn.
Check Bpf.mk_insn.
Check Bpf.next_pid.
Check Bpf.pref_of.
Check Bpf.prefixgen_bpf_words.
Check Bpf.prefixgen_bpf.
Check Bpf.prefixgen_bpf_words_machines.
Check Bpf.prefixgen_bpf_preserves_machine.

Check machines_of.
Check prefixgen_bpf.
Check prefixgen_rv32.
Check prefixgen_bpf_object.
Check prefixgen_rv32_elf.

Check Theorems.prefixgen_bpf_preserves_machine.
Check Theorems.prefixgen_bpf_length.
Check Theorems.prefixgen_rv32_preserves_machine.
Check Theorems.prefixgen_rv32_length.

(* -------------------------------------------------------------------- *)
(** * Predicate helpers — compute *)
(* -------------------------------------------------------------------- *)

Example width_bits_table :
  width_bits W8 = 8 /\ width_bits W16 = 16 /\
  width_bits W32 = 32 /\ width_bits W64 = 64.
Proof. repeat split; reflexivity. Qed.

Example singleton_prefix_shape :
  singleton_prefix 3%nat PExit =
    [{| node_id := 3%nat; node_pred := PExit |}].
Proof. reflexivity. Qed.

Example insn_keep_machine_bpf :
  insn_keep_machine
    {| insn_index := 0%nat; insn_machine := MBpf 1; insn_prefix := [] |}
  = MBpf 1.
Proof. reflexivity. Qed.

Example bpf_machines_cons :
  bpf_machines [1; 2] = [MBpf 1; MBpf 2].
Proof. reflexivity. Qed.

Example rv32_machines_mix :
  rv32_machines [U32w 1; U16w 2] = [MRv32 1; MRv16 2].
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(** * Bpf field extractors — fixture word [b4 00 00 00 01 00 00 00] *)
(* -------------------------------------------------------------------- *)

Import Bpf.

Definition w_mov32 : N := 0x00000001000000b4.
(** [07 01 00 00 0e 00 00 00] — [r1 += 0xe] *)
Definition w_add64 : N := 0x0000000e00000107.
(** [07 02 00 00 fc ff ff ff] — [r2 += -4] *)
Definition w_add64_m4 : N := 0xfffffffc00000207.
(** [63 1a fc ff 00 00 00 00] — [*(u32 *)(r10 - 4) = w1] *)
Definition w_stx_m4 : N := 0x00000000fffc1a63.

Example fields_mov32 :
  word_code w_mov32 = 0xb4 /\
  word_dst w_mov32 = 0 /\
  word_src w_mov32 = 0 /\
  word_off_u w_mov32 = 0 /\
  word_imm_u w_mov32 = 1.
Proof. repeat split; reflexivity. Qed.

Example fields_add64 :
  class_of (word_code w_add64) = 0x07 /\
  op_of (word_code w_add64) = 0x00 /\
  negb (src_reg_bit (word_code w_add64)) = true /\
  word_dst w_add64 = 1 /\
  word_imm_u w_add64 = 0xe.
Proof. repeat split; reflexivity. Qed.

Example off_signed_neg4 :
  word_off_s w_stx_m4 = (-4)%Z.
Proof. reflexivity. Qed.

Example imm_sext_neg4 :
  imm32_as_u64_sext w_add64_m4 = 0xfffffffffffffffc.
Proof. reflexivity. Qed.

Example to_u64_neg16 :
  to_u64 (-16)%Z = 0xfffffffffffffff0.
Proof. reflexivity. Qed.

Example n_to_nat_small : n_to_nat 7 = 7%nat.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(** * Tables: mem_width / alu_op / cmp_op / regs / address *)
(* -------------------------------------------------------------------- *)

Example mem_width_all :
  mem_width 0x00 = Some U32 /\
  mem_width 0x08 = Some U16 /\
  mem_width 0x10 = Some U8 /\
  mem_width 0x18 = Some U64 /\
  mem_width 0x20 = None.
Proof. repeat split; reflexivity. Qed.

Example alu_op_all :
  alu_op 0x00 = Some AAdd /\
  alu_op 0x10 = Some ASub /\
  alu_op 0x20 = Some AMul /\
  alu_op 0x30 = Some ADivu /\
  alu_op 0x40 = Some AOr /\
  alu_op 0x50 = Some AAnd /\
  alu_op 0x60 = Some AShl /\
  alu_op 0x70 = Some ALshr /\
  alu_op 0x90 = Some ARemu /\
  alu_op 0xa0 = Some AXor /\
  alu_op 0xc0 = Some AAshr /\
  alu_op 0xb0 = None /\
  alu_op 0xff = None.
Proof. repeat split; reflexivity. Qed.

Example cmp_op_all :
  cmp_op 0x10 = Some CEq /\
  cmp_op 0x20 = Some CGt /\
  cmp_op 0x30 = Some CGe /\
  cmp_op 0x50 = Some CNe /\
  cmp_op 0x60 = Some CSgt /\
  cmp_op 0x70 = Some CSge /\
  cmp_op 0xa0 = Some CLt /\
  cmp_op 0xb0 = Some CLe /\
  cmp_op 0xc0 = Some CSlt /\
  cmp_op 0xd0 = Some CSle /\
  cmp_op 0x40 = None /\
  cmp_op 0x00 = None.
Proof. repeat split; reflexivity. Qed.

Example regs_and_dst_load :
  reg_w 2 = Rw 2%nat /\
  reg_r 6 = Rr 6%nat /\
  dst_reg_load 0 U64 = Rr 0%nat /\
  dst_reg_load 0 U32 = Rw 0%nat /\
  dst_reg_load 0 U8 = Rw 0%nat.
Proof. repeat split; reflexivity. Qed.

Example address_zero_and_neg :
  address 10 0%Z = {| addr_base := Rr 10%nat; addr_offset := None |} /\
  address 10 (-4)%Z =
    {| addr_base := Rr 10%nat;
       addr_offset := Some (Bv64 0xfffffffffffffffc) |}.
Proof. repeat split; reflexivity. Qed.

Example next_pid_pref :
  next_pid None 5%nat = 5%nat /\
  next_pid (Some PExit) 5%nat = 6%nat /\
  pref_of None 0%nat = [] /\
  pref_of (Some PExit) 0%nat = singleton_prefix 0%nat PExit.
Proof. repeat split; reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(** * decode_insn — one Example per BPF class used in the fixture *)
(* -------------------------------------------------------------------- *)

(** ALU32 MOV: [b4 00 00 00 01 00 00 00] *)
Example decode_alu32_mov :
  decode_insn w_mov32 None =
    Some (Some (PSet (Rw 0) (OImm (Bv32 1))), 1%nat).
Proof. reflexivity. Qed.

(** ALU64 MOV X: [bf 61 00 00 00 00 00 00] *)
Definition w_mov64 : N := 0x00000000000061bf.
Example decode_alu64_mov_x :
  decode_insn w_mov64 None =
    Some (Some (PSet (Rr 1) (OReg (Rr 6))), 1%nat).
Proof. reflexivity. Qed.

(** ALU64 ADD K *)
Example decode_alu64_add_k :
  decode_insn w_add64 None =
    Some (Some (PAluAssign (Rr 1) AAdd (OImm (Bv64 0xe))), 1%nat).
Proof. reflexivity. Qed.

(** LDX MEM W: [61 12 04 00 00 00 00 00] — [w2 = *(u32 *)(r1 + 4)] *)
Definition w_ldx_w : N := 0x0000000000041261.
Example decode_ldx_w :
  decode_insn w_ldx_w None =
    Some (Some (PLoad (Rw 2) U32
      {| addr_base := Rr 1%nat; addr_offset := Some (Bv64 4) |}), 1%nat).
Proof. reflexivity. Qed.

(** LDX MEM H: [69 64 0c 00 ...] *)
Definition w_ldx_h : N := 0x00000000000c6469.
Example decode_ldx_h :
  decode_insn w_ldx_h None =
    Some (Some (PLoad (Rw 4) U16
      {| addr_base := Rr 6%nat; addr_offset := Some (Bv64 0xc) |}), 1%nat).
Proof. reflexivity. Qed.

(** LDX MEM B: [71 41 09 00 ...] *)
Definition w_ldx_b : N := 0x0000000000094171.
Example decode_ldx_b :
  decode_insn w_ldx_b None =
    Some (Some (PLoad (Rw 1) U8
      {| addr_base := Rr 4%nat; addr_offset := Some (Bv64 9) |}), 1%nat).
Proof. reflexivity. Qed.

(** LDX MEM DW: [79 01 00 00 ...] *)
Definition w_ldx_dw : N := 0x0000000000000179.
Example decode_ldx_dw :
  decode_insn w_ldx_dw None =
    Some (Some (PLoad (Rr 1) U64
      {| addr_base := Rr 0%nat; addr_offset := None |}), 1%nat).
Proof. reflexivity. Qed.

(** STX MEM W with neg off *)
Example decode_stx_w_neg :
  decode_insn w_stx_m4 None =
    Some (Some (PStore U32
      {| addr_base := Rr 10%nat;
         addr_offset := Some (Bv64 0xfffffffffffffffc) |}
      (OReg (Rw 1))), 1%nat).
Proof. reflexivity. Qed.

(** STX MEM H: [6b 26 00 00 ...] *)
Definition w_stx_h : N := 0x000000000000266b.
Example decode_stx_h :
  decode_insn w_stx_h None =
    Some (Some (PStore U16
      {| addr_base := Rr 6%nat; addr_offset := None |}
      (OReg (Rw 2))), 1%nat).
Proof. reflexivity. Qed.

(** STX MEM DW: [7b 10 00 00 ...] *)
Definition w_stx_dw : N := 0x000000000000107b.
Example decode_stx_dw :
  decode_insn w_stx_dw None =
    Some (Some (PStore U64
      {| addr_base := Rr 0%nat; addr_offset := None |}
      (OReg (Rr 1))), 1%nat).
Proof. reflexivity. Qed.

(** JMP JGT X: [2d 21 33 00 ...] — [if r1 > r2 goto +0x33] *)
Definition w_jgt : N := 0x000000000033212d.
Example decode_jmp_jgt :
  decode_insn w_jgt None =
    Some (Some (PIfGoto
      {| cond_lhs := OReg (Rr 1); cond_op := CGt; cond_rhs := OReg (Rr 2) |}
      0x33%Z), 1%nat).
Proof. reflexivity. Qed.

(** JMP32 JEQ K: [16 04 02 00 81 00 00 00] *)
Definition w_jeq32 : N := 0x0000008100020416.
Example decode_jmp32_jeq :
  decode_insn w_jeq32 None =
    Some (Some (PIfGoto
      {| cond_lhs := OReg (Rw 4); cond_op := CEq; cond_rhs := OImm (Bv32 0x81) |}
      2%Z), 1%nat).
Proof. reflexivity. Qed.

(** JMP32 JNE K: [56 04 05 00 88 a8 00 00] *)
Definition w_jne32 : N := 0x0000a88800050456.
Example decode_jmp32_jne :
  decode_insn w_jne32 None =
    Some (Some (PIfGoto
      {| cond_lhs := OReg (Rw 4); cond_op := CNe; cond_rhs := OImm (Bv32 0xa888) |}
      5%Z), 1%nat).
Proof. reflexivity. Qed.

(** JA: [05 00 06 00 ...] *)
Definition w_ja : N := 0x0000000000060005.
Example decode_ja :
  decode_insn w_ja None = Some (Some (PGoto 6%Z), 1%nat).
Proof. reflexivity. Qed.

(** CALL: [85 00 00 00 01 00 00 00] *)
Definition w_call : N := 0x0000000100000085.
Example decode_call :
  decode_insn w_call None = Some (Some (PCall 1), 1%nat).
Proof. reflexivity. Qed.

(** EXIT: [95 ...] *)
Definition w_exit : N := 0x0000000000000095.
Example decode_exit :
  decode_insn w_exit None = Some (Some PExit, 1%nat).
Proof. reflexivity. Qed.

(** LDDW: [18 01 00 00 00 00 00 00] + continuation *)
Definition w_lddw0 : N := 0x0000000000000118.
Definition w_lddw1 : N := 0x0000000000000000.
Example decode_lddw :
  decode_insn w_lddw0 (Some w_lddw1) =
    Some (Some (PSet (Rr 1) (OImm (Bv64 0))), 2%nat).
Proof. reflexivity. Qed.

Example decode_lddw_missing_cont :
  decode_insn w_lddw0 None = None.
Proof. reflexivity. Qed.

(** JSET unsupported; unknown class *)
Definition w_jset : N := 0x0000000000000045. (* JMP|JSET|K roughly — class 5 op 40 *)
Example decode_jset_none :
  (* op 0x40 on JMP: code = 0x05|0x40 = 0x45 *)
  decode_insn w_jset None = None.
Proof. reflexivity. Qed.

Definition w_bad : N := 0x00000000000000ff.
Example decode_bad_class :
  decode_insn w_bad None = None.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(** * decode_alu / decode_jmp direct + NEG *)
(* -------------------------------------------------------------------- *)

Example decode_alu_neg32 :
  decode_alu false 0x80 0x84 3 0 w_mov32 =
    Some (PAlu (Rw 3) ASub (OImm (Bv32 0)) (OReg (Rw 3))).
Proof. reflexivity. Qed.

Example decode_jmp_exit_direct :
  decode_jmp true 0x90 0x95 0 0 w_exit 0%Z = Some PExit.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(** * prefixgen_bpf_words — empty, single, lddw pair, failure *)
(* -------------------------------------------------------------------- *)

Example prefixgen_empty :
  prefixgen_bpf [] = Some [].
Proof. reflexivity. Qed.

Example prefixgen_exit_prog :
  prefixgen_bpf [w_exit] =
    Some [{| insn_index := 0%nat;
             insn_machine := MBpf w_exit;
             insn_prefix := singleton_prefix 0%nat PExit |}].
Proof. reflexivity. Qed.

Example prefixgen_lddw_two_slots :
  match prefixgen_bpf [w_lddw0; w_lddw1; w_exit] with
  | Some [i0; i1; i2] =>
      insn_index i0 = 0%nat /\
      insn_index i1 = 1%nat /\
      insn_prefix i1 = [] /\
      insn_machine i1 = MBpf w_lddw1 /\
      insn_index i2 = 2%nat
  | _ => False
  end.
Proof. repeat split; reflexivity. Qed.

Example prefixgen_lddw_truncated :
  prefixgen_bpf [w_lddw0] = None.
Proof. reflexivity. Qed.

Example prefixgen_machines_ok :
  match prefixgen_bpf [w_mov32; w_exit] with
  | Some prog => map insn_machine prog = [MBpf w_mov32; MBpf w_exit]
  | None => False
  end.
Proof. reflexivity. Qed.

Example mk_insn_shape :
  mk_insn 4%nat w_exit (singleton_prefix 1%nat PExit) =
    {| insn_index := 4%nat;
       insn_machine := MBpf w_exit;
       insn_prefix := singleton_prefix 1%nat PExit |}.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(** * Facade aliases *)
(* -------------------------------------------------------------------- *)

Example facade_bpf_eq_base :
  Prefixgen.prefixgen_bpf [w_exit] = Bpf.prefixgen_bpf [w_exit].
Proof. reflexivity. Qed.

Example machines_of_via_facade :
  match Prefixgen.prefixgen_bpf [w_exit] with
  | Some prog => machines_of prog = [MBpf w_exit]
  | None => False
  end.
Proof. reflexivity. Qed.

End Examples.
