#!/usr/bin/env python3
"""Regenerate Bpf.Tests + Module Rv32 in theories/prefixgen/Base.v from out/ fixtures."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "out"
BASE = Path(__file__).resolve().parent / "theories/prefixgen/Base.v"


def fmt_list(items, indent="    "):
    lines, row = [], []
    for it in items:
        row.append(it)
        if len(row) >= 4:
            lines.append(indent + "; ".join(row))
            row = []
    if row:
        lines.append(indent + "; ".join(row))
    return ";\n".join(lines)


def bpf_raw():
    out = []
    for line in (OUT / "bpf/prefixgen/prog.txt").read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        mach = line.split(":", 1)[1].split(",", 1)[0].strip()
        out.append(int.from_bytes(bytes.fromhex(mach), "little"))
    return out


def rv_raw():
    out = []
    for line in (OUT / "rv32imc/prefixgen/prog.txt").read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        mach = line.split(":", 1)[1].split(",", 1)[0].strip().replace(" ", "")
        v = int.from_bytes(bytes.fromhex(mach), "little")
        if len(mach) == 4:
            out.append(f"U16w 0x{v:x}")
        else:
            out.append(f"U32w 0x{v:x}")
    return out


bpf_body = fmt_list([f"0x{w:x}" for w in bpf_raw()])
rv_body = fmt_list(rv_raw())

bpf_tests = f"""
(** Unit tests from [out/bpf/prefixgen/prog.txt]. *)
Module Tests.

Definition bpf_o_raw : BpfRawProgram := [
{bpf_body}
].

Definition nth_pred (prog : Program) (i : nat) : option Predicate :=
  match nth_error prog i with
  | None => None
  | Some insn =>
      match insn.(insn_prefix) with
      | [] => Some PEmpty
      | n :: _ => Some n.(node_pred)
      end
  end.

(** out/bpf line 0: [b400000001000000] → [w0 = 0x1] *)
Example out_bpf_0 :
  let input := 0x1000000b4 in
  let output :=
    Some (Some (PSet (Rw 0) (OImm (Bv32 1))), 1%nat) in
  decode_insn input None = output.
Proof. reflexivity. Qed.

Example out_bpf_0_prog :
  match prefixgen_bpf bpf_o_raw with
  | Some prog => nth_pred prog 0%nat =
      Some (PSet (Rw 0) (OImm (Bv32 1)))
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** out/bpf line 1: load w *)
Example out_bpf_1 :
  let input := 0x41261 in
  let output :=
    Some (Some (PLoad (Rw 2) U32
      {{| addr_base := Rr 1%nat; addr_offset := Some (Bv64 4) |}}), 1%nat) in
  decode_insn input None = output.
Proof. reflexivity. Qed.

(** out/bpf line 3: [r1 = r6] *)
Example out_bpf_3 :
  let input := 0x61bf in
  let output :=
    Some (Some (PSet (Rr 1) (OReg (Rr 6))), 1%nat) in
  decode_insn input None = output.
Proof. reflexivity. Qed.

(** out/bpf line 4: [r1 += 0xe] *)
Example out_bpf_4 :
  let input := 0xe00000107 in
  let output :=
    Some (Some (PAluAssign (Rr 1) AAdd (OImm (Bv64 0xe))), 1%nat) in
  decode_insn input None = output.
Proof. reflexivity. Qed.

(** out/bpf line 5: if r1 > r2 goto +0x33 *)
Example out_bpf_5 :
  let input := 0x33212d in
  let output :=
    Some (Some (PIfGoto
      {{| cond_lhs := OReg (Rr 1); cond_op := CGt; cond_rhs := OReg (Rr 2) |}}
      0x33%Z), 1%nat) in
  decode_insn input None = output.
Proof. reflexivity. Qed.

(** out/bpf line 24: goto +6 *)
Example out_bpf_24 :
  let input := 0x60005 in
  let output := Some (Some (PGoto 6%Z), 1%nat) in
  decode_insn input None = output.
Proof. reflexivity. Qed.

(** out/bpf line 31: store with neg offset *)
Example out_bpf_31_prog :
  match prefixgen_bpf bpf_o_raw with
  | Some prog => nth_pred prog 31%nat =
      Some (PStore U32
        {{| addr_base := Rr 10; addr_offset := Some (Bv64 0xfffffffffffffffc) |}}
        (OReg (Rw 1)))
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** out/bpf lines 34–35: LDDW pair + empty slot *)
Example out_bpf_34_35 :
  match prefixgen_bpf bpf_o_raw with
  | Some prog =>
      (nth_pred prog 34%nat = Some (PSet (Rr 1) (OImm (Bv64 0))))
      /\\ (nth_pred prog 35%nat = Some PEmpty)
  | None => False
  end.
Proof. vm_compute. repeat split. Qed.

(** out/bpf line 36: call 1 *)
Example out_bpf_36 :
  let input := 0x100000085 in
  let output := Some (Some (PCall 1), 1%nat) in
  decode_insn input None = output.
Proof. reflexivity. Qed.

(** out/bpf line 57: exit *)
Example out_bpf_57 :
  let input := 0x95 in
  let output := Some (Some PExit, 1%nat) in
  decode_insn input None = output.
Proof. reflexivity. Qed.

Example bpf_o_len :
  match prefixgen_bpf bpf_o_raw with
  | Some prog => length prog = 58%nat
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

End Tests.
"""

# Fix double braces used to escape in f-string for Coq records
bpf_tests = bpf_tests.replace("{{|", "{|").replace("|}}", "|}").replace("/\\\\", "/\\")

rv32_module = r"""
(** RV32IMC words → Prefix (concrete decode + lower, mirrors Rust). *)
Module Rv32.
Import Predicate Raw.

Definition n_to_nat (n : N) : nat := N.to_nat n.
Definition reg_w (n : N) : Reg := Rw (n_to_nat n).

Definition to_u32 (z : Z) : N :=
  Z.to_N (Z.modulo z (Z.pow 2 32)).

Definition sext (bits : N) (u : N) : Z :=
  let half := N.shiftl 1 (bits - 1) in
  if N.ltb u half then Z.of_N u
  else (Z.of_N u - Z.shiftl 1 (Z.of_N bits))%Z.

Definition bits (w : N) (hi lo : N) : N :=
  N.land (N.shiftr w lo) (N.ones (hi - lo + 1)).

(** Expanded RV32I forms used by just_tx / IMC decompress. *)
Inductive IOp :=
| ILui (rd imm20 : N)
| IAuipc (rd imm20 : N)
| IAddi (rd rs1 : N) (imm : Z)
| IAdd (rd rs1 rs2 : N)
| ISltiu (rd rs1 : N) (imm : Z)
| ILw (rd rs1 : N) (off : Z)
| ILh (rd rs1 : N) (off : Z)
| ILhu (rd rs1 : N) (off : Z)
| ILbu (rd rs1 : N) (off : Z)
| ISw (rs1 rs2 : N) (off : Z)
| ISh (rs1 rs2 : N) (off : Z)
| IBeq (rs1 rs2 : N) (off : Z)
| IBne (rs1 rs2 : N) (off : Z)
| IBltu (rs1 rs2 : N) (off : Z)
| IBgeu (rs1 rs2 : N) (off : Z)
| IJal (rd : N) (off : Z)
| IJalr (rd rs1 : N) (off : Z).

Definition i_imm (w : N) : Z := sext 12 (bits w 31 20).
Definition s_imm (w : N) : Z :=
  sext 12 (N.lor (N.shiftl (bits w 31 25) 5) (bits w 11 7)).
Definition b_imm (w : N) : Z :=
  sext 13 (
    N.lor (N.lor (N.lor
      (N.shiftl (bits w 31 31) 12)
      (N.shiftl (bits w 30 25) 5))
      (N.shiftl (bits w 11 8) 1))
      (N.shiftl (bits w 7 7) 11)).
Definition u_imm (w : N) : N := N.shiftr w 12.
Definition j_imm (w : N) : Z :=
  sext 21 (
    N.lor (N.lor (N.lor
      (N.shiftl (bits w 31 31) 20)
      (N.shiftl (bits w 30 21) 1))
      (N.shiftl (bits w 20 20) 11))
      (N.shiftl (bits w 19 12) 12)).

Definition decode32 (w : N) : option IOp :=
  let opcode := bits w 6 0 in
  let rd := bits w 11 7 in
  let funct3 := bits w 14 12 in
  let rs1 := bits w 19 15 in
  let rs2 := bits w 24 20 in
  let funct7 := bits w 31 25 in
  if N.eqb opcode 0x37 then Some (ILui rd (u_imm w))
  else if N.eqb opcode 0x17 then Some (IAuipc rd (u_imm w))
  else if N.eqb opcode 0x6f then Some (IJal rd (j_imm w))
  else if N.eqb opcode 0x67 then
    if N.eqb funct3 0 then Some (IJalr rd rs1 (i_imm w)) else None
  else if N.eqb opcode 0x63 then
    if N.eqb funct3 0 then Some (IBeq rs1 rs2 (b_imm w))
    else if N.eqb funct3 1 then Some (IBne rs1 rs2 (b_imm w))
    else if N.eqb funct3 6 then Some (IBltu rs1 rs2 (b_imm w))
    else if N.eqb funct3 7 then Some (IBgeu rs1 rs2 (b_imm w))
    else None
  else if N.eqb opcode 0x03 then
    if N.eqb funct3 1 then Some (ILh rd rs1 (i_imm w))
    else if N.eqb funct3 2 then Some (ILw rd rs1 (i_imm w))
    else if N.eqb funct3 4 then Some (ILbu rd rs1 (i_imm w))
    else if N.eqb funct3 5 then Some (ILhu rd rs1 (i_imm w))
    else None
  else if N.eqb opcode 0x23 then
    if N.eqb funct3 1 then Some (ISh rs1 rs2 (s_imm w))
    else if N.eqb funct3 2 then Some (ISw rs1 rs2 (s_imm w))
    else None
  else if N.eqb opcode 0x13 then
    if N.eqb funct3 0 then Some (IAddi rd rs1 (i_imm w))
    else if N.eqb funct3 3 then Some (ISltiu rd rs1 (i_imm w))
    else None
  else if N.eqb opcode 0x33 then
    if (N.eqb funct3 0) && (N.eqb funct7 0) then Some (IAdd rd rs1 rs2)
    else None
  else None.

Definition c_imm_li (c : N) : Z :=
  sext 6 (N.lor (N.shiftl (bits c 12 12) 5) (bits c 6 2)).
Definition c_imm_lui (c : N) : N :=
  to_u32 (sext 6 (N.lor (N.shiftl (bits c 12 12) 5) (bits c 6 2))).
Definition c_imm_addi16sp (c : N) : Z :=
  sext 10 (
    N.lor (N.lor (N.lor (N.lor
      (N.shiftl (bits c 12 12) 9)
      (N.shiftl (bits c 6 6) 4))
      (N.shiftl (bits c 5 5) 6))
      (N.shiftl (bits c 4 3) 7))
      (N.shiftl (bits c 2 2) 5)).
Definition c_imm_addi4spn (c : N) : Z :=
  Z.of_N (
    N.lor (N.lor (N.lor
      (N.shiftl (bits c 12 11) 4)
      (N.shiftl (bits c 10 7) 6))
      (N.shiftl (bits c 6 6) 2))
      (N.shiftl (bits c 5 5) 3)).
Definition c_offset_lsw (c : N) : Z :=
  Z.of_N (
    N.lor (N.lor
      (N.shiftl (bits c 12 10) 3)
      (N.shiftl (bits c 6 6) 2))
      (N.shiftl (bits c 5 5) 6)).
Definition c_offset_lwsp (c : N) : Z :=
  Z.of_N (
    N.lor (N.lor
      (N.shiftl (bits c 12 12) 5)
      (N.shiftl (bits c 6 4) 2))
      (N.shiftl (bits c 3 2) 6)).
Definition c_offset_swsp (c : N) : Z :=
  Z.of_N (
    N.lor (N.shiftl (bits c 12 9) 2) (N.shiftl (bits c 8 7) 6)).
Definition c_offset_jump (c : N) : Z :=
  sext 12 (
    N.lor (N.lor (N.lor (N.lor (N.lor (N.lor (N.lor
      (N.shiftl (bits c 12 12) 11)
      (N.shiftl (bits c 11 11) 4))
      (N.shiftl (bits c 10 9) 8))
      (N.shiftl (bits c 8 8) 10))
      (N.shiftl (bits c 7 7) 6))
      (N.shiftl (bits c 6 6) 7))
      (N.shiftl (bits c 5 3) 1))
      (N.shiftl (bits c 2 2) 5)).
Definition c_offset_branch (c : N) : Z :=
  sext 9 (
    N.lor (N.lor (N.lor (N.lor
      (N.shiftl (bits c 12 12) 8)
      (N.shiftl (bits c 11 10) 3))
      (N.shiftl (bits c 6 5) 6))
      (N.shiftl (bits c 4 3) 1))
      (N.shiftl (bits c 2 2) 5)).

Definition decode16 (c : N) : option IOp :=
  let opcode := bits c 1 0 in
  let funct3 := bits c 15 13 in
  if N.eqb opcode 0 then
    let rd := bits c 4 2 + 8 in
    let rs1 := bits c 9 7 + 8 in
    let rs2 := bits c 4 2 + 8 in
    if N.eqb c 0 then None
    else if N.eqb funct3 0 then Some (IAddi rd 2 (c_imm_addi4spn c))
    else if N.eqb funct3 2 then Some (ILw rd rs1 (c_offset_lsw c))
    else if N.eqb funct3 6 then Some (ISw rs1 rs2 (c_offset_lsw c))
    else None
  else if N.eqb opcode 1 then
    let rd := bits c 11 7 in
    let rs1 := bits c 9 7 + 8 in
    let y := bits c 11 7 in
    if N.eqb funct3 0 then
      if N.eqb y 0 then None
      else Some (IAddi rd rd (c_imm_li c))
    else if N.eqb funct3 2 then Some (IAddi rd 0 (c_imm_li c))
    else if N.eqb funct3 3 then
      if N.eqb y 2 then Some (IAddi 2 2 (c_imm_addi16sp c))
      else Some (ILui rd (c_imm_lui c))
    else if N.eqb funct3 5 then Some (IJal 0 (c_offset_jump c))
    else if N.eqb funct3 6 then Some (IBeq rs1 0 (c_offset_branch c))
    else if N.eqb funct3 7 then Some (IBne rs1 0 (c_offset_branch c))
    else None
  else if N.eqb opcode 2 then
    let rd := bits c 11 7 in
    let rs1 := bits c 11 7 in
    let rs2 := bits c 6 2 in
    let z := bits c 12 12 in
    if N.eqb funct3 2 then Some (ILw rd 2 (c_offset_lwsp c))
    else if N.eqb funct3 4 then
      if N.eqb z 0 then
        if N.eqb rs2 0 then Some (IJalr 0 rs1 0)
        else Some (IAdd rd 0 rs2)
      else
        if N.eqb rs2 0 then Some (IJalr 1 rs1 0)
        else Some (IAdd rd rd rs2)
    else if N.eqb funct3 6 then Some (ISw 2 rs2 (c_offset_swsp c))
    else None
  else None.

Definition decode_word (w : U32OrU16) : option IOp :=
  match w with
  | U16w c => decode16 c
  | U32w v => decode32 v
  end.

Definition word_len (w : U32OrU16) : N :=
  match w with U16w _ => 2 | U32w _ => 4 end.

Fixpoint pcs_of (raw : Rv32RawProgram) (pc : N) : list N :=
  match raw with
  | [] => []
  | w :: rest => pc :: pcs_of rest (pc + word_len w)
  end.

Fixpoint find_pc (pcs : list N) (target : N) (i : nat) : option nat :=
  match pcs with
  | [] => None
  | p :: rest =>
      if N.eqb p target then Some i else find_pc rest target (S i)
  end.

Definition rel_goto (from to : nat) : Z :=
  (Z.of_nat to - Z.of_nat from - 1)%Z.

Definition imm32 (z : Z) : Operand := OImm (Bv32 (to_u32 z)).
Definition address (base : N) (off : Z) : Address :=
  {| addr_base := reg_w base;
     addr_offset := if Z.eqb off 0 then None else Some (Bv32 (to_u32 off)) |}.

Definition alu_addi (rd rs1 : N) (imm : Z) : option Predicate :=
  if N.eqb rd 0 then None
  else if Z.eqb imm 0 then Some (PSet (reg_w rd) (OReg (reg_w rs1)))
  else if N.eqb rs1 0 then Some (PSet (reg_w rd) (imm32 imm))
  else if N.eqb rd rs1 then Some (PAluAssign (reg_w rd) AAdd (imm32 imm))
  else Some (PAlu (reg_w rd) AAdd (OReg (reg_w rs1)) (imm32 imm)).

Definition alu_add (rd rs1 rs2 : N) : option Predicate :=
  if N.eqb rd 0 then None
  else if N.eqb rs1 0 then Some (PSet (reg_w rd) (OReg (reg_w rs2)))
  else if N.eqb rs2 0 then Some (PSet (reg_w rd) (OReg (reg_w rs1)))
  else if N.eqb rd rs1 then Some (PAluAssign (reg_w rd) AAdd (OReg (reg_w rs2)))
  else Some (PAlu (reg_w rd) AAdd (OReg (reg_w rs1)) (OReg (reg_w rs2))).

Inductive Prior :=
| NoPrior
| PriorAuipc (pc rd imm20 : N).

Definition branch_cmp (iop : IOp) : CmpOp :=
  match iop with
  | IBeq _ _ _ => CEq
  | IBne _ _ _ => CNe
  | IBltu _ _ _ => CLt
  | IBgeu _ _ _ => CGe
  | _ => CEq
  end.

Definition lower_iop (iop : IOp) (index : nat) (pc : N) (pcs : list N) (prior : Prior)
  : option Predicate :=
  match iop with
  | ILui rd imm20 =>
      if N.eqb rd 0 then None
      else Some (PSet (reg_w rd) (OImm (Bv32 (N.shiftl imm20 12))))
  | IAuipc rd imm20 =>
      if N.eqb rd 0 then None
      else
        let v := N.land (pc + N.shiftl imm20 12) 0xffffffff in
        Some (PSet (reg_w rd) (OImm (Bv32 v)))
  | IAddi rd rs1 imm => alu_addi rd rs1 imm
  | IAdd rd rs1 rs2 => alu_add rd rs1 rs2
  | ISltiu rd rs1 imm =>
      if N.eqb rd 0 then None
      else Some (PAluCall (reg_w rd) ACSltu (OReg (reg_w rs1)) (imm32 imm))
  | ILw rd rs1 off =>
      if N.eqb rd 0 then None else Some (PLoad (reg_w rd) U32 (address rs1 off))
  | ILh rd rs1 off =>
      if N.eqb rd 0 then None else Some (PLoad (reg_w rd) S16 (address rs1 off))
  | ILhu rd rs1 off =>
      if N.eqb rd 0 then None else Some (PLoad (reg_w rd) U16 (address rs1 off))
  | ILbu rd rs1 off =>
      if N.eqb rd 0 then None else Some (PLoad (reg_w rd) U8 (address rs1 off))
  | ISw rs1 rs2 off => Some (PStore U32 (address rs1 off) (OReg (reg_w rs2)))
  | ISh rs1 rs2 off => Some (PStore U16 (address rs1 off) (OReg (reg_w rs2)))
  | IBeq rs1 rs2 off
  | IBne rs1 rs2 off
  | IBltu rs1 rs2 off
  | IBgeu rs1 rs2 off =>
      let target_pc := to_u32 (Z.of_N pc + off) in
      match find_pc pcs target_pc 0%nat with
      | None => None
      | Some tgt =>
          Some (PIfGoto
            {| cond_lhs := OReg (reg_w rs1); cond_op := branch_cmp iop;
               cond_rhs := OReg (reg_w rs2) |}
            (rel_goto index tgt))
      end
  | IJal rd off =>
      let target_pc := to_u32 (Z.of_N pc + off) in
      match find_pc pcs target_pc 0%nat with
      | None => None
      | Some tgt =>
          if N.eqb rd 0 then Some (PGoto (rel_goto index tgt)) else None
      end
  | IJalr rd rs1 off =>
      if (N.eqb rd 0) && (N.eqb rs1 1) && (Z.eqb off 0) then Some PExit
      else if N.eqb rd 1 then
        match prior with
        | PriorAuipc prior_pc _ imm20 =>
            let target :=
              N.land (prior_pc + N.shiftl imm20 12 + to_u32 off) 0xfffffffe in
            Some (PCall (N.land target 0xffffffff))
        | NoPrior => None
        end
      else None
  end.

Definition next_prior (iop : IOp) (pc : N) : Prior :=
  match iop with
  | IAuipc rd imm20 => PriorAuipc pc rd imm20
  | _ => NoPrior
  end.

Definition mk_insn (idx : nat) (w : U32OrU16) (pref : Prefix) : Insn :=
  {| insn_index := idx; insn_machine := rv32_machine w; insn_prefix := pref |}.

Definition pref_of (po : option Predicate) (pid : nat) : Prefix :=
  match po with
  | None => []
  | Some p => singleton_prefix pid p
  end.

Definition next_pid (po : option Predicate) (pid : nat) : nat :=
  match po with None => pid | Some _ => S pid end.

Definition is_rd0_elision (iop : IOp) : bool :=
  match iop with
  | ILui 0 _ | IAuipc 0 _ | IAddi 0 _ _ | IAdd 0 _ _
  | ISltiu 0 _ _ | ILw 0 _ _ | ILh 0 _ _ | ILhu 0 _ _ | ILbu 0 _ _ => true
  | _ => false
  end.

Fixpoint prefixgen_go (raw : Rv32RawProgram) (pcs_all pcs : list N)
  (idx : nat) (pid : nat) (prior : Prior) : option Program :=
  match raw with
  | [] => Some []
  | w :: rest =>
      match pcs with
      | [] => None
      | pc :: pcs_tail =>
          match decode_word w with
          | None => None
          | Some iop =>
              match lower_iop iop idx pc pcs_all prior with
              | Some pred =>
                  match prefixgen_go rest pcs_all pcs_tail (S idx)
                          (next_pid (Some pred) pid) (next_prior iop pc) with
                  | None => None
                  | Some ps =>
                      Some (mk_insn idx w (pref_of (Some pred) pid) :: ps)
                  end
              | None =>
                  if is_rd0_elision iop then
                    match prefixgen_go rest pcs_all pcs_tail (S idx) pid
                            (next_prior iop pc) with
                    | None => None
                    | Some ps => Some (mk_insn idx w [] :: ps)
                    end
                  else None
              end
          end
      end
  end.

Definition prefixgen_rv32_words (raw : Rv32RawProgram) : option Program :=
  let pcs := pcs_of raw 0 in
  prefixgen_go raw pcs pcs 0%nat 0%nat NoPrior.

Lemma prefixgen_go_machines :
  forall raw pcs_all pcs idx pid prior prog,
    prefixgen_go raw pcs_all pcs idx pid prior = Some prog ->
    map insn_machine prog = map rv32_machine raw.
Proof.
  induction raw as [| w rest IH]; intros pcs_all pcs idx pid prior prog H; simpl in H.
  - inversion H. reflexivity.
  - destruct pcs as [| pc pcs_tail]; try discriminate.
    destruct (decode_word w) as [iop|] eqn:Hd; try discriminate.
    destruct (lower_iop iop idx pc pcs_all prior) as [pred|] eqn:Hl.
    + simpl in H.
      destruct (prefixgen_go rest pcs_all pcs_tail (S idx) (S pid) (next_prior iop pc))
        as [ps|] eqn:Hr; try discriminate.
      inversion H; subst; simpl; f_equal.
      eapply IH; eauto.
    + destruct (is_rd0_elision iop) eqn:He; try discriminate.
      destruct (prefixgen_go rest pcs_all pcs_tail (S idx) pid (next_prior iop pc))
        as [ps|] eqn:Hr; try discriminate.
      inversion H; subst; simpl; f_equal.
      eapply IH; eauto.
Qed.

Lemma prefixgen_rv32_preserves_machine :
  forall raw prog,
    prefixgen_rv32_words raw = Some prog ->
    map insn_machine prog = rv32_machines raw.
Proof.
  intros raw prog H.
  unfold prefixgen_rv32_words, rv32_machines in *.
  eapply prefixgen_go_machines; eauto.
Qed.

(** Fixture: [out/rv32imc/prefixgen/prog.txt] machine column (just_tx.elf). *)
Definition just_tx_raw : Rv32RawProgram := [
@@JUST_TX_RAW@@
].

Definition nth_pred (prog : Program) (i : nat) : option Predicate :=
  match nth_error prog i with
  | None => None
  | Some insn =>
      match insn.(insn_prefix) with
      | [] => None
      | n :: _ => Some n.(node_pred)
      end
  end.

Module Tests.

Example out_rv_0_decode :
  let input := U16w 0x1141 in
  let output := Some (IAddi 2 2 (-16)%Z) in
  decode_word input = output.
Proof. reflexivity. Qed.

Example out_rv_0_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 0%nat =
      Some (PAluAssign (Rw 2) AAdd (OImm (Bv32 0xfffffff0)))
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_1_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 1%nat =
      Some (PStore U32 {| addr_base := Rw 2; addr_offset := Some (Bv32 0xc) |}
              (OReg (Rw 1)))
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_4_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 4%nat =
      Some (PAlu (Rw 8) AAdd (OReg (Rw 2)) (OImm (Bv32 0x10)))
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_8_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 8%nat =
      Some (PSet (Rw 10) (OImm (Bv32 1)))
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_9_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 9%nat =
      Some (PIfGoto {| cond_lhs := OReg (Rw 11); cond_op := CLt;
                       cond_rhs := OReg (Rw 12) |} 0x3e%Z)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_11_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 11%nat =
      Some (PSet (Rw 13) (OImm (Bv32 0xb000)))
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_20_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 20%nat = Some (PGoto 1%Z)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_45_call :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 45%nat = Some (PCall 0x6e4a5c)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_48_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 48%nat =
      Some (PIfGoto {| cond_lhs := OReg (Rw 11); cond_op := CEq;
                       cond_rhs := OReg (Rw 0) |} 7%Z)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_52_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 52%nat =
      Some (PAluCall (Rw 14) ACSltu (OReg (Rw 12)) (OImm (Bv32 1)))
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_76_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 76%nat = Some PExit
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example out_rv_78_prefix :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => nth_pred prog 78%nat = Some (PGoto (-0x2b)%Z)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example just_tx_len :
  match prefixgen_rv32_words just_tx_raw with
  | Some prog => length prog = 79%nat
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

End Tests.

End Rv32.
"""

rv32_module = rv32_module.replace("@@JUST_TX_RAW@@", rv_body)

text = BASE.read_text()
marker = "(** Unit tests: instruction-word input → Prefix / Program output. *)"
idx = text.find(marker)
if idx < 0:
    # already regenerated?
    marker2 = "(** Unit tests from [out/bpf/prefixgen/prog.txt]. *)"
    idx = text.find(marker2)
    if idx < 0:
        raise SystemExit("marker not found")
    # find start of Tests inside Bpf — go back to before Module Tests of bpf
    # Actually find End of preserves_machine
    pass

# Prefer original marker; if missing, find preserves_machine Qed then Tests
if "(** Unit tests: instruction-word input" in text:
    idx = text.find("(** Unit tests: instruction-word input → Prefix / Program output. *)")
elif "(** Unit tests from [out/bpf/prefixgen/prog.txt]. *)" in text:
    idx = text.find("(** Unit tests from [out/bpf/prefixgen/prog.txt]. *)")
else:
    raise SystemExit("no tests marker")

# Find Module Rv32 or End Bpf after idx — replace from idx to EOF of Bpf+Rv32
# Head is everything before tests
head = text[:idx]
# Drop trailing End Bpf if present before Rv32 in head? Head should end after preserves Qed.
out = head + bpf_tests + "\nEnd Bpf.\n" + rv32_module
BASE.write_text(out)
print(f"wrote {BASE} ({len(out)} bytes)")
