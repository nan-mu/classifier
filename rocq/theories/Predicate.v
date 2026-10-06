(** * Predicate / Prefix / Insn — mirrors [src/predicate/].

    Bit-vector *payloads* are [N] tagged by width (executable decode).
    Semantic well-formedness ([n < 2^w]) is a separate obligation. *)

From Stdlib Require Import List NArith ZArith.
Import ListNotations.
Open Scope N_scope.

Module Predicate.

Inductive Width := W8 | W16 | W32 | W64.

Definition width_bits (w : Width) : N :=
  match w with
  | W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64
  end.

(** Tagged bit-vector; value is little-endian numeric [N]. *)
Inductive BitVec :=
| Bv8  : N -> BitVec
| Bv16 : N -> BitVec
| Bv32 : N -> BitVec
| Bv64 : N -> BitVec.

Inductive MemWidth := U8 | U16 | U32 | U64 | S8 | S16 | S32.

(** Surface registers: [Rw n] = wN, [Rr n] = rN. *)
Inductive Reg :=
| Rw : nat -> Reg
| Rr : nat -> Reg.

Inductive Operand :=
| OReg : Reg -> Operand
| OImm : BitVec -> Operand.

Record Address := {
  addr_base : Reg;
  addr_offset : option BitVec
}.

Inductive CmpOp :=
| CEq | CNe | CLt | CLe | CGt | CGe
| CSlt | CSle | CSgt | CSge.

Record Condition := {
  cond_lhs : Operand;
  cond_op : CmpOp;
  cond_rhs : Operand
}.

Inductive AluOp :=
| AAdd | ASub | AMul | AAnd | AOr | AXor
| AShl | ALshr | AAshr | ADiv | ADivu | ARem | ARemu.

(** Non-infix ALU shown as [dst = name(lhs, rhs)]. *)
Inductive AluCallName := ACSlt | ACSltu | ACMulh | ACMulhu | ACMulhsu.

(** Relative jump offset in instruction slots (signed). *)
Definition JumpOff := Z.

Inductive Predicate :=
| PSet : Reg -> Operand -> Predicate
| PAluAssign : Reg -> AluOp -> Operand -> Predicate
| PAlu : Reg -> AluOp -> Operand -> Operand -> Predicate
| PAluCall : Reg -> AluCallName -> Operand -> Operand -> Predicate
| PLoad : Reg -> MemWidth -> Address -> Predicate
| PStore : MemWidth -> Address -> Operand -> Predicate
| PAssert : Condition -> bool -> Predicate
| PIfGoto : Condition -> JumpOff -> Predicate
| PGoto : JumpOff -> Predicate
| PCall : N -> Predicate
| PExit : Predicate
| PTrap : Predicate
| PEmpty : Predicate.

Definition PredicateId := nat.

Record PredicateNode := {
  node_id : PredicateId;
  node_pred : Predicate
}.

Definition Prefix := list PredicateNode.

Definition singleton_prefix (id : PredicateId) (p : Predicate) : Prefix :=
  [{| node_id := id; node_pred := p |}].

Inductive Machine :=
| MBpf : N -> Machine
| MRv32 : N -> Machine
| MRv16 : N -> Machine.

Record Insn := {
  insn_index : nat;
  insn_machine : Machine;
  insn_prefix : Prefix
}.

Definition Program := list Insn.

Definition insn_keep_machine (i : Insn) : Machine := insn_machine i.

(** Unit tests: named input → expected output. *)
Module Tests.
Example width_bits_W32 : width_bits W32 = 32. Proof. reflexivity. Qed.

Example singleton_prefix_exit :
  let input_id := 0%nat in
  let input_pred := PExit in
  let output := [{| node_id := 0%nat; node_pred := PExit |}] in
  singleton_prefix input_id input_pred = output.
Proof. reflexivity. Qed.

Example keep_machine_roundtrip :
  let input := {| insn_index := 1%nat; insn_machine := MBpf 42; insn_prefix := [] |} in
  let output := MBpf 42 in
  insn_keep_machine input = output.
Proof. reflexivity. Qed.
End Tests.

End Predicate.
