(** * Prefixgen facade — mirrors [src/prefixgen/mod.rs]. *)

From Stdlib Require Import List NArith.
Import ListNotations.
From Classifier Require Import Predicate Raw.
From Classifier Require Import prefixgen.Base prefixgen.Extract.

Module Prefixgen.
Import Predicate Raw.
Import Base.
Import Extract.

Definition machines_of (p : Program) : list Machine :=
  map insn_machine p.

Definition prefixgen_bpf : BpfRawProgram -> option Program :=
  Bpf.prefixgen_bpf.

Definition prefixgen_rv32 : Rv32RawProgram -> option Program :=
  Rv32.prefixgen_rv32_words.

Definition prefixgen_bpf_object (bytes : Bytes) : option Program :=
  match extract_bpf_words bytes with
  | None => None
  | Some raw => prefixgen_bpf raw
  end.

Definition prefixgen_rv32_elf (bytes : Bytes) : option Program :=
  match extract_rv32_image bytes with
  | None => None
  | Some image =>
      match split_rv32imc image with
      | None => None
      | Some raw => prefixgen_rv32 raw
      end
  end.

Module Tests.
Example facade_matches_base :
  let input : BpfRawProgram := [0x0000000000000095] in
  prefixgen_bpf input = Bpf.prefixgen_bpf input.
Proof. reflexivity. Qed.

Example machines_of_io :
  let input : Program :=
    [{| insn_index := 0%nat;
        insn_machine := MBpf 9;
        insn_prefix := [] |}] in
  let output := [MBpf 9] in
  machines_of input = output.
Proof. reflexivity. Qed.
End Tests.

End Prefixgen.
