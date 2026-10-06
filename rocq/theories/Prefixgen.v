(** * Prefixgen facade — mirrors [src/prefixgen/mod.rs]. *)

From Stdlib Require Import List NArith.
Import ListNotations.
From Classifier Require Import Predicate Raw Extract BpfDecode Rv32Decode.

Module Prefixgen.
Import Predicate Raw Extract BpfDecode Rv32Decode.

Definition machines_of (p : Program) : list Machine :=
  map insn_machine p.

(** From partitioned BPF words (primary proof path). *)
Definition prefixgen_bpf : BpfRawProgram -> option Program :=
  BpfDecode.prefixgen_bpf.

(** From partitioned RV32 words. *)
Definition prefixgen_rv32 : Rv32RawProgram -> option Program :=
  Rv32Decode.prefixgen_rv32_words.

(** Object / ELF entry points (extraction still parametric). *)
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

End Prefixgen.
