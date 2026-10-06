//! Prefix generation: raw machine slots → [`Insn`] with BPF-asm-style [`Prefix`].

mod bpf;
mod bpf_decode;
mod extract;
mod rv32;

pub use bpf::prefixgen_bpf_asm;
pub use bpf_decode::prefixgen_bpf_words;
pub use extract::{
    extract_bpf_words, extract_bpf_words_from_path, extract_rv32_image,
    extract_rv32_image_from_path,
};
pub use rv32::prefixgen_rv32;

use anyhow::Result;
use std::path::Path;

use crate::predicate::{Insn, Machine};
use crate::rv32::Environment;

/// Architecture directory name under the output root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arch {
    Bpf,
    Rv32imc,
}

impl Arch {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Bpf => "bpf",
            Self::Rv32imc => "rv32imc",
        }
    }
}

pub const TASK_PREFIXGEN: &str = "prefixgen";

/// RV32IMC raw instruction word (16- or 32-bit).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum U32OrU16 {
    U32(u32),
    U16(u16),
}

impl U32OrU16 {
    pub fn to_machine(self) -> Machine {
        match self {
            Self::U32(w) => Machine::Rv32(w),
            Self::U16(w) => Machine::Rv16(w),
        }
    }
}

pub type BpfRawProgram = Vec<u64>;
pub type Rv32RawProgram = Vec<U32OrU16>;

/// Split a flat RV32IMC image into raw instruction words (LE).
pub fn split_rv32imc(code: &[u8]) -> anyhow::Result<Rv32RawProgram> {
    let decoded = crate::rv32::decode::decode_rv32imc(code)?;
    let mut out = Vec::with_capacity(decoded.len());
    for d in decoded {
        match d.bytes.len() {
            2 => {
                let w = u16::from_le_bytes([d.bytes[0], d.bytes[1]]);
                out.push(U32OrU16::U16(w));
            }
            4 => {
                let w = u32::from_le_bytes([d.bytes[0], d.bytes[1], d.bytes[2], d.bytes[3]]);
                out.push(U32OrU16::U32(w));
            }
            n => anyhow::bail!("split_rv32imc: unexpected insn length {n}"),
        }
    }
    Ok(out)
}

/// `bpf.o` → annotated program.
pub fn prefixgen_bpf_object(path: &Path) -> Result<Vec<Insn>> {
    let raw = extract_bpf_words_from_path(path)?;
    prefixgen_bpf_words(raw)
}

/// `just_tx.elf` (or any xpost ELF) → annotated RV32 program.
pub fn prefixgen_rv32_elf(path: &Path, env: &Environment) -> Result<Vec<Insn>> {
    let image = extract_rv32_image_from_path(path)?;
    prefixgen_rv32(&image, env)
}

/// Format a linear program as emit lines (index column aligned).
pub fn emit_lines(insns: &[Insn]) -> Vec<String> {
    let width = crate::predicate::index_column_width(insns);
    insns.iter().map(|i| i.emit_line(width)).collect()
}
