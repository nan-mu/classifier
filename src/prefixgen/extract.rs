//! Extract partitioned machine code from host ELF artifacts.

use anyhow::{bail, Context, Result};
use object::{Object, ObjectSection, SectionKind};
use std::path::Path;

use crate::prefixgen::BpfRawProgram;

/// Extract BPF program words from a relocatable `bpf.o`.
///
/// Prefers an executable section named `xdp*` with non-empty data.
/// Length must be a multiple of 8. Relocations are **not** applied: raw
/// section bytes are kept (unresolved `R_BPF_64_64` map immediates stay 0).
pub fn extract_bpf_words(object_bytes: &[u8]) -> Result<BpfRawProgram> {
    let file = object::File::parse(object_bytes).context("parse BPF ELF")?;
    let section = select_bpf_prog_section(&file)?;
    let name = section.name().unwrap_or("<unnamed>").to_string();
    let data = section
        .data()
        .with_context(|| format!("read section {name}"))?;
    if data.len() % 8 != 0 {
        bail!(
            "BPF program section `{name}` length {} is not a multiple of 8",
            data.len()
        );
    }
    let mut words = Vec::with_capacity(data.len() / 8);
    for chunk in data.chunks_exact(8) {
        words.push(u64::from_le_bytes(chunk.try_into().unwrap()));
    }
    if words.is_empty() {
        bail!("BPF program section `{name}` is empty");
    }
    Ok(words)
}

fn select_bpf_prog_section<'data, 'file>(
    file: &'file object::File<'data>,
) -> Result<object::Section<'data, 'file>> {
    let mut xdp = None;
    let mut textish = None;
    for section in file.sections() {
        let Ok(name) = section.name() else {
            continue;
        };
        if section.size() == 0 {
            continue;
        }
        let is_code = matches!(section.kind(), SectionKind::Text)
            || name.starts_with("xdp")
            || name == ".text";
        if !is_code {
            continue;
        }
        if name.starts_with("xdp") {
            xdp = Some(section);
            break;
        }
        if textish.is_none() && name != ".text" {
            textish = Some(section);
        } else if textish.is_none() {
            textish = Some(section);
        }
    }
    xdp.or(textish)
        .ok_or_else(|| anyhow::anyhow!("no BPF program section found (expected xdp*)"))
}

/// Extract the RV32IMC flat image from an xpost compact ELF (`.xpost.image`).
pub fn extract_rv32_image(elf_bytes: &[u8]) -> Result<Vec<u8>> {
    let file = object::File::parse(elf_bytes).context("parse RV32 ELF")?;
    for section in file.sections() {
        let Ok(name) = section.name() else {
            continue;
        };
        if name == ".xpost.image" {
            let data = section.data().context("read .xpost.image")?;
            if data.is_empty() {
                bail!(".xpost.image is empty");
            }
            return Ok(data.to_vec());
        }
    }
    bail!("missing .xpost.image section")
}

pub fn extract_bpf_words_from_path(path: &Path) -> Result<BpfRawProgram> {
    let bytes = std::fs::read(path).with_context(|| format!("read {}", path.display()))?;
    extract_bpf_words(&bytes).with_context(|| format!("extract BPF from {}", path.display()))
}

pub fn extract_rv32_image_from_path(path: &Path) -> Result<Vec<u8>> {
    let bytes = std::fs::read(path).with_context(|| format!("read {}", path.display()))?;
    extract_rv32_image(&bytes).with_context(|| format!("extract RV32 from {}", path.display()))
}
