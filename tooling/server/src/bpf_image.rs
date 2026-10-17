//! Extract eBPF insn words (u64 LE) from an ELF64 bpf object.

/// Default eBPF object fixture (clang -target bpf).
pub const DEFAULT_BPF: &[u8] = include_bytes!("../../fixtures/just_tx.bpf.o");
/// Display name parallel to [`rv32_image::DEFAULT_NAME`].
pub const DEFAULT_BPF_NAME: &str = "just_tx.bpf.o";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BpfProgram {
    /// Contiguous 8-byte eBPF insn slots from the program section (lddw = 2 words).
    pub words: Vec<u64>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum BpfElfError {
    InvalidElf,
    UnsupportedClass,
    UnsupportedEndian,
    Truncated,
    MissingProgramSection,
    MisalignedSection,
}

/// Prefer a non-empty `.text`, else `xdp1` / `xdp` (clang often leaves `.text` empty).
pub fn extract_insn_words(bytes: &[u8]) -> Result<BpfProgram, BpfElfError> {
    let section = program_section_bytes(bytes)?;
    if section.len() % 8 != 0 {
        return Err(BpfElfError::MisalignedSection);
    }
    let words = section
        .as_chunks::<8>()
        .0
        .iter()
        .map(|c| u64::from_le_bytes(*c))
        .collect();
    Ok(BpfProgram { words })
}

/// Raw insn-slot indices of map LDDW loads (`R_BPF_64_64` / type 1 on the program section).
/// Empty when the object has no map relocations (e.g. merge_try).
pub fn map_lddw_slots(bytes: &[u8]) -> Result<Vec<u32>, BpfElfError> {
    const SHT_REL: u32 = 9;
    let headers = elf_headers(bytes)?;
    let prog_index = program_section_index(&headers)?;
    let mut slots = Vec::new();
    for sh in &headers.shdrs {
        if sh.sh_type != SHT_REL || sh.info != prog_index {
            continue;
        }
        if sh.entsize == 0 || sh.size % sh.entsize != 0 || sh.entsize < 16 {
            return Err(BpfElfError::MisalignedSection);
        }
        let rel = slice(bytes, sh.offset, sh.size)?;
        for chunk in rel.chunks_exact(sh.entsize) {
            let r_offset = u64::from_le_bytes(chunk[0..8].try_into().expect("8"));
            let r_info = u64::from_le_bytes(chunk[8..16].try_into().expect("8"));
            let r_type = (r_info & 0xffff_ffff) as u32;
            // R_BPF_64_64 = 1: LDDW map/fd relocation at the first of two words.
            if r_type != 1 {
                continue;
            }
            if r_offset % 8 != 0 {
                return Err(BpfElfError::MisalignedSection);
            }
            let slot = u32::try_from(r_offset / 8).map_err(|_| BpfElfError::Truncated)?;
            slots.push(slot);
        }
    }
    slots.sort_unstable();
    slots.dedup();
    Ok(slots)
}

struct ElfHeaders {
    shdrs: Vec<Shdr>,
    strtab: Vec<u8>,
}

fn elf_headers(bytes: &[u8]) -> Result<ElfHeaders, BpfElfError> {
    const ELFCLASS64: u8 = 2;
    const ELFDATA2LSB: u8 = 1;

    if bytes.len() < 64 || bytes.get(0..4) != Some(&[0x7f, b'E', b'L', b'F']) {
        return Err(BpfElfError::InvalidElf);
    }
    if bytes[4] != ELFCLASS64 {
        return Err(BpfElfError::UnsupportedClass);
    }
    if bytes[5] != ELFDATA2LSB {
        return Err(BpfElfError::UnsupportedEndian);
    }

    let e_shoff = read_u64(bytes, 40)? as usize;
    let e_shentsize = read_u16(bytes, 58)? as usize;
    let e_shnum = read_u16(bytes, 60)? as usize;
    let e_shstrndx = read_u16(bytes, 62)? as usize;
    if e_shentsize < 64 || e_shnum == 0 || e_shstrndx >= e_shnum {
        return Err(BpfElfError::InvalidElf);
    }

    let mut shdrs = Vec::with_capacity(e_shnum);
    for i in 0..e_shnum {
        shdrs.push(section_header(bytes, e_shoff, e_shentsize, i)?);
    }
    let shstr = &shdrs[e_shstrndx];
    let strtab = slice(bytes, shstr.offset, shstr.size)?.to_vec();
    Ok(ElfHeaders { shdrs, strtab })
}

fn program_section_index(headers: &ElfHeaders) -> Result<usize, BpfElfError> {
    const SHT_PROGBITS: u32 = 1;
    let mut text: Option<usize> = None;
    let mut xdp1: Option<usize> = None;
    let mut xdp: Option<usize> = None;
    for (i, sh) in headers.shdrs.iter().enumerate() {
        if sh.sh_type != SHT_PROGBITS || sh.size == 0 {
            continue;
        }
        let name = c_str_at(&headers.strtab, sh.name_off)?;
        match name {
            ".text" => text = Some(i),
            "xdp1" | ".xdp1" => xdp1 = Some(i),
            "xdp" | ".xdp" => xdp = Some(i),
            _ => {}
        }
    }
    text.or(xdp1)
        .or(xdp)
        .ok_or(BpfElfError::MissingProgramSection)
}

fn program_section_bytes(bytes: &[u8]) -> Result<&[u8], BpfElfError> {
    let headers = elf_headers(bytes)?;
    let idx = program_section_index(&headers)?;
    let sh = &headers.shdrs[idx];
    slice(bytes, sh.offset, sh.size)
}

struct Shdr {
    name_off: usize,
    sh_type: u32,
    offset: usize,
    size: usize,
    /// sh_info: for SHT_REL, the section index being relocated.
    info: usize,
    entsize: usize,
}

fn section_header(
    bytes: &[u8],
    e_shoff: usize,
    e_shentsize: usize,
    index: usize,
) -> Result<Shdr, BpfElfError> {
    let base = index
        .checked_mul(e_shentsize)
        .and_then(|o| e_shoff.checked_add(o))
        .ok_or(BpfElfError::Truncated)?;
    if base.saturating_add(56) > bytes.len() {
        return Err(BpfElfError::Truncated);
    }
    Ok(Shdr {
        name_off: read_u32(bytes, base)? as usize,
        sh_type: read_u32(bytes, base + 4)?,
        offset: read_u64(bytes, base + 24)? as usize,
        size: read_u64(bytes, base + 32)? as usize,
        // Elf64_Shdr: sh_link @ 40, sh_info @ 44, sh_entsize @ 56.
        info: read_u32(bytes, base + 44)? as usize,
        entsize: read_u64(bytes, base + 56)? as usize,
    })
}

fn c_str_at(strtab: &[u8], off: usize) -> Result<&str, BpfElfError> {
    let rest = strtab.get(off..).ok_or(BpfElfError::Truncated)?;
    let end = rest
        .iter()
        .position(|&b| b == 0)
        .ok_or(BpfElfError::Truncated)?;
    std::str::from_utf8(&rest[..end]).map_err(|_| BpfElfError::InvalidElf)
}

fn slice(bytes: &[u8], off: usize, size: usize) -> Result<&[u8], BpfElfError> {
    let end = off.checked_add(size).ok_or(BpfElfError::Truncated)?;
    bytes.get(off..end).ok_or(BpfElfError::Truncated)
}

fn read_u16(bytes: &[u8], off: usize) -> Result<u16, BpfElfError> {
    let b = bytes.get(off..off + 2).ok_or(BpfElfError::Truncated)?;
    Ok(u16::from_le_bytes([b[0], b[1]]))
}

fn read_u32(bytes: &[u8], off: usize) -> Result<u32, BpfElfError> {
    let b = bytes.get(off..off + 4).ok_or(BpfElfError::Truncated)?;
    Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
}

fn read_u64(bytes: &[u8], off: usize) -> Result<u64, BpfElfError> {
    let b = bytes.get(off..off + 8).ok_or(BpfElfError::Truncated)?;
    Ok(u64::from_le_bytes([
        b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
    ]))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn just_tx_bpf_has_58_insn_words() {
        let program = extract_insn_words(DEFAULT_BPF).expect(DEFAULT_BPF_NAME);
        // llvm-objdump -d: xdp1 ends at slot 57; lddw at 34 occupies two words (34+35).
        assert_eq!(program.words.len(), 58);
        // First insn: w0 = 1 → BPF_MOV | BPF_K | BPF_ALU, imm 1.
        assert_eq!(program.words[0], 0x0000_0001_0000_00b4);
        // lddw high word at slot 35 is zero immediate extension.
        assert_eq!(program.words[34] & 0xff, 0x18);
        assert_eq!(program.words[35], 0);
        // Last insn: exit.
        assert_eq!(program.words[57], 0x0000_0000_0000_0095);
    }

    #[test]
    fn just_tx_map_lddw_slot_is_34() {
        assert_eq!(map_lddw_slots(DEFAULT_BPF).expect("slots"), vec![34]);
    }

    #[test]
    fn just_drop_and_firewall_map_lddw_slots() {
        let drop_bpf = include_bytes!("../../test/xdp/just_drop/just_drop.bpf.o");
        let fw_bpf = include_bytes!("../../test/xdp/firewall/firewall.bpf.o");
        assert_eq!(map_lddw_slots(drop_bpf).expect("drop"), vec![25]);
        assert_eq!(map_lddw_slots(fw_bpf).expect("fw"), vec![24]);
    }

    #[test]
    fn rejects_non_elf() {
        assert_eq!(
            extract_insn_words(b"not elf").unwrap_err(),
            BpfElfError::InvalidElf
        );
    }
}
