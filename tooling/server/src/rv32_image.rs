//! Validate compact XDP ELF bindings and partition its RV32 instruction prefix.

#[cfg(test)]
use std::sync::OnceLock;

use std::str::FromStr;

use lean_binding::rv32::MapLayout;
use riscv_isa::{decode_le_bytes, Instruction, Target};

/// Default XDP fixture used when the client omits an uploaded image.
/// Checked in at `tooling/fixtures/just_tx.elf`.
pub const DEFAULT_ELF: &[u8] = include_bytes!("../../fixtures/just_tx.elf");
pub const DEFAULT_NAME: &str = "just_tx.elf";
/// Firewall fixture retained for helper-completion regressions.
#[cfg(test)]
pub const FIREWALL_ELF: &[u8] = include_bytes!("../../fixtures/xdp.elf");
#[cfg(test)]
const RAW_REGRESSION: &[u8] = include_bytes!("../../fixtures/esp32c3.bin");
pub const WRAPPER_RETURN: u32 = 0x2000;
/// Compact ELF ARRAY maps omit key layout; BPF array index is always 4 bytes.
const ARRAY_KEY_BYTES: u32 = 4;

#[derive(Debug, Clone)]
pub struct DecodedInsn {
    pub offset: u32,
    pub size: u8,
    pub word: u32,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct InsnImage {
    pub insns: Vec<DecodedInsn>,
}

#[derive(Debug, Clone)]
pub struct Rv32Program {
    pub image: InsnImage,
    pub base_address: u32,
    pub helper_address: u32,
    /// Map VMA + key/value sizes (`mapId` = AOT map address).
    pub maps: Vec<MapLayout>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ImageError {
    InvalidContainer,
    TrailingBytes,
    InvalidRange,
    BindingCollision,
    EmptyCode,
}

/// Wire layout descriptors are field widths in **bits** (xpost Compact ELF V0).
fn layout_byte_size(layout: &[u8]) -> Option<u32> {
    let mut bits: u32 = 0;
    for &w in layout {
        if w == 0 {
            return None;
        }
        bits = bits.checked_add(u32::from(w))?;
    }
    if !bits.is_multiple_of(8) {
        return None;
    }
    Some(bits / 8)
}

fn maps_from_parsed(parsed: &xpost_elf::ParsedContainer) -> Result<Vec<MapLayout>, ImageError> {
    let mut out = Vec::with_capacity(parsed.maps.len());
    for m in &parsed.maps {
        let value_size = layout_byte_size(m.value.as_ref().map(|v| v.as_slice()).unwrap_or(&[]))
            .filter(|&n| n > 0)
            .ok_or(ImageError::InvalidContainer)?;
        let key_size = match m.key.as_ref() {
            None => ARRAY_KEY_BYTES, // BPF_MAP_TYPE_ARRAY implicit u32 index
            Some(k) => layout_byte_size(k.as_slice())
                .filter(|&n| n > 0)
                .ok_or(ImageError::InvalidContainer)?,
        };
        out.push(MapLayout {
            map_id: m.vma,
            key_size,
            value_size,
        });
    }
    Ok(out)
}

pub fn parse_xdp_elf(bytes: &[u8]) -> Result<Rv32Program, ImageError> {
    let mut source = bytes;
    let xpost_elf::ScanOutcome::Ok(parsed) = xpost_elf::scan_at(&mut source, 0) else {
        return Err(ImageError::InvalidContainer);
    };
    if parsed.file_len != bytes.len() {
        return Err(ImageError::TrailingBytes);
    }
    let base = u32::try_from(parsed.slot_address).map_err(|_| ImageError::InvalidRange)?;
    let helper = u32::try_from(parsed.helper_address).map_err(|_| ImageError::InvalidRange)?;
    let size = u32::try_from(parsed.image_size).map_err(|_| ImageError::InvalidRange)?;
    let end_address = base.checked_add(size).ok_or(ImageError::InvalidRange)?;
    if (base..end_address).contains(&WRAPPER_RETURN)
        || helper == WRAPPER_RETURN
        || (base..end_address).contains(&helper)
    {
        return Err(ImageError::BindingCollision);
    }
    let end = parsed
        .image_offset
        .checked_add(parsed.image_size)
        .ok_or(ImageError::InvalidRange)?;
    let raw = bytes
        .get(parsed.image_offset..end)
        .ok_or(ImageError::InvalidRange)?;
    let image = decode_image(raw);
    let last = image.insns.last().ok_or(ImageError::EmptyCode)?;
    if last
        .offset
        .checked_add(u32::from(last.size))
        .is_none_or(|end| end > size)
    {
        return Err(ImageError::InvalidRange);
    }
    let maps = maps_from_parsed(&parsed)?;
    Ok(Rv32Program {
        image,
        base_address: base,
        helper_address: helper,
        maps,
    })
}

fn code_end(bin: &[u8]) -> usize {
    bin.windows(4)
        .position(|w| w == b"GPL\0")
        .unwrap_or(bin.len())
}

fn abi_reg(n: u32) -> &'static str {
    match n {
        0 => "zero",
        1 => "ra",
        2 => "sp",
        3 => "gp",
        4 => "tp",
        5 => "t0",
        6 => "t1",
        7 => "t2",
        8 => "s0",
        9 => "s1",
        10 => "a0",
        11 => "a1",
        12 => "a2",
        13 => "a3",
        14 => "a4",
        15 => "a5",
        16 => "a6",
        17 => "a7",
        18 => "s2",
        19 => "s3",
        20 => "s4",
        21 => "s5",
        22 => "s6",
        23 => "s7",
        24 => "s8",
        25 => "s9",
        26 => "s10",
        27 => "s11",
        28 => "t3",
        29 => "t4",
        30 => "t5",
        31 => "t6",
        _ => "?",
    }
}

fn x(n: impl Into<u32>) -> String {
    abi_reg(n.into()).to_string()
}

fn pretty(insn: &Instruction) -> String {
    use Instruction::*;
    match *insn {
        LUI { rd, imm } => format!("LUI {},{}", x(rd), imm),
        AUIPC { rd, imm } => format!("AUIPC {},{}", x(rd), imm),
        JAL { rd, offset } => format!("JAL {},{}", x(rd), offset),
        JALR { rd, rs1, offset } => format!("JALR {},{}({})", x(rd), offset, x(rs1)),
        BEQ { rs1, rs2, offset } => format!("BEQ {},{},{}", x(rs1), x(rs2), offset),
        BNE { rs1, rs2, offset } => format!("BNE {},{},{}", x(rs1), x(rs2), offset),
        BLT { rs1, rs2, offset } => format!("BLT {},{},{}", x(rs1), x(rs2), offset),
        BGE { rs1, rs2, offset } => format!("BGE {},{},{}", x(rs1), x(rs2), offset),
        BLTU { rs1, rs2, offset } => format!("BLTU {},{},{}", x(rs1), x(rs2), offset),
        BGEU { rs1, rs2, offset } => format!("BGEU {},{},{}", x(rs1), x(rs2), offset),
        LB { rd, rs1, offset } => format!("LB {},{}({})", x(rd), offset, x(rs1)),
        LH { rd, rs1, offset } => format!("LH {},{}({})", x(rd), offset, x(rs1)),
        LW { rd, rs1, offset } => format!("LW {},{}({})", x(rd), offset, x(rs1)),
        LBU { rd, rs1, offset } => format!("LBU {},{}({})", x(rd), offset, x(rs1)),
        LHU { rd, rs1, offset } => format!("LHU {},{}({})", x(rd), offset, x(rs1)),
        SB { rs1, rs2, offset } => format!("SB {},{}({})", x(rs2), offset, x(rs1)),
        SH { rs1, rs2, offset } => format!("SH {},{}({})", x(rs2), offset, x(rs1)),
        SW { rs1, rs2, offset } => format!("SW {},{}({})", x(rs2), offset, x(rs1)),
        ADDI { rd, rs1, imm } => format!("ADDI {},{},{}", x(rd), x(rs1), imm),
        SLTI { rd, rs1, imm } => format!("SLTI {},{},{}", x(rd), x(rs1), imm),
        SLTIU { rd, rs1, imm } => format!("SLTIU {},{},{}", x(rd), x(rs1), imm),
        XORI { rd, rs1, imm } => format!("XORI {},{},{}", x(rd), x(rs1), imm),
        ORI { rd, rs1, imm } => format!("ORI {},{},{}", x(rd), x(rs1), imm),
        ANDI { rd, rs1, imm } => format!("ANDI {},{},{}", x(rd), x(rs1), imm),
        SLLI { rd, rs1, shamt } => format!("SLLI {},{},{}", x(rd), x(rs1), shamt),
        SRLI { rd, rs1, shamt } => format!("SRLI {},{},{}", x(rd), x(rs1), shamt),
        SRAI { rd, rs1, shamt } => format!("SRAI {},{},{}", x(rd), x(rs1), shamt),
        ADD { rd, rs1, rs2 } => format!("ADD {},{},{}", x(rd), x(rs1), x(rs2)),
        SUB { rd, rs1, rs2 } => format!("SUB {},{},{}", x(rd), x(rs1), x(rs2)),
        SLL { rd, rs1, rs2 } => format!("SLL {},{},{}", x(rd), x(rs1), x(rs2)),
        SLT { rd, rs1, rs2 } => format!("SLT {},{},{}", x(rd), x(rs1), x(rs2)),
        SLTU { rd, rs1, rs2 } => format!("SLTU {},{},{}", x(rd), x(rs1), x(rs2)),
        XOR { rd, rs1, rs2 } => format!("XOR {},{},{}", x(rd), x(rs1), x(rs2)),
        SRL { rd, rs1, rs2 } => format!("SRL {},{},{}", x(rd), x(rs1), x(rs2)),
        SRA { rd, rs1, rs2 } => format!("SRA {},{},{}", x(rd), x(rs1), x(rs2)),
        OR { rd, rs1, rs2 } => format!("OR {},{},{}", x(rd), x(rs1), x(rs2)),
        AND { rd, rs1, rs2 } => format!("AND {},{},{}", x(rd), x(rs1), x(rs2)),
        MUL { rd, rs1, rs2 } => format!("MUL {},{},{}", x(rd), x(rs1), x(rs2)),
        MULH { rd, rs1, rs2 } => format!("MULH {},{},{}", x(rd), x(rs1), x(rs2)),
        MULHSU { rd, rs1, rs2 } => format!("MULHSU {},{},{}", x(rd), x(rs1), x(rs2)),
        MULHU { rd, rs1, rs2 } => format!("MULHU {},{},{}", x(rd), x(rs1), x(rs2)),
        DIV { rd, rs1, rs2 } => format!("DIV {},{},{}", x(rd), x(rs1), x(rs2)),
        DIVU { rd, rs1, rs2 } => format!("DIVU {},{},{}", x(rd), x(rs1), x(rs2)),
        REM { rd, rs1, rs2 } => format!("REM {},{},{}", x(rd), x(rs1), x(rs2)),
        REMU { rd, rs1, rs2 } => format!("REMU {},{},{}", x(rd), x(rs1), x(rs2)),
        FENCE { .. } => "FENCE".into(),
        FENCE_I => "FENCE.I".into(),
        ECALL => "ECALL".into(),
        EBREAK => "EBREAK".into(),
        other => format!("{other:?}"),
    }
}

pub fn decode_image(bin: &[u8]) -> InsnImage {
    let end = code_end(bin);
    let target = Target::from_str("RV32IMC").expect("RV32IMC target");
    let mut insns = Vec::new();
    let mut off = 0usize;
    while off < end {
        let Some((insn, len)) = decode_le_bytes(&bin[off..end], &target) else {
            break;
        };
        let word = if len == 2 {
            u16::from_le_bytes(bin[off..off + 2].try_into().unwrap()) as u32
        } else {
            u32::from_le_bytes(bin[off..off + 4].try_into().unwrap())
        };
        insns.push(DecodedInsn {
            offset: off as u32,
            size: len as u8,
            word,
            text: format!("{:04x} {}", off, pretty(&insn)),
        });
        off += len;
    }
    InsnImage { insns }
}

#[cfg(test)]
pub fn esp32c3_image() -> &'static InsnImage {
    static IMAGE: OnceLock<InsnImage> = OnceLock::new();
    IMAGE.get_or_init(|| decode_image(RAW_REGRESSION))
}

pub fn words(image: &InsnImage) -> Vec<u32> {
    image.insns.iter().map(|d| d.word).collect()
}

#[cfg(test)]
pub fn emit_lean_words(image: &InsnImage) -> String {
    let body = image
        .insns
        .iter()
        .map(|d| format!("0x{:x}", d.word))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "-- @generated by server::rv32_image from tooling/fixtures/esp32c3.bin (riscv-isa)\n\
         -- Do not edit. One UInt32 per insn (compressed in the low 16 bits).\n\
         namespace Cross.RV32\n\
         \n\
         def esp32c3Words : Array UInt32 := #[{body}]\n\
         \n\
         end Cross.RV32\n"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_real_compact_elf_bindings() {
        let program = parse_xdp_elf(DEFAULT_ELF).expect("real compact ELF");
        assert_eq!(program.base_address, 0x40380200);
        assert_eq!(program.helper_address, 0x40380000);
        assert_eq!(program.image.insns.len(), 79);
        assert!(program.image.insns[0].text.contains("ADDI"));
        // just_tx.c rxcnt: ARRAY key u32, value u64 at AOT 0x403802e8.
        assert_eq!(
            program.maps,
            vec![MapLayout {
                map_id: 0x4038_02e8,
                key_size: 4,
                value_size: 8,
            }]
        );
        let firewall = parse_xdp_elf(FIREWALL_ELF).expect("firewall compact ELF");
        assert_eq!(firewall.base_address, 0x40380200);
        assert_eq!(firewall.helper_address, 0x40380000);
        assert!(firewall.image.insns.iter().any(|i| i.offset == 0x64));
    }

    #[test]
    fn rejects_corrupt_and_noncanonical_containers() {
        assert_eq!(
            parse_xdp_elf(RAW_REGRESSION).unwrap_err(),
            ImageError::InvalidContainer
        );
        assert_eq!(
            parse_xdp_elf(&DEFAULT_ELF[..DEFAULT_ELF.len() - 1]).unwrap_err(),
            ImageError::InvalidContainer
        );
        let mut appended = DEFAULT_ELF.to_vec();
        appended.push(0);
        assert_eq!(
            parse_xdp_elf(&appended).unwrap_err(),
            ImageError::TrailingBytes
        );
        let mut corrupt = DEFAULT_ELF.to_vec();
        *corrupt.last_mut().unwrap() ^= 1;
        assert_eq!(
            parse_xdp_elf(&corrupt).unwrap_err(),
            ImageError::InvalidContainer
        );
        let mut profile = DEFAULT_ELF.to_vec();
        profile[213] = 2;
        assert_eq!(
            parse_xdp_elf(&profile).unwrap_err(),
            ImageError::InvalidContainer
        );
    }

    #[test]
    fn rejects_empty_instruction_prefix() {
        let metadata = xpost_elf::ImageMetadataV0 {
            slot_address: 0x40380200,
            helper_address: 0x40380000,
            machine: 1,
            name: "invalid".try_into().unwrap(),
            maps: Default::default(),
        };
        let bytes = xpost_elf::build_container(b"GPL\0", &metadata, None).unwrap();
        assert_eq!(parse_xdp_elf(&bytes).unwrap_err(), ImageError::EmptyCode);
    }

    #[test]
    fn rejects_invalid_address_bindings() {
        for (offset, value, expected) in [
            (144, 0xffff_fffc, ImageError::InvalidRange),
            (144, 0x2000, ImageError::BindingCollision),
            (216, 0x2000, ImageError::BindingCollision),
            (216, 0x40380200, ImageError::BindingCollision),
        ] {
            let mut bytes = DEFAULT_ELF.to_vec();
            bytes[offset..offset + 4].copy_from_slice(&u32::to_le_bytes(value));
            assert_eq!(parse_xdp_elf(&bytes).unwrap_err(), expected);
        }
    }

    #[test]
    fn partitions_full_esp32c3_image() {
        let image = esp32c3_image();
        assert_eq!(image.insns.len(), 48);
        assert_eq!(image.insns[0].offset, 0);
        assert_eq!(image.insns[0].size, 2);
        assert_eq!(image.insns[0].word, 0x4110);
        assert!(image.insns[0].text.contains("LW"));
        assert!(image.insns[0].text.contains("a2") || image.insns[0].text.contains("x12"));
        assert_eq!(image.insns.iter().map(|i| i.size as u32).sum::<u32>(), 0x80);
    }

    #[test]
    fn lean_words_match_checked_in() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../src/Cross/RV32/Program.lean");
        let expected = emit_lean_words(esp32c3_image());
        if std::env::var_os("UPDATE_ESP32C3_LEAN").is_some() {
            std::fs::write(&path, &expected).expect("write src/Cross/RV32/Program.lean");
        }
        let on_disk = std::fs::read_to_string(&path).expect("src/Cross/RV32/Program.lean");
        assert_eq!(on_disk, expected, "run UPDATE_ESP32C3_LEAN=1 lake test");
    }
}
