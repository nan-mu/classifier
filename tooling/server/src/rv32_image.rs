//! Partition and label `esp32c3.bin` with `riscv-isa` (strict 2/4-byte RV32IMC lengths).

use std::sync::OnceLock;

use std::str::FromStr;

use riscv_isa::{decode_le_bytes, Instruction, Target};

/// Default XDP fixture used when the client omits an uploaded image.
pub const DEFAULT_BIN: &[u8] = include_bytes!("../../fixtures/esp32c3.bin");
pub const DEFAULT_NAME: &str = "esp32c3.bin";

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

pub fn esp32c3_image() -> &'static InsnImage {
    static IMAGE: OnceLock<InsnImage> = OnceLock::new();
    IMAGE.get_or_init(|| decode_image(DEFAULT_BIN))
}

pub fn words(image: &InsnImage) -> Vec<u32> {
    image.insns.iter().map(|d| d.word).collect()
}

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
         namespace RV32IMC\n\
         \n\
         def esp32c3Words : Array UInt32 := #[{body}]\n\
         \n\
         end RV32IMC\n"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

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
            .join("../../RV32IMC/Esp32c3Program.lean");
        let expected = emit_lean_words(esp32c3_image());
        if std::env::var_os("UPDATE_ESP32C3_LEAN").is_some() {
            std::fs::write(&path, &expected).expect("write Esp32c3Program.lean");
        }
        let on_disk = std::fs::read_to_string(&path).expect("Esp32c3Program.lean");
        assert_eq!(on_disk, expected, "run UPDATE_ESP32C3_LEAN=1 lake test");
    }
}
