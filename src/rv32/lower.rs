//! Decode bytes into [`Op`] (former T-1 without Isla footprint checks).
use super::decode::{decode_rv32imc, DecodedInsn};
use super::environment::Environment;
use super::op::*;
use anyhow::{bail, ensure, Context, Result};
use riscv_isa::{decode_le_bytes, Instruction as I, Target};
use std::collections::BTreeMap;

/// Lower a flat image to an indexed instruction table.
pub fn lower_bin(bin: &[u8], env: &Environment) -> Result<Path> {
    env.validate()?;
    let raw = decode_rv32imc(bin)?;
    lower_decoded(&raw, env)
}

pub fn lower_decoded(input: &[DecodedInsn], env: &Environment) -> Result<Path> {
    env.validate()?;
    ensure!(!input.is_empty(), "lower: empty image");
    let target: Target = "RV32IMC".parse().unwrap();
    let mut offset = 0usize;
    let mut decoded = Vec::new();
    let mut layout = BTreeMap::new();
    for (i, f) in input.iter().enumerate() {
        ensure!(
            f.offset == offset,
            "lower index {i}: non-contiguous byte layout"
        );
        let (ins, len) =
            decode_le_bytes(&f.bytes, &target).context("lower: truncated opcode")?;
        ensure!(len == f.bytes.len(), "lower index {i}: opcode length mismatch");
        let hex: String = f.bytes.iter().map(|b| format!("{b:02x}")).collect();
        ensure!(
            hex == f.hex.to_ascii_lowercase(),
            "lower index {i}: hex/bytes mismatch"
        );
        let pc = env
            .image_base
            .checked_add(u32::try_from(offset)?)
            .context("lower: PC overflow")?;
        layout.insert(pc, i);
        decoded.push((ins, pc, len));
        offset += len;
    }
    ensure!(env.entry < input.len(), "lower: entry outside instruction table");
    let mut out = Vec::new();
    let mut pair_sites = Vec::new();
    for (index, (ins, pc, len)) in decoded.iter().copied().enumerate() {
        let next_pc = pc
            .checked_add(len as u32)
            .context("lower: PC successor overflow")?;
        let branch_target = |delta: i32| -> Result<usize> {
            let addr = (pc as i64) + (delta as i64);
            ensure!(
                (0..=u32::MAX as i64).contains(&addr),
                "PC-relative target wraps"
            );
            layout
                .get(&(addr as u32))
                .copied()
                .with_context(|| format!("target {addr:#x} is not an instruction entry"))
        };
        let make_call = |target: u32| -> Result<Op> {
            ensure!(index + 1 < input.len(), "call has no continuation");
            let c = env.call(index)?;
            ensure!(
                c.target == target,
                "call target {target:#x} disagrees with contract {:#x}",
                c.target
            );
            Ok(Op::Call {
                target,
                link: next_pc,
                next: index + 1,
            })
        };
        let lower = || -> Result<Op> {
            macro_rules! alu {
                ($rd:expr,$k:ident,$a:expr,$b:expr) => {
                    Op::Alu {
                        rd: $rd,
                        kind: Alu::$k,
                        a: Operand::Reg($a),
                        b: $b,
                    }
                };
            }
            macro_rules! load {
                ($rd:expr,$r:expr,$o:expr,$s:expr,$sign:expr) => {
                    Op::Load {
                        rd: $rd,
                        base: $r,
                        offset: $o,
                        size: $s,
                        signed: $sign,
                    }
                };
            }
            macro_rules! store {
                ($r:expr,$s:expr,$o:expr,$n:expr) => {
                    Op::Store {
                        src: $s,
                        base: $r,
                        offset: $o,
                        size: $n,
                    }
                };
            }
            macro_rules! br {
                ($k:ident,$a:expr,$b:expr,$o:expr) => {
                    Op::Branch {
                        cmp: Cmp::$k,
                        a: $a,
                        b: $b,
                        target: branch_target($o)?,
                    }
                };
            }
            Ok(match ins {
                I::LUI { rd, imm } => Op::Set {
                    rd,
                    src: Operand::Imm(imm << 12),
                },
                I::AUIPC { rd, imm } => Op::Set {
                    rd,
                    src: Operand::Imm(pc.wrapping_add(imm << 12)),
                },
                I::ADDI { rd, rs1, imm: 0 } => Op::Set {
                    rd,
                    src: Operand::Reg(rs1),
                },
                I::ADDI { rd, rs1: 0, imm } => Op::Set {
                    rd,
                    src: Operand::Imm(imm as u32),
                },
                I::ADD { rd, rs1: 0, rs2 }
                | I::ADD {
                    rd,
                    rs1: rs2,
                    rs2: 0,
                } => Op::Set {
                    rd,
                    src: Operand::Reg(rs2),
                },
                I::ADDI { rd, rs1, imm } => alu!(rd, Add, rs1, Operand::Imm(imm as u32)),
                I::SLTI { rd, rs1, imm } => alu!(rd, Slt, rs1, Operand::Imm(imm as u32)),
                I::SLTIU { rd, rs1, imm } => alu!(rd, Sltu, rs1, Operand::Imm(imm as u32)),
                I::XORI { rd, rs1, imm } => alu!(rd, Xor, rs1, Operand::Imm(imm as u32)),
                I::ORI { rd, rs1, imm } => alu!(rd, Or, rs1, Operand::Imm(imm as u32)),
                I::ANDI { rd, rs1, imm } => alu!(rd, And, rs1, Operand::Imm(imm as u32)),
                I::SLLI { rd, rs1, shamt } => alu!(rd, Shl, rs1, Operand::Imm(shamt)),
                I::SRLI { rd, rs1, shamt } => alu!(rd, Lshr, rs1, Operand::Imm(shamt)),
                I::SRAI { rd, rs1, shamt } => alu!(rd, Ashr, rs1, Operand::Imm(shamt)),
                I::ADD { rd, rs1, rs2 } => alu!(rd, Add, rs1, Operand::Reg(rs2)),
                I::SUB { rd, rs1, rs2 } => alu!(rd, Sub, rs1, Operand::Reg(rs2)),
                I::AND { rd, rs1, rs2 } => alu!(rd, And, rs1, Operand::Reg(rs2)),
                I::OR { rd, rs1, rs2 } => alu!(rd, Or, rs1, Operand::Reg(rs2)),
                I::XOR { rd, rs1, rs2 } => alu!(rd, Xor, rs1, Operand::Reg(rs2)),
                I::SLL { rd, rs1, rs2 } => alu!(rd, Shl, rs1, Operand::Reg(rs2)),
                I::SRL { rd, rs1, rs2 } => alu!(rd, Lshr, rs1, Operand::Reg(rs2)),
                I::SRA { rd, rs1, rs2 } => alu!(rd, Ashr, rs1, Operand::Reg(rs2)),
                I::SLT { rd, rs1, rs2 } => alu!(rd, Slt, rs1, Operand::Reg(rs2)),
                I::SLTU { rd, rs1, rs2 } => alu!(rd, Sltu, rs1, Operand::Reg(rs2)),
                I::MUL { rd, rs1, rs2 } => alu!(rd, Mul, rs1, Operand::Reg(rs2)),
                I::MULH { rd, rs1, rs2 } => alu!(rd, Mulh, rs1, Operand::Reg(rs2)),
                I::MULHU { rd, rs1, rs2 } => alu!(rd, Mulhu, rs1, Operand::Reg(rs2)),
                I::MULHSU { rd, rs1, rs2 } => alu!(rd, Mulhsu, rs1, Operand::Reg(rs2)),
                I::DIV { rd, rs1, rs2 } => alu!(rd, Div, rs1, Operand::Reg(rs2)),
                I::DIVU { rd, rs1, rs2 } => alu!(rd, Divu, rs1, Operand::Reg(rs2)),
                I::REM { rd, rs1, rs2 } => alu!(rd, Rem, rs1, Operand::Reg(rs2)),
                I::REMU { rd, rs1, rs2 } => alu!(rd, Remu, rs1, Operand::Reg(rs2)),
                I::LB { rd, rs1, offset } => load!(rd, rs1, offset, 1, true),
                I::LH { rd, rs1, offset } => load!(rd, rs1, offset, 2, true),
                I::LW { rd, rs1, offset } => load!(rd, rs1, offset, 4, false),
                I::LBU { rd, rs1, offset } => load!(rd, rs1, offset, 1, false),
                I::LHU { rd, rs1, offset } => load!(rd, rs1, offset, 2, false),
                I::SB { rs1, rs2, offset } => store!(rs1, rs2, offset, 1),
                I::SH { rs1, rs2, offset } => store!(rs1, rs2, offset, 2),
                I::SW { rs1, rs2, offset } => store!(rs1, rs2, offset, 4),
                I::BEQ { rs1, rs2, offset } => br!(Eq, rs1, rs2, offset),
                I::BNE { rs1, rs2, offset } => br!(Ne, rs1, rs2, offset),
                I::BLT { rs1, rs2, offset } => br!(Lt, rs1, rs2, offset),
                I::BGE { rs1, rs2, offset } => br!(Ge, rs1, rs2, offset),
                I::BLTU { rs1, rs2, offset } => br!(Ltu, rs1, rs2, offset),
                I::BGEU { rs1, rs2, offset } => br!(Geu, rs1, rs2, offset),
                I::JAL { rd: 0, offset } => Op::Jump(branch_target(offset)?),
                I::JAL { rd: 1, offset } => make_call(pc.wrapping_add_signed(offset))?,
                I::JALR {
                    rd: 0,
                    rs1: 1,
                    offset: 0,
                } => Op::Exit,
                I::JALR { rd: 1, rs1, offset } => {
                    ensure!(index > 0, "unresolved JALR");
                    let (prior, prior_pc, _) = decoded[index - 1];
                    let I::AUIPC { rd, imm } = prior else {
                        bail!("JALR requires adjacent AUIPC")
                    };
                    ensure!(rd == rs1, "AUIPC/JALR register mismatch");
                    make_call(prior_pc.wrapping_add(imm << 12).wrapping_add_signed(offset) & !1)?
                }
                I::UNIMP if input[index].bytes == [0, 0] => Op::Trap,
                _ => bail!("unsupported or unknown instruction {ins:?}"),
            })
        };
        let op = lower().with_context(|| format!("lower index {index}"))?;
        if matches!(ins, I::JALR { rd: 1, .. }) {
            pair_sites.push(index);
        }
        out.push(Line::new(index, op));
    }
    for site in pair_sites {
        ensure!(
            env.entry != site,
            "lower: entry bypasses AUIPC at call {site}"
        );
        for line in &out {
            ensure!(
                !matches!(line.op, Op::Jump(t) | Op::Branch { target: t, .. } if t == site),
                "lower: control edge bypasses AUIPC at call {site}"
            );
        }
    }
    for c in &env.calls {
        ensure!(
            out.get(c.index)
                .is_some_and(|l| matches!(l.op, Op::Call { .. })),
            "lower: contract {} does not name a call",
            c.index
        );
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn c_addi_sp_lowers_to_inplace_add() {
        let env = Environment::default();
        let table = lower_bin(&[0x41, 0x11], &env).unwrap();
        assert_eq!(table[0].body, "w2 += -0x10");
    }
}
