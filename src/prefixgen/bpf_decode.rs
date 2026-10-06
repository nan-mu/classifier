//! Decode BPF instruction words into structured Prefix predicates.

use anyhow::{bail, Result};

use crate::predicate::{
    Address, AluOp, BitVec, CmpOp, Condition, Insn, Machine, MemWidth, Operand, Origin, Predicate,
    PredicateId, Prefix, Reg,
};
use crate::prefixgen::BpfRawProgram;

/// Annotate a partitioned BPF word sequence.
pub fn prefixgen_bpf_words(raw: BpfRawProgram) -> Result<Vec<Insn>> {
    let mut out = Vec::new();
    let mut id = 0u64;
    let mut i = 0usize;
    while i < raw.len() {
        let w = raw[i];
        let (pred, width) = decode_insn(w, raw.get(i + 1).copied())?;
        let mut prefix = Prefix::new();
        if let Some(p) = pred {
            prefix.push(PredicateId(id), p, Origin::stage("prefixgen"));
            id += 1;
        }
        out.push(Insn {
            index: i as u32,
            machine: Machine::Bpf(w),
            prefix,
        });
        if width == 2 {
            let cont = raw.get(i + 1).copied().ok_or_else(|| {
                anyhow::anyhow!("BPF lddw at {i} missing continuation slot")
            })?;
            out.push(Insn {
                index: (i + 1) as u32,
                machine: Machine::Bpf(cont),
                prefix: Prefix::new(),
            });
            i += 2;
        } else {
            i += 1;
        }
    }
    Ok(out)
}

fn decode_insn(w: u64, next: Option<u64>) -> Result<(Option<Predicate>, u8)> {
    let code = (w & 0xff) as u8;
    let dst = ((w >> 8) & 0xf) as u8;
    let src = ((w >> 12) & 0xf) as u8;
    let off = (w >> 16) as i16;
    let imm = (w >> 32) as i32;

    let class = code & 0x07;
    let op = code & 0xf0;
    let size = code & 0x18;
    let mode = code & 0xe0;

    match class {
        0x00 | 0x01 => {
            // BPF_LD / BPF_LDX
            // lddw: BPF_LD | BPF_DW | BPF_IMM → opcode 0x18
            if class == 0x00 && size == 0x18 && mode == 0x00 {
                let hi = next.ok_or_else(|| anyhow::anyhow!("lddw missing second word"))?;
                let imm64 = (imm as u32 as u64) | ((hi >> 32) << 32);
                return Ok((
                    Some(Predicate::Set {
                        dst: Reg::r(dst as u32),
                        src: Operand::Imm(BitVec::Bv64(imm64)),
                    }),
                    2,
                ));
            }
            if class == 0x01 && mode == 0x60 {
                // LDX MEM
                let width = mem_width(size)?;
                return Ok((
                    Some(Predicate::Load {
                        dst: dst_reg_for_load(dst, width),
                        width,
                        addr: address(src, off),
                    }),
                    1,
                ));
            }
            bail!("unsupported BPF_LD/LDX opcode {code:#04x}")
        }
        0x02 | 0x03 => {
            // ST / STX MEM
            if mode != 0x60 {
                bail!("unsupported BPF_ST mode {mode:#x}");
            }
            let width = mem_width(size)?;
            let src_op = if class == 0x02 {
                Operand::Imm(BitVec::Bv32(imm as u32))
            } else {
                Operand::Reg(src_reg_for_store(src, width))
            };
            Ok((
                Some(Predicate::Store {
                    width,
                    addr: address(dst, off),
                    src: src_op,
                }),
                1,
            ))
        }
        0x04 => Ok((Some(decode_alu(false, op, code, dst, src, imm)?), 1)),
        0x05 => Ok((Some(decode_jmp(true, op, code, dst, src, imm, off)?), 1)),
        0x06 => Ok((Some(decode_jmp(false, op, code, dst, src, imm, off)?), 1)),
        0x07 => Ok((Some(decode_alu(true, op, code, dst, src, imm)?), 1)),
        _ => bail!("unknown BPF class in {code:#04x} (word {w:#018x})"),
    }
}

fn decode_alu(
    is64: bool,
    op: u8,
    code: u8,
    dst: u8,
    src: u8,
    imm: i32,
) -> Result<Predicate> {
    let src_reg = (code & 0x08) != 0;
    let d = if is64 {
        Reg::r(dst as u32)
    } else {
        Reg::w(dst as u32)
    };
    let rhs = if src_reg {
        Operand::Reg(if is64 {
            Reg::r(src as u32)
        } else {
            Reg::w(src as u32)
        })
    } else if is64 {
        Operand::Imm(BitVec::Bv64(imm as i64 as u64))
    } else {
        Operand::Imm(BitVec::Bv32(imm as u32))
    };

    match op {
        0xb0 => Ok(Predicate::Set { dst: d, src: rhs }), // MOV
        0x00 => Ok(alu_assign(d, AluOp::Add, rhs)),
        0x10 => Ok(alu_assign(d, AluOp::Sub, rhs)),
        0x20 => Ok(alu_assign(d, AluOp::Mul, rhs)),
        0x30 => Ok(alu_assign(d, AluOp::Divu, rhs)),
        0x40 => Ok(alu_assign(d, AluOp::Or, rhs)),
        0x50 => Ok(alu_assign(d, AluOp::And, rhs)),
        0x60 => Ok(alu_assign(d, AluOp::Shl, rhs)),
        0x70 => Ok(alu_assign(d, AluOp::Lshr, rhs)),
        0x90 => Ok(alu_assign(d, AluOp::Remu, rhs)),
        0xa0 => Ok(alu_assign(d, AluOp::Xor, rhs)),
        0xc0 => Ok(alu_assign(d, AluOp::Ashr, rhs)),
        0x80 => Ok(Predicate::Alu {
            dst: d.clone(),
            op: AluOp::Sub,
            lhs: Operand::Imm(if is64 {
                BitVec::Bv64(0)
            } else {
                BitVec::Bv32(0)
            }),
            rhs: Operand::Reg(d),
        }),
        _ => bail!("unsupported ALU op {op:#x}"),
    }
}

fn alu_assign(dst: Reg, op: AluOp, rhs: Operand) -> Predicate {
    Predicate::AluAssign { dst, op, rhs }
}

fn decode_jmp(
    is64: bool,
    op: u8,
    code: u8,
    dst: u8,
    src: u8,
    imm: i32,
    off: i16,
) -> Result<Predicate> {
    match op {
        0x80 => Ok(Predicate::Call {
            target: format!("{imm:#x}"),
        }),
        0x90 => Ok(Predicate::Exit),
        0x00 => Ok(Predicate::Goto {
            offset: format_off(off),
        }),
        _ => {
            let src_reg = (code & 0x08) != 0;
            let lhs = Operand::Reg(if is64 {
                Reg::r(dst as u32)
            } else {
                Reg::w(dst as u32)
            });
            let rhs = if src_reg {
                Operand::Reg(if is64 {
                    Reg::r(src as u32)
                } else {
                    Reg::w(src as u32)
                })
            } else if is64 {
                Operand::Imm(BitVec::Bv64(imm as i64 as u64))
            } else {
                Operand::Imm(BitVec::Bv32(imm as u32))
            };
            let cmp = match op {
                0x10 => CmpOp::Eq,
                0x20 => CmpOp::Gt,
                0x30 => CmpOp::Ge,
                0x50 => CmpOp::Ne,
                0x60 => CmpOp::Sgt,
                0x70 => CmpOp::Sge,
                0xa0 => CmpOp::Lt,
                0xb0 => CmpOp::Le,
                0xc0 => CmpOp::Slt,
                0xd0 => CmpOp::Sle,
                0x40 => bail!("BPF_JSET not supported in prefixgen"),
                _ => bail!("unsupported JMP op {op:#x}"),
            };
            Ok(Predicate::IfGoto {
                condition: Condition {
                    lhs,
                    op: cmp,
                    rhs,
                },
                offset: format_off(off),
            })
        }
    }
}

fn format_off(off: i16) -> String {
    if off >= 0 {
        format!("+{off:#x}")
    } else {
        format!("-{0:#x}", (-(off as i32)) as u32)
    }
}

fn mem_width(size: u8) -> Result<MemWidth> {
    match size {
        0x00 => Ok(MemWidth::U32),
        0x08 => Ok(MemWidth::U16),
        0x10 => Ok(MemWidth::U8),
        0x18 => Ok(MemWidth::U64),
        _ => bail!("unsupported mem size {size:#x}"),
    }
}

fn address(base: u8, off: i16) -> Address {
    let off32 = off as i32;
    Address {
        base: Reg::r(base as u32),
        offset: if off32 == 0 {
            None
        } else {
            Some(BitVec::Bv64(off32 as i64 as u64))
        },
    }
}

fn dst_reg_for_load(n: u8, width: MemWidth) -> Reg {
    match width {
        MemWidth::U64 => Reg::r(n as u32),
        _ => Reg::w(n as u32),
    }
}

fn src_reg_for_store(n: u8, width: MemWidth) -> Reg {
    dst_reg_for_load(n, width)
}
