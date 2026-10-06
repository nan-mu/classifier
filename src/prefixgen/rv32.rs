//! RV32IMC raw image → annotated [`Insn`] sequence.

use anyhow::{bail, Result};

use crate::predicate::{
    Address, AluOp, BitVec, CmpOp, Condition, Insn, Machine, MemWidth, Operand, Origin, Predicate,
    PredicateId, Prefix, Reg,
};
use crate::prefixgen::U32OrU16;
use crate::rv32::environment::Environment;
use crate::rv32::lower::lower_bin;
use crate::rv32::op::{Alu, Cmp, Op, Operand as RvOperand};

/// Annotate an RV32IMC flat image under `env`.
pub fn prefixgen_rv32(bin: &[u8], env: &Environment) -> Result<Vec<Insn>> {
    let raw = crate::prefixgen::split_rv32imc(bin)?;
    let lines = lower_bin(bin, env)?;
    if raw.len() != lines.len() {
        bail!(
            "prefixgen_rv32: raw len {} != lowered len {}",
            raw.len(),
            lines.len()
        );
    }
    let mut id = 0u64;
    let mut out = Vec::with_capacity(lines.len());
    for (slot, line) in lines.into_iter().enumerate() {
        let machine = match raw[slot] {
            U32OrU16::U32(w) => Machine::Rv32(w),
            U32OrU16::U16(w) => Machine::Rv16(w),
        };
        let mut prefix = Prefix::new();
        if let Some(pred) = op_to_predicate(&line.op, line.index)? {
            prefix.push(
                PredicateId(id),
                pred,
                Origin::stage("prefixgen"),
            );
            id += 1;
        }
        out.push(Insn {
            index: slot as u32,
            machine,
            prefix,
        });
    }
    Ok(out)
}

fn op_to_predicate(op: &Op, index: usize) -> Result<Option<Predicate>> {
    Ok(Some(match *op {
        Op::Set { rd: 0, .. } | Op::Alu { rd: 0, .. } => return Ok(None),
        Op::Set { rd, src } => Predicate::Set {
            dst: Reg::w(rd),
            src: rv_operand(src),
        },
        Op::Alu { rd, kind, a, b } => alu_pred(rd, kind, a, b),
        Op::Load {
            rd: 0,
            ..
        } => {
            bail!("prefixgen: load to x0 is unsupported (exception/order not modeled)")
        }
        Op::Load {
            rd,
            base,
            offset,
            size,
            signed,
        } => Predicate::Load {
            dst: Reg::w(rd),
            width: MemWidth::from_size_signed(size, signed)
                .ok_or_else(|| anyhow::anyhow!("unsupported load width {size}"))?,
            addr: address(base, offset),
        },
        Op::Store {
            src,
            base,
            offset,
            size,
        } => Predicate::Store {
            width: MemWidth::from_size_signed(size, false)
                .ok_or_else(|| anyhow::anyhow!("unsupported store width {size}"))?,
            addr: address(base, offset),
            src: Operand::Reg(Reg::w(src)),
        },
        Op::Branch { cmp, a, b, target } => Predicate::IfGoto {
            condition: cmp_cond(cmp, a, b),
            offset: rel_goto(index, target),
        },
        Op::Assert { cmp, a, b, taken } => Predicate::Assert {
            condition: cmp_cond(cmp, a, b),
            expected: taken,
        },
        Op::Jump(t) => Predicate::Goto {
            offset: rel_goto(index, t),
        },
        Op::Call { target, .. } => Predicate::Call {
            target: format!("{target:#x}"),
        },
        Op::Exit => Predicate::Exit,
        Op::Trap => Predicate::Trap {
            reason: "IllegalInstruction".into(),
        },
    }))
}

fn alu_pred(rd: u32, kind: Alu, a: RvOperand, b: RvOperand) -> Predicate {
    match kind {
        Alu::Slt => Predicate::AluCall {
            dst: Reg::w(rd),
            name: "slt",
            lhs: rv_operand(a),
            rhs: rv_operand(b),
        },
        Alu::Sltu => Predicate::AluCall {
            dst: Reg::w(rd),
            name: "sltu",
            lhs: rv_operand(a),
            rhs: rv_operand(b),
        },
        Alu::Mulh => Predicate::AluCall {
            dst: Reg::w(rd),
            name: "mulh",
            lhs: rv_operand(a),
            rhs: rv_operand(b),
        },
        Alu::Mulhu => Predicate::AluCall {
            dst: Reg::w(rd),
            name: "mulhu",
            lhs: rv_operand(a),
            rhs: rv_operand(b),
        },
        Alu::Mulhsu => Predicate::AluCall {
            dst: Reg::w(rd),
            name: "mulhsu",
            lhs: rv_operand(a),
            rhs: rv_operand(b),
        },
        other => {
            let op = alu_op(other);
            if matches!(a, RvOperand::Reg(r) if r == rd) {
                Predicate::AluAssign {
                    dst: Reg::w(rd),
                    op,
                    rhs: rv_operand(b),
                }
            } else {
                Predicate::Alu {
                    dst: Reg::w(rd),
                    op,
                    lhs: rv_operand(a),
                    rhs: rv_operand(b),
                }
            }
        }
    }
}

fn alu_op(k: Alu) -> AluOp {
    match k {
        Alu::Add => AluOp::Add,
        Alu::Sub => AluOp::Sub,
        Alu::And => AluOp::And,
        Alu::Or => AluOp::Or,
        Alu::Xor => AluOp::Xor,
        Alu::Shl => AluOp::Shl,
        Alu::Lshr => AluOp::Lshr,
        Alu::Ashr => AluOp::Ashr,
        Alu::Mul => AluOp::Mul,
        Alu::Div => AluOp::Div,
        Alu::Divu => AluOp::Divu,
        Alu::Rem => AluOp::Rem,
        Alu::Remu => AluOp::Remu,
        Alu::Slt | Alu::Sltu | Alu::Mulh | Alu::Mulhu | Alu::Mulhsu => {
            unreachable!("handled as AluCall")
        }
    }
}

fn rv_operand(o: RvOperand) -> Operand {
    match o {
        RvOperand::Reg(0) => Operand::Imm(BitVec::Bv32(0)),
        RvOperand::Reg(r) => Operand::Reg(Reg::w(r)),
        RvOperand::Imm(v) => Operand::Imm(BitVec::Bv32(v)),
    }
}

fn address(base: u32, offset: i32) -> Address {
    let off = offset as u32;
    Address {
        base: Reg::w(base),
        offset: if off == 0 {
            None
        } else {
            Some(BitVec::Bv32(off))
        },
    }
}

fn cmp_cond(cmp: Cmp, a: u32, b: u32) -> Condition {
    let (op, lhs, rhs) = match cmp {
        Cmp::Eq => (CmpOp::Eq, a, b),
        Cmp::Ne => (CmpOp::Ne, a, b),
        Cmp::Lt => (CmpOp::Slt, a, b),
        Cmp::Ge => (CmpOp::Sge, a, b),
        Cmp::Ltu => (CmpOp::Lt, a, b),
        Cmp::Geu => (CmpOp::Ge, a, b),
    };
    Condition {
        lhs: Operand::Reg(Reg::w(lhs)),
        op,
        rhs: Operand::Reg(Reg::w(rhs)),
    }
}

fn rel_goto(from: usize, to: usize) -> String {
    let n = to as i64 - from as i64 - 1;
    if n >= 0 {
        format!("+{n:#x}")
    } else {
        format!("-{0:#x}", (-n) as u64)
    }
}
