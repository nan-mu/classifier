//! BPF asm / raw words → annotated [`Insn`] sequence.

use anyhow::{bail, Context, Result};
use regex::Regex;
use std::sync::LazyLock;

use crate::predicate::{
    Address, AluOp, BitVec, CmpOp, Condition, Insn, Machine, MemWidth, Operand, Origin, Predicate,
    PredicateId, Prefix, Reg,
};

static SPLIT: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?x)^(?P<index>[0-9]+):\s+(?P<body>.+)$").unwrap()
});

/// Annotate from bpftool-style `index: body` lines (fixture / debug helper).
///
/// Prefer [`super::prefixgen_bpf_object`] for real machine codes from `bpf.o`.
pub fn prefixgen_bpf_asm(lines: &[String]) -> Result<Vec<Insn>> {
    let mut id = 0u64;
    let mut out = Vec::new();
    let mut pending_cont: Option<u32> = None;

    for line in lines {
        let caps = SPLIT
            .captures(line)
            .with_context(|| format!("prefixgen_bpf: bad line `{line}`"))?;
        let index: u32 = caps["index"].parse()?;
        let body = caps["body"].trim();

        if let Some(expected) = pending_cont {
            if index != expected {
                // Insert empty continuation for missing slot (bpftool omits it).
                out.push(Insn {
                    index: expected,
                    machine: Machine::Bpf(0),
                    prefix: Prefix::new(),
                });
            }
            pending_cont = None;
        }

        let (pred, is_ll) = parse_bpf_body(body)?;
        let mut prefix = Prefix::new();
        if let Some(p) = pred {
            prefix.push(PredicateId(id), p, Origin::stage("prefixgen"));
            id += 1;
        }
        out.push(Insn {
            index,
            machine: Machine::Bpf(0),
            prefix,
        });
        if is_ll {
            pending_cont = Some(index + 1);
        }
    }
    if let Some(expected) = pending_cont {
        out.push(Insn {
            index: expected,
            machine: Machine::Bpf(0),
            prefix: Prefix::new(),
        });
    }
    Ok(out)
}

fn parse_bpf_body(body: &str) -> Result<(Option<Predicate>, bool)> {
    let body = body.trim();
    if body == "exit" {
        return Ok((Some(Predicate::Exit), false));
    }
    if let Some(rest) = body.strip_prefix("call ") {
        return Ok((
            Some(Predicate::Call {
                target: rest.trim().to_string(),
            }),
            false,
        ));
    }
    if let Some(rest) = body.strip_prefix("goto ") {
        let offset = strip_label(rest.trim());
        return Ok((Some(Predicate::Goto { offset }), false));
    }
    if let Some(rest) = body.strip_prefix("if ") {
        return Ok((Some(parse_if_goto(rest)?), false));
    }
    if let Some((lhs, rhs)) = body.split_once(" = ") {
        let lhs = lhs.trim();
        let rhs = rhs.trim();
        if lhs.starts_with("*(") {
            let (width, addr) = parse_mem_lhs(lhs)?;
            return Ok((
                Some(Predicate::Store {
                    width,
                    addr,
                    src: parse_operand(rhs)?,
                }),
                false,
            ));
        }
        if rhs.ends_with(" ll") {
            let imm = rhs.trim_end_matches(" ll").trim();
            let v = parse_imm64(imm)?;
            return Ok((
                Some(Predicate::Set {
                    dst: parse_reg(lhs)?,
                    src: Operand::Imm(BitVec::Bv64(v)),
                }),
                true,
            ));
        }
        if let Some(mem) = parse_mem_rhs(rhs)? {
            return Ok((
                Some(Predicate::Load {
                    dst: parse_reg(lhs)?,
                    width: mem.0,
                    addr: mem.1,
                }),
                false,
            ));
        }
        if let Some(pred) = parse_alu_or_set(lhs, rhs)? {
            return Ok((Some(pred), false));
        }
    }
    // In-place ALU: `w0 += 0x1`
    if let Some(pred) = parse_inplace_alu(body)? {
        return Ok((Some(pred), false));
    }
    bail!("prefixgen_bpf: unsupported body `{body}`")
}

fn parse_if_goto(rest: &str) -> Result<Predicate> {
    let rest = rest.trim();
    let Some((cond, goto)) = rest.split_once(" goto ") else {
        bail!("bad if: {rest}");
    };
    let offset = strip_label(goto.trim());
    Ok(Predicate::IfGoto {
        condition: parse_condition(cond.trim())?,
        offset,
    })
}

fn parse_condition(s: &str) -> Result<Condition> {
    for (tok, op) in [
        (" == ", CmpOp::Eq),
        (" != ", CmpOp::Ne),
        (" s<= ", CmpOp::Sle),
        (" s>= ", CmpOp::Sge),
        (" s< ", CmpOp::Slt),
        (" s> ", CmpOp::Sgt),
        (" <= ", CmpOp::Le),
        (" >= ", CmpOp::Ge),
        (" < ", CmpOp::Lt),
        (" > ", CmpOp::Gt),
    ] {
        if let Some((l, r)) = s.split_once(tok) {
            return Ok(Condition {
                lhs: parse_operand(l.trim())?,
                op,
                rhs: parse_operand(r.trim())?,
            });
        }
    }
    bail!("bad condition `{s}`")
}

fn parse_alu_or_set(dst: &str, rhs: &str) -> Result<Option<Predicate>> {
    let dst = parse_reg(dst)?;
    for (tok, op) in [
        (" + ", AluOp::Add),
        (" - ", AluOp::Sub),
        (" * ", AluOp::Mul),
        (" & ", AluOp::And),
        (" | ", AluOp::Or),
        (" ^ ", AluOp::Xor),
        (" << ", AluOp::Shl),
        (" s>> ", AluOp::Ashr),
        (" >> ", AluOp::Lshr),
    ] {
        if let Some((l, r)) = rhs.split_once(tok) {
            return Ok(Some(Predicate::Alu {
                dst: dst.clone(),
                op,
                lhs: parse_operand_for(&dst, l.trim())?,
                rhs: parse_operand_for(&dst, r.trim())?,
            }));
        }
    }
    Ok(Some(Predicate::Set {
        dst: dst.clone(),
        src: parse_operand_for(&dst, rhs)?,
    }))
}

fn parse_inplace_alu(body: &str) -> Result<Option<Predicate>> {
    for (tok, op) in [
        (" += ", AluOp::Add),
        (" -= ", AluOp::Sub),
        (" *= ", AluOp::Mul),
        (" &= ", AluOp::And),
        (" |= ", AluOp::Or),
        (" ^= ", AluOp::Xor),
        (" <<= ", AluOp::Shl),
        (" s>>= ", AluOp::Ashr),
        (" >>= ", AluOp::Lshr),
    ] {
        if let Some((dst, rhs)) = body.split_once(tok) {
            let dst = parse_reg(dst.trim())?;
            return Ok(Some(Predicate::AluAssign {
                dst: dst.clone(),
                op,
                rhs: parse_operand_for(&dst, rhs.trim())?,
            }));
        }
    }
    Ok(None)
}

fn parse_mem_rhs(rhs: &str) -> Result<Option<(MemWidth, Address)>> {
    if !rhs.starts_with("*(") {
        return Ok(None);
    }
    Ok(Some(parse_mem_lhs(rhs)?))
}

fn parse_mem_lhs(s: &str) -> Result<(MemWidth, Address)> {
    // *(u32 *)(r1 + 0x4) or *(u32 *)(r1)
    let s = s.trim();
    let Some(rest) = s.strip_prefix("*(") else {
        bail!("bad mem `{s}`");
    };
    let Some((ty, rest)) = rest.split_once(" *)(") else {
        bail!("bad mem `{s}`");
    };
    let rest = rest.strip_suffix(')').unwrap_or(rest);
    let width = match ty {
        "u8" => MemWidth::U8,
        "u16" => MemWidth::U16,
        "u32" => MemWidth::U32,
        "u64" => MemWidth::U64,
        "s8" => MemWidth::S8,
        "s16" => MemWidth::S16,
        "s32" => MemWidth::S32,
        _ => bail!("bad mem type `{ty}`"),
    };
    let addr = if let Some((base, off)) = rest.split_once(" + ") {
        let base_reg = parse_reg(base.trim())?;
        let bv = imm_for_reg(&base_reg, off.trim())?;
        Address {
            base: base_reg,
            offset: if is_zero_bv(bv) {
                None
            } else {
                Some(bv)
            },
        }
    } else if let Some((base, off)) = rest.split_once(" - ") {
        let base_reg = parse_reg(base.trim())?;
        let mag = parse_imm_u64(off.trim())?;
        let neg = match base_reg.name.as_bytes().first() {
            Some(b'r') => BitVec::Bv64((-(mag as i64)) as u64),
            _ => BitVec::Bv32((-(mag as i32)) as u32),
        };
        Address {
            base: base_reg,
            offset: Some(neg),
        }
    } else {
        Address {
            base: parse_reg(rest.trim())?,
            offset: None,
        }
    };
    Ok((width, addr))
}

fn parse_reg(s: &str) -> Result<Reg> {
    let s = s.trim();
    if let Some(n) = s.strip_prefix('w') {
        return Ok(Reg::w(n.parse()?));
    }
    if let Some(n) = s.strip_prefix('r') {
        return Ok(Reg::r(n.parse()?));
    }
    bail!("bad reg `{s}`")
}

fn parse_operand(s: &str) -> Result<Operand> {
    parse_operand_for(&Reg::w(0), s)
}

fn parse_operand_for(hint: &Reg, s: &str) -> Result<Operand> {
    let s = s.trim();
    if s.starts_with('w') || s.starts_with('r') {
        return Ok(Operand::Reg(parse_reg(s)?));
    }
    Ok(Operand::Imm(imm_for_reg(hint, s)?))
}

fn imm_for_reg(reg: &Reg, s: &str) -> Result<BitVec> {
    let v = parse_imm_i64(s)?;
    if reg.name.starts_with('r') {
        Ok(BitVec::Bv64(v as u64))
    } else {
        Ok(BitVec::Bv32(v as u32))
    }
}

fn is_zero_bv(bv: BitVec) -> bool {
    matches!(
        bv,
        BitVec::Bv8(0) | BitVec::Bv16(0) | BitVec::Bv32(0) | BitVec::Bv64(0)
    )
}

fn parse_imm64(s: &str) -> Result<u64> {
    Ok(parse_imm_i64(s)? as u64)
}

fn parse_imm_u64(s: &str) -> Result<u64> {
    let s = s.trim();
    if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        return Ok(u64::from_str_radix(h, 16)?);
    }
    if let Some(h) = s.strip_prefix("-0x").or_else(|| s.strip_prefix("-0X")) {
        let mag = u64::from_str_radix(h, 16)?;
        return Ok((-(mag as i64)) as u64);
    }
    Ok(s.parse::<i64>()? as u64)
}

fn parse_imm_i64(s: &str) -> Result<i64> {
    let s = s.trim();
    if let Some(h) = s.strip_prefix("-0x").or_else(|| s.strip_prefix("-0X")) {
        let mag = i64::from_str_radix(h, 16)?;
        return Ok(-mag);
    }
    if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        return Ok(u64::from_str_radix(h, 16)? as i64);
    }
    Ok(s.parse()?)
}

fn strip_label(s: &str) -> String {
    match s.split_once(" <") {
        Some((off, _)) => off.trim().to_string(),
        None => s.to_string(),
    }
}
