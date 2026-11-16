#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Src {
    Reg(u8),
    Imm(i32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Width {
    W32,
    W64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AluOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Or,
    And,
    Lsh,
    Rsh,
    Neg,
    Xor,
    Mov,
    Arsh,
    Sdiv,
    Smod,
    Movsx,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cond {
    Ja,
    Jeq,
    Jne,
    Jgt,
    Jge,
    Jlt,
    Jle,
    Jsgt,
    Jsge,
    Jslt,
    Jsle,
    Exit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemSize {
    Byte,
    Half,
    Word,
    Dword,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Insn {
    Alu {
        index: u32,
        width: Width,
        op: AluOp,
        dst: u8,
        src: Src,
        /// MOVSX source width, or 1 when a DIV/MOD is signed.
        extra: u8,
    },
    End {
        index: u32,
        dst: u8,
        bits: u8,
        to_be: bool,
    },
    Jmp {
        index: u32,
        width: Width,
        cond: Cond,
        dst: u8,
        src: Src,
        off: i32,
    },
    Load {
        index: u32,
        size: MemSize,
        signed: bool,
        dst: u8,
        base: u8,
        off: i16,
    },
    Store {
        index: u32,
        size: MemSize,
        base: u8,
        off: i16,
        src: Src,
    },
    Lddw {
        index: u32,
        dst: u8,
        imm: i64,
        pseudo: u8,
    },
    Call {
        index: u32,
        id: i32,
    },
}

impl Insn {
    pub fn index(&self) -> u32 {
        match *self {
            Insn::Alu { index, .. }
            | Insn::End { index, .. }
            | Insn::Jmp { index, .. }
            | Insn::Load { index, .. }
            | Insn::Store { index, .. }
            | Insn::Lddw { index, .. }
            | Insn::Call { index, .. } => index,
        }
    }

    pub fn slots(&self) -> u32 {
        if matches!(self, Insn::Lddw { .. }) { 2 } else { 1 }
    }
}

pub fn decode(bytes: &[u8]) -> Result<Vec<Insn>, String> {
    if bytes.len() % 8 != 0 {
        return Err(format!("bytecode length {} is not a multiple of 8", bytes.len()));
    }
    let mut out = Vec::new();
    let mut slot = 0u32;
    while (slot as usize) * 8 < bytes.len() {
        let at = slot as usize * 8;
        let opcode = bytes[at];
        let regs = bytes[at + 1];
        let dst = regs & 0x0f;
        let src = regs >> 4;
        let off = i16::from_le_bytes([bytes[at + 2], bytes[at + 3]]);
        let imm = i32::from_le_bytes([bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]]);
        check_reg(slot, dst)?;
        check_reg(slot, src)?;
        let class = opcode & 7;
        let code = opcode & 0xf0;
        if code == 0xd0 && (class == 0x04 || class == 0x07) {
            let bits = match imm {
                16 => 16,
                32 => 32,
                64 => 64,
                _ => return Err(format!("slot {slot}: END immediate {imm} is not 16, 32, or 64")),
            };
            if off != 0 {
                return Err(format!("slot {slot}: END offset must be 0"));
            }
            out.push(Insn::End { index: slot, dst, bits, to_be: opcode & 0x08 != 0 });
            slot += 1;
            continue;
        }
        if opcode == 0x18 {
            let next = slot as usize + 1;
            if next * 8 + 8 > bytes.len() {
                return Err(format!("slot {slot}: LDDW is missing its second slot"));
            }
            let hi_at = next * 8;
            if bytes[hi_at] != 0 || bytes[hi_at + 1] != 0 || bytes[hi_at + 2] != 0 || bytes[hi_at + 3] != 0 {
                return Err(format!("slot {slot}: LDDW second slot is not reserved zeros"));
            }
            let hi = i32::from_le_bytes([bytes[hi_at + 4], bytes[hi_at + 5], bytes[hi_at + 6], bytes[hi_at + 7]]);
            let wide = ((hi as u32 as u64) << 32) | (imm as u32 as u64);
            out.push(Insn::Lddw { index: slot, dst, imm: wide as i64, pseudo: src });
            slot += 2;
            continue;
        }
        if class == 0x01 || class == 0x02 || class == 0x03 {
            let size = mem_size(opcode)?;
            let mode = opcode >> 5;
            let signed = mode == 4;
            if mode != 3 && mode != 4 {
                return Err(format!("slot {slot}: memory mode {mode} is not MEM"));
            }
            if class == 0x01 {
                if imm != 0 {
                    return Err(format!("slot {slot}: LDX immediate must be 0"));
                }
                out.push(Insn::Load { index: slot, size, signed, dst, base: src, off });
            } else if class == 0x03 {
                if imm != 0 {
                    return Err(format!("slot {slot}: STX immediate must be 0"));
                }
                out.push(Insn::Store { index: slot, size, base: dst, off, src: Src::Reg(src) });
            } else {
                if src != 0 {
                    return Err(format!("slot {slot}: ST source register must be 0"));
                }
                out.push(Insn::Store { index: slot, size, base: dst, off, src: Src::Imm(imm) });
            }
            slot += 1;
            continue;
        }
        if class == 0x04 || class == 0x07 {
            let width = if class == 0x07 { Width::W64 } else { Width::W32 };
            let reg_src = opcode & 0x08 != 0;
            let src_op = if reg_src { Src::Reg(src) } else { Src::Imm(imm) };
            let (op, extra) = alu_op(slot, code, off, reg_src, width)?;
            if matches!(src_op, Src::Imm(_)) && src != 0 && op != AluOp::Neg {
                return Err(format!("slot {slot}: immediate ALU source register must be 0"));
            }
            out.push(Insn::Alu { index: slot, width, op, dst, src: src_op, extra });
            slot += 1;
            continue;
        }
        if class == 0x05 || class == 0x06 {
            let width = if class == 0x06 { Width::W32 } else { Width::W64 };
            if code == 0x80 {
                if src != 0 {
                    return Err(format!("slot {slot}: call source {src} is not a static helper id"));
                }
                if off != 0 || dst != 0 {
                    return Err(format!("slot {slot}: malformed call"));
                }
                out.push(Insn::Call { index: slot, id: imm });
                slot += 1;
                continue;
            }
            let reg_src = opcode & 0x08 != 0;
            let cond = jump_op(code).ok_or_else(|| format!("slot {slot}: unknown jump opcode {opcode:#x}"))?;
            if cond == Cond::Exit {
                if class != 0x05 || reg_src || off != 0 || src != 0 || dst != 0 {
                    return Err(format!("slot {slot}: malformed exit"));
                }
                out.push(Insn::Jmp { index: slot, width, cond, dst, src: Src::Imm(0), off: 0 });
            } else if cond == Cond::Ja {
                if reg_src || src != 0 || dst != 0 {
                    return Err(format!("slot {slot}: malformed ja"));
                }
                let disp = if class == 0x06 {
                    if off != 0 {
                        return Err(format!("slot {slot}: jmp32 ja offset field must be 0"));
                    }
                    imm
                } else {
                    if imm != 0 {
                        return Err(format!("slot {slot}: ja immediate must be 0"));
                    }
                    off as i32
                };
                out.push(Insn::Jmp { index: slot, width, cond, dst, src: Src::Imm(0), off: disp });
            } else {
                if !reg_src && src != 0 {
                    return Err(format!("slot {slot}: immediate jump source register must be 0"));
                }
                let src_op = if reg_src { Src::Reg(src) } else { Src::Imm(imm) };
                out.push(Insn::Jmp { index: slot, width, cond, dst, src: src_op, off: off as i32 });
            }
            slot += 1;
            continue;
        }
        return Err(format!("slot {slot}: unsupported class in opcode {opcode:#x}"));
    }
    Ok(out)
}

pub fn target_slot(insn: &Insn) -> Option<i64> {
    let Insn::Jmp { index, cond, off, .. } = insn else { return None };
    if *cond == Cond::Exit { None } else { Some(*index as i64 + 1 + *off as i64) }
}

fn check_reg(slot: u32, reg: u8) -> Result<(), String> {
    if reg > 10 {
        Err(format!("slot {slot}: register r{reg} is out of range"))
    } else {
        Ok(())
    }
}

fn mem_size(opcode: u8) -> Result<MemSize, String> {
    match (opcode >> 3) & 3 {
        0 => Ok(MemSize::Word),
        1 => Ok(MemSize::Half),
        2 => Ok(MemSize::Byte),
        3 => Ok(MemSize::Dword),
        _ => Err(format!("opcode {opcode:#x}: bad memory size")),
    }
}

fn alu_op(slot: u32, code: u8, off: i16, reg_src: bool, width: Width) -> Result<(AluOp, u8), String> {
    if code == 0x80 {
        if reg_src {
            return Err(format!("slot {slot}: NEG with a register source is not in the ISA"));
        }
        if off != 0 {
            return Err(format!("slot {slot}: NEG offset must be 0"));
        }
        return Ok((AluOp::Neg, 0));
    }
    if code == 0x30 || code == 0x90 {
        let signed = if off == 1 {
            true
        } else if off == 0 {
            false
        } else {
            return Err(format!("slot {slot}: DIV/MOD offset must be 0 or 1"));
        };
        let op = if code == 0x30 {
            if signed { AluOp::Sdiv } else { AluOp::Div }
        } else if signed {
            AluOp::Smod
        } else {
            AluOp::Mod
        };
        return Ok((op, u8::from(signed)));
    }
    if code == 0xb0 {
        if off == 0 {
            return Ok((AluOp::Mov, 0));
        }
        if !reg_src {
            return Err(format!("slot {slot}: MOVSX requires a register source"));
        }
        if off != 8 && off != 16 && off != 32 {
            return Err(format!("slot {slot}: MOVSX width {off} is not 8, 16, or 32"));
        }
        if off == 32 && width == Width::W32 {
            return Err(format!("slot {slot}: MOVSX from 32 bits requires ALU64"));
        }
        return Ok((AluOp::Movsx, off as u8));
    }
    if off != 0 {
        return Err(format!("slot {slot}: non-zero ALU offset is not a supported instruction"));
    }
    let op = match code {
        0x00 => AluOp::Add,
        0x10 => AluOp::Sub,
        0x20 => AluOp::Mul,
        0x40 => AluOp::Or,
        0x50 => AluOp::And,
        0x60 => AluOp::Lsh,
        0x70 => AluOp::Rsh,
        0xa0 => AluOp::Xor,
        0xc0 => AluOp::Arsh,
        _ => return Err(format!("slot {slot}: unsupported ALU opcode {code:#x}")),
    };
    Ok((op, 0))
}

fn jump_op(code: u8) -> Option<Cond> {
    Some(match code {
        0x00 => Cond::Ja,
        0x10 => Cond::Jeq,
        0x50 => Cond::Jne,
        0x20 => Cond::Jgt,
        0x30 => Cond::Jge,
        0xa0 => Cond::Jlt,
        0xb0 => Cond::Jle,
        0x60 => Cond::Jsgt,
        0x70 => Cond::Jsge,
        0xc0 => Cond::Jslt,
        0xd0 => Cond::Jsle,
        0x90 => Cond::Exit,
        _ => return None,
    })
}
