//! Typed RV32 ops; surface text matches bpftool-style in-place syntax.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Operand {
    Reg(u32),
    Imm(u32),
}
impl Operand {
    pub fn text(self) -> String {
        match self {
            Self::Reg(0) => "0x0".into(),
            Self::Reg(r) => format!("w{r}"),
            Self::Imm(v) => {
                let s = v as i32;
                if s < 0 {
                    signed_hex(s as i64)
                } else {
                    format!("{v:#x}")
                }
            }
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Alu {
    Add,
    Sub,
    And,
    Or,
    Xor,
    Shl,
    Lshr,
    Ashr,
    Slt,
    Sltu,
    Mul,
    Mulh,
    Mulhu,
    Mulhsu,
    Div,
    Divu,
    Rem,
    Remu,
}
impl Alu {
    pub fn eval(self, a: u32, b: u32) -> u32 {
        let (s, t) = (a as i32, b as i32);
        match self {
            Self::Add => a.wrapping_add(b),
            Self::Sub => a.wrapping_sub(b),
            Self::And => a & b,
            Self::Or => a | b,
            Self::Xor => a ^ b,
            Self::Shl => a.wrapping_shl(b & 31),
            Self::Lshr => a >> (b & 31),
            Self::Ashr => (s >> (b & 31)) as u32,
            Self::Slt => (s < t) as u32,
            Self::Sltu => (a < b) as u32,
            Self::Mul => a.wrapping_mul(b),
            Self::Mulh => ((s as i64 * t as i64) >> 32) as u32,
            Self::Mulhu => ((a as u64 * b as u64) >> 32) as u32,
            Self::Mulhsu => ((s as i64 * b as i64) >> 32) as u32,
            Self::Div => {
                if b == 0 {
                    u32::MAX
                } else {
                    s.wrapping_div(t) as u32
                }
            }
            Self::Divu => {
                if b == 0 {
                    u32::MAX
                } else {
                    a / b
                }
            }
            Self::Rem => {
                if b == 0 {
                    a
                } else {
                    s.wrapping_rem(t) as u32
                }
            }
            Self::Remu => {
                if b == 0 {
                    a
                } else {
                    a % b
                }
            }
        }
    }
    fn infix(self) -> Option<&'static str> {
        match self {
            Self::Add => Some("+"),
            Self::Sub => Some("-"),
            Self::And => Some("&"),
            Self::Or => Some("|"),
            Self::Xor => Some("^"),
            Self::Shl => Some("<<"),
            Self::Lshr => Some(">>"),
            Self::Ashr => Some("s>>"),
            Self::Mul => Some("*"),
            Self::Div => Some("s/"),
            Self::Divu => Some("/"),
            Self::Rem => Some("s%"),
            Self::Remu => Some("%"),
            Self::Slt | Self::Sltu | Self::Mulh | Self::Mulhu | Self::Mulhsu => None,
        }
    }
    fn fn_name(self) -> &'static str {
        match self {
            Self::Slt => "slt",
            Self::Sltu => "sltu",
            Self::Mulh => "mulh",
            Self::Mulhu => "mulhu",
            Self::Mulhsu => "mulhsu",
            _ => unreachable!(),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Cmp {
    Eq,
    Ne,
    Lt,
    Ge,
    Ltu,
    Geu,
}
impl Cmp {
    pub fn text(self, a: u32, b: u32) -> String {
        let (a, b) = (Operand::Reg(a).text(), Operand::Reg(b).text());
        match self {
            Self::Eq => format!("{a} == {b}"),
            Self::Ne => format!("{a} != {b}"),
            Self::Lt => format!("{a} s< {b}"),
            Self::Ge => format!("{a} s>= {b}"),
            Self::Ltu => format!("{a} < {b}"),
            Self::Geu => format!("{a} >= {b}"),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    Set {
        rd: u32,
        src: Operand,
    },
    Alu {
        rd: u32,
        kind: Alu,
        a: Operand,
        b: Operand,
    },
    Load {
        rd: u32,
        base: u32,
        offset: i32,
        size: u32,
        signed: bool,
    },
    Store {
        src: u32,
        base: u32,
        offset: i32,
        size: u32,
    },
    Branch {
        cmp: Cmp,
        a: u32,
        b: u32,
        target: usize,
    },
    Assert {
        cmp: Cmp,
        a: u32,
        b: u32,
        taken: bool,
    },
    Jump(usize),
    Call {
        target: u32,
        link: u32,
        next: usize,
    },
    Exit,
    Trap,
}
impl Op {
    pub fn write(&self) -> Option<u32> {
        match *self {
            Self::Set { rd, .. } | Self::Alu { rd, .. } | Self::Load { rd, .. } if rd != 0 => {
                Some(rd)
            }
            _ => None,
        }
    }
    /// Surface text at instruction `index` (needed for relative goto offsets).
    pub fn text(&self, index: usize) -> String {
        match *self {
            Self::Set { rd: 0, .. } | Self::Alu { rd: 0, .. } => "nop".into(),
            Self::Set { rd, src } => format!("w{rd} = {}", src.text()),
            Self::Alu { rd, kind, a, b } => alu_text(rd, kind, a, b),
            Self::Load {
                rd,
                base,
                offset,
                size,
                signed,
            } => {
                let mem = mem_ref(base, offset, size, signed);
                if rd == 0 {
                    format!("discard {mem}")
                } else {
                    format!("w{rd} = {mem}")
                }
            }
            Self::Store {
                src,
                base,
                offset,
                size,
            } => {
                // Stores are always unsigned width in bpftool spelling.
                let mem = mem_ref(base, offset, size, false);
                format!("{mem} = {}", stored(src, size))
            }
            Self::Branch { cmp, a, b, target } => {
                format!("if {} goto {}", cmp.text(a, b), rel_goto(index, target))
            }
            Self::Assert { cmp, a, b, taken } => {
                format!("assert ({}) == {taken}", cmp.text(a, b))
            }
            Self::Jump(t) => format!("goto {}", rel_goto(index, t)),
            Self::Call { target, .. } => format!("call {target:#x}"),
            Self::Exit => "exit".into(),
            Self::Trap => "trap IllegalInstruction".into(),
        }
    }
}

fn alu_text(rd: u32, kind: Alu, a: Operand, b: Operand) -> String {
    if let Some(op) = kind.infix() {
        if matches!(a, Operand::Reg(r) if r == rd) {
            return format!("w{rd} {op}= {}", b.text());
        }
        return format!("w{rd} = {} {op} {}", a.text(), b.text());
    }
    format!("w{rd} = {}({}, {})", kind.fn_name(), a.text(), b.text())
}

fn mem_ref(base: u32, offset: i32, size: u32, signed: bool) -> String {
    let ty = match (size, signed) {
        (1, true) => "s8",
        (1, false) => "u8",
        (2, true) => "s16",
        (2, false) => "u16",
        (4, _) => "u32",
        _ => "u32",
    };
    format!(
        "*({ty} *)({} + {})",
        Operand::Reg(base).text(),
        signed_hex(offset as i64)
    )
}

pub(crate) fn signed_hex(n: i64) -> String {
    if n < 0 {
        format!("-0x{:x}", n.unsigned_abs())
    } else {
        format!("{n:#x}")
    }
}

pub(crate) fn stored(src: u32, size: u32) -> String {
    // Narrow stores still name the source register; width is in the *(uN *) cast.
    let _ = size;
    Operand::Reg(src).text()
}

pub(crate) fn extend(expr: String, size: u32, signed: bool) -> String {
    if size == 4 {
        expr
    } else {
        format!("{}32({expr})", if signed { "sext" } else { "zext" })
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

#[derive(Clone, Debug)]
pub(crate) struct Line {
    pub index: usize,
    pub op: Op,
    pub body: String,
}
impl Line {
    pub fn new(index: usize, op: Op) -> Self {
        let body = op.text(index);
        Self { index, op, body }
    }
    pub fn text(&self) -> String {
        format!("{}: {}", self.index, self.body)
    }
    pub fn annotate(&mut self, s: impl AsRef<str>) {
        self.body.push_str(", ");
        self.body.push_str(s.as_ref());
    }
}
pub(crate) type Path = Vec<Line>;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rv32_arithmetic_corner_cases() {
        assert_eq!(Alu::Div.eval(5, 0), u32::MAX);
        assert_eq!(Alu::Rem.eval(5, 0), 5);
        assert_eq!(Alu::Div.eval(0x80000000, u32::MAX), 0x80000000);
        assert_eq!(Alu::Rem.eval(0x80000000, u32::MAX), 0);
        assert_eq!(Alu::Mulhsu.eval(u32::MAX, u32::MAX), u32::MAX);
        assert_eq!(Alu::Shl.eval(1, 32), 1);
        assert_eq!(Alu::Ashr.eval(0x80000000, 31), u32::MAX);
    }
    #[test]
    fn bpftool_spelling_examples() {
        assert_eq!(
            Op::Alu {
                rd: 2,
                kind: Alu::Add,
                a: Operand::Reg(2),
                b: Operand::Imm((-0x10i32) as u32),
            }
            .text(0),
            "w2 += -0x10"
        );
        assert_eq!(
            Op::Alu {
                rd: 8,
                kind: Alu::Add,
                a: Operand::Reg(2),
                b: Operand::Imm(0x10),
            }
            .text(4),
            "w8 = w2 + 0x10"
        );
        assert_eq!(
            Op::Store {
                src: 1,
                base: 2,
                offset: 0xc,
                size: 4,
            }
            .text(1),
            "*(u32 *)(w2 + 0xc) = w1"
        );
        assert_eq!(
            Op::Load {
                rd: 9,
                base: 10,
                offset: 0,
                size: 4,
                signed: false,
            }
            .text(5),
            "w9 = *(u32 *)(w10 + 0x0)"
        );
        assert_eq!(
            Op::Branch {
                cmp: Cmp::Ltu,
                a: 11,
                b: 12,
                target: 20,
            }
            .text(9),
            "if w11 < w12 goto +0xa"
        );
    }
}
