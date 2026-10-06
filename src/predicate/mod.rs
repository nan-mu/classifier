//! Structured predicate IR and BPF-assembly-style canonical printing.
//!
//! Strings are the surface form only; stages must not re-parse free text for semantics.

pub mod print;

use std::fmt;

/// Fixed-width bit-vector immediate (semantic value, not an identifier).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BitVec {
    Bv8(u8),
    Bv16(u16),
    Bv32(u32),
    Bv64(u64),
}

impl BitVec {
    pub fn width_bits(self) -> u32 {
        match self {
            Self::Bv8(_) => 8,
            Self::Bv16(_) => 16,
            Self::Bv32(_) => 32,
            Self::Bv64(_) => 64,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MemWidth {
    U8,
    U16,
    U32,
    U64,
    S8,
    S16,
    S32,
}

impl MemWidth {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::S8 => "s8",
            Self::S16 => "s16",
            Self::S32 => "s32",
        }
    }

    pub fn from_size_signed(size: u32, signed: bool) -> Option<Self> {
        match (size, signed) {
            (1, true) => Some(Self::S8),
            (1, false) => Some(Self::U8),
            (2, true) => Some(Self::S16),
            (2, false) => Some(Self::U16),
            (4, true) => Some(Self::S32),
            (4, false) => Some(Self::U32),
            (8, false) => Some(Self::U64),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AluOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    Lshr,
    Ashr,
    Div,
    Divu,
    Rem,
    Remu,
    Slt,
    Sltu,
    Mulh,
    Mulhu,
    Mulhsu,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

impl CmpOp {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Slt => "s<",
            Self::Sle => "s<=",
            Self::Sgt => "s>",
            Self::Sge => "s>=",
        }
    }
}

/// Register name in surface syntax (`wN` or `rN`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Reg {
    pub name: String,
}

impl Reg {
    pub fn w(n: u32) -> Self {
        Self {
            name: format!("w{n}"),
        }
    }

    pub fn r(n: u32) -> Self {
        Self {
            name: format!("r{n}"),
        }
    }
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    Reg(Reg),
    Imm(BitVec),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Address {
    pub base: Reg,
    /// Address-width bit-vector; `None` means zero offset (omitted in print).
    pub offset: Option<BitVec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Condition {
    pub lhs: Operand,
    pub op: CmpOp,
    pub rhs: Operand,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Predicate {
    Set {
        dst: Reg,
        src: Operand,
    },
    AluAssign {
        dst: Reg,
        op: AluOp,
        rhs: Operand,
    },
    Alu {
        dst: Reg,
        op: AluOp,
        lhs: Operand,
        rhs: Operand,
    },
    /// Non-infix ALU shown as `dst = name(lhs, rhs)` (slt/mulh/…).
    AluCall {
        dst: Reg,
        name: &'static str,
        lhs: Operand,
        rhs: Operand,
    },
    Load {
        dst: Reg,
        width: MemWidth,
        addr: Address,
    },
    Store {
        width: MemWidth,
        addr: Address,
        src: Operand,
    },
    Assert {
        condition: Condition,
        expected: bool,
    },
    /// Base control condition (not yet path-asserted).
    IfGoto {
        condition: Condition,
        /// Relative bpftool-style offset text, e.g. `+0x33` or `-0x2b`.
        offset: String,
    },
    Goto {
        offset: String,
    },
    Call {
        target: String,
    },
    Exit,
    Trap {
        reason: String,
    },
    /// Opaque continuation / empty semantic slot.
    Empty,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PredicateId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    pub note: String,
}

impl Origin {
    pub fn stage(name: &str) -> Self {
        Self {
            note: name.to_string(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateNode {
    pub id: PredicateId,
    pub predicate: Predicate,
    pub origin: Origin,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Prefix(pub Vec<PredicateNode>);

impl Prefix {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push(&mut self, id: PredicateId, predicate: Predicate, origin: Origin) {
        self.0.push(PredicateNode {
            id,
            predicate,
            origin,
        });
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty() || self.0.iter().all(|n| matches!(n.predicate, Predicate::Empty))
    }
}

/// Raw machine encoding for one program slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Machine {
    /// BPF 64-bit slot.
    Bpf(u64),
    /// RV32 32-bit instruction word.
    Rv32(u32),
    /// RV32 compressed 16-bit instruction.
    Rv16(u16),
}

impl Machine {
    /// Fixed-width hex field for emit: BPF 16 digits; RV32 8 digits (C padded with spaces).
    /// RV bytes are little-endian memory order (first byte leftmost).
    pub fn emit_hex_field(&self) -> String {
        match *self {
            Self::Bpf(w) => {
                let b = w.to_le_bytes();
                format!(
                    "{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
                    b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]
                )
            }
            Self::Rv32(w) => format!(
                "{:02x}{:02x}{:02x}{:02x}",
                w as u8,
                (w >> 8) as u8,
                (w >> 16) as u8,
                (w >> 24) as u8
            ),
            Self::Rv16(w) => format!("{:02x}{:02x}    ", w as u8, (w >> 8) as u8),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Insn {
    pub index: u32,
    pub machine: Machine,
    pub prefix: Prefix,
}

impl Insn {
    /// Emit one acceptance line; `index_width` right-aligns the index column.
    pub fn emit_line(&self, index_width: usize) -> String {
        let prefix = print::print_prefix(&self.prefix);
        format!(
            "{:>width$}: {}, {}",
            self.index,
            self.machine.emit_hex_field(),
            prefix,
            width = index_width
        )
    }
}

/// Decimal width needed to right-align every index in `insns`.
pub fn index_column_width(insns: &[Insn]) -> usize {
    insns
        .iter()
        .map(|i| i.index)
        .max()
        .unwrap_or(0)
        .to_string()
        .len()
        .max(1)
}
