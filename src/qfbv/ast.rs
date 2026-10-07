//! Typed, quantifier-free fixed-width bit-vector expressions.

use std::error::Error;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstError(pub(crate) String);

impl fmt::Display for AstError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl Error for AstError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BvUnaryOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BvBinaryOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    Lshr,
    Ashr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BvCmpOp {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BvExpr {
    Var {
        name: String,
        width: u32,
    },
    Const {
        value: u64,
        width: u32,
    },
    Unary {
        op: BvUnaryOp,
        value: Box<BvExpr>,
    },
    Binary {
        op: BvBinaryOp,
        left: Box<BvExpr>,
        right: Box<BvExpr>,
        width: u32,
    },
    Ite {
        condition: Box<BoolExpr>,
        then_value: Box<BvExpr>,
        else_value: Box<BvExpr>,
        width: u32,
    },
    Extract {
        value: Box<BvExpr>,
        high: u32,
        low: u32,
    },
    Extend {
        value: Box<BvExpr>,
        by: u32,
        signed: bool,
        width: u32,
    },
    Concat {
        high: Box<BvExpr>,
        low: Box<BvExpr>,
        width: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BoolExpr {
    Const(bool),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Xor(Box<BoolExpr>, Box<BoolExpr>),
    Compare {
        op: BvCmpOp,
        left: Box<BvExpr>,
        right: Box<BvExpr>,
    },
}

fn valid_width(width: u32) -> Result<(), AstError> {
    if matches!(width, 1..=64) {
        Ok(())
    } else {
        Err(AstError(format!(
            "unsupported bit-vector width {width}; expected 1..=64"
        )))
    }
}

fn mask(width: u32) -> u64 {
    if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn valid_symbol(name: &str) -> bool {
    let mut bytes = name.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

impl BvExpr {
    pub fn var(name: impl Into<String>, width: u32) -> Result<Self, AstError> {
        valid_width(width)?;
        let name = name.into();
        if !valid_symbol(&name) {
            return Err(AstError(format!("invalid SMT symbol `{name}`")));
        }
        Ok(Self::Var { name, width })
    }

    pub fn constant(width: u32, value: u64) -> Result<Self, AstError> {
        valid_width(width)?;
        Ok(Self::Const {
            value: value & mask(width),
            width,
        })
    }

    pub fn width(&self) -> u32 {
        match self {
            Self::Var { width, .. }
            | Self::Const { width, .. }
            | Self::Binary { width, .. }
            | Self::Ite { width, .. }
            | Self::Extend { width, .. }
            | Self::Concat { width, .. } => *width,
            Self::Unary { value, .. } => value.width(),
            Self::Extract { high, low, .. } => high - low + 1,
        }
    }

    pub fn unary(op: BvUnaryOp, value: Self) -> Self {
        Self::Unary {
            op,
            value: Box::new(value),
        }
    }

    pub fn binary(op: BvBinaryOp, left: Self, right: Self) -> Result<Self, AstError> {
        if left.width() != right.width() {
            return Err(AstError(format!(
                "bit-vector width mismatch: {} versus {}",
                left.width(),
                right.width()
            )));
        }
        let width = left.width();
        Ok(Self::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
            width,
        })
    }

    pub fn ite(condition: BoolExpr, then_value: Self, else_value: Self) -> Result<Self, AstError> {
        if then_value.width() != else_value.width() {
            return Err(AstError(format!(
                "ite branch width mismatch: {} versus {}",
                then_value.width(),
                else_value.width()
            )));
        }
        let width = then_value.width();
        Ok(Self::Ite {
            condition: Box::new(condition),
            then_value: Box::new(then_value),
            else_value: Box::new(else_value),
            width,
        })
    }

    pub fn extract(self, high: u32, low: u32) -> Result<Self, AstError> {
        if low > high || high >= self.width() {
            return Err(AstError(format!(
                "invalid extract [{high}:{low}] from BV{}",
                self.width()
            )));
        }
        if low == 0 && high + 1 == self.width() {
            return Ok(self);
        }
        Ok(Self::Extract {
            value: Box::new(self),
            high,
            low,
        })
    }

    pub fn zero_extend(self, width: u32) -> Result<Self, AstError> {
        self.extend(width, false)
    }

    pub fn sign_extend(self, width: u32) -> Result<Self, AstError> {
        self.extend(width, true)
    }

    pub fn concat(high: Self, low: Self) -> Result<Self, AstError> {
        let width = high
            .width()
            .checked_add(low.width())
            .ok_or_else(|| AstError(String::from("concatenation width overflow")))?;
        valid_width(width)?;
        Ok(Self::Concat {
            high: Box::new(high),
            low: Box::new(low),
            width,
        })
    }

    fn extend(self, width: u32, signed: bool) -> Result<Self, AstError> {
        valid_width(width)?;
        if width < self.width() {
            return Err(AstError(format!(
                "cannot extend BV{} to BV{width}",
                self.width()
            )));
        }
        if width == self.width() {
            return Ok(self);
        }
        Ok(Self::Extend {
            by: width - self.width(),
            value: Box::new(self),
            signed,
            width,
        })
    }
}

impl BoolExpr {
    pub fn compare(op: BvCmpOp, left: BvExpr, right: BvExpr) -> Result<Self, AstError> {
        if left.width() != right.width() {
            return Err(AstError(format!(
                "comparison width mismatch: {} versus {}",
                left.width(),
                right.width()
            )));
        }
        Ok(Self::Compare {
            op,
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    pub fn logical_not(value: Self) -> Self {
        match value {
            Self::Const(value) => Self::Const(!value),
            Self::Not(value) => *value,
            value => Self::Not(Box::new(value)),
        }
    }

    pub fn and(values: impl IntoIterator<Item = Self>) -> Self {
        let mut out = Vec::new();
        for value in values {
            match value {
                Self::Const(false) => return Self::Const(false),
                Self::Const(true) => {}
                Self::And(values) => out.extend(values),
                value => out.push(value),
            }
        }
        match out.len() {
            0 => Self::Const(true),
            1 => out.pop().unwrap(),
            _ => Self::And(out),
        }
    }

    pub fn or(values: impl IntoIterator<Item = Self>) -> Self {
        let mut out = Vec::new();
        for value in values {
            match value {
                Self::Const(true) => return Self::Const(true),
                Self::Const(false) => {}
                Self::Or(values) => out.extend(values),
                value => out.push(value),
            }
        }
        match out.len() {
            0 => Self::Const(false),
            1 => out.pop().unwrap(),
            _ => Self::Or(out),
        }
    }

    pub fn xor(left: Self, right: Self) -> Self {
        match (left, right) {
            (Self::Const(false), value) | (value, Self::Const(false)) => value,
            (Self::Const(true), value) | (value, Self::Const(true)) => Self::logical_not(value),
            (left, right) => Self::Xor(Box::new(left), Box::new(right)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructors_reject_ill_typed_terms() {
        let x = BvExpr::var("x", 32).unwrap();
        let y = BvExpr::var("y", 64).unwrap();
        assert!(BvExpr::binary(BvBinaryOp::Add, x.clone(), y.clone()).is_err());
        assert!(BoolExpr::compare(BvCmpOp::Eq, x, y).is_err());
        assert!(BvExpr::var("bad-name", 32).is_err());
        assert!(BvExpr::constant(0, 0).is_err());
    }

    #[test]
    fn constants_are_masked_to_their_width() {
        assert_eq!(
            BvExpr::constant(8, 0x1ff).unwrap(),
            BvExpr::Const {
                value: 0xff,
                width: 8
            }
        );
    }
}
