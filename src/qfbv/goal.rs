//! Symbolic evaluation from structured Path predicates to QF_BV obligations.

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

use crate::pathgen::Path;
use crate::predicate::{AluOp, BitVec, CmpOp, Machine, Operand, Predicate, PredicateId, Reg};

use super::ast::{AstError, BoolExpr, BvBinaryOp, BvCmpOp, BvExpr};
use super::smtlib::QfbvQuery;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GoalError {
    Ast(AstError),
    Invalid {
        path_code: String,
        reason: String,
    },
    Unsupported {
        path_code: String,
        insn_index: u32,
        predicate_id: PredicateId,
        reason: String,
    },
}

impl fmt::Display for GoalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ast(error) => write!(f, "QF_BV AST: {error}"),
            Self::Invalid { path_code, reason } => {
                write!(f, "path {path_code}: {reason}")
            }
            Self::Unsupported {
                path_code,
                insn_index,
                predicate_id,
                reason,
            } => write!(
                f,
                "path {path_code}, instruction {insn_index}, predicate {}: unsupported: {reason}",
                predicate_id.0
            ),
        }
    }
}

impl Error for GoalError {}

impl From<AstError> for GoalError {
    fn from(value: AstError) -> Self {
        Self::Ast(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathFormula {
    pub path_code: String,
    pub assertion: BoolExpr,
    pub(crate) entry_registers: BTreeMap<String, BvExpr>,
    pub(crate) assertion_sources: Vec<(u32, PredicateId)>,
    pub(crate) input_origins: BTreeMap<String, String>,
    pub(crate) observations: Vec<(String, BvExpr)>,
}

impl PathFormula {
    /// Return the canonical entry register variable (`rN` for BPF, `wN` for
    /// RV32) if that register was read before its first definition.
    pub fn entry_register(&self, name: &str) -> Option<&BvExpr> {
        self.entry_registers.get(name)
    }

    pub fn entry_registers(&self) -> &BTreeMap<String, BvExpr> {
        &self.entry_registers
    }

    pub fn assertion_sources(&self) -> &[(u32, PredicateId)] {
        &self.assertion_sources
    }

    pub fn input_origins(&self) -> &BTreeMap<String, String> {
        &self.input_origins
    }

    pub fn observations(&self) -> &[(String, BvExpr)] {
        &self.observations
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Arch {
    Bpf,
    Rv32,
}

struct SymbolicState<'a> {
    arch: Arch,
    namespace: &'a str,
    registers: BTreeMap<u32, BvExpr>,
    entry_registers: BTreeMap<String, BvExpr>,
    assertions: Vec<BoolExpr>,
    assertion_sources: Vec<(u32, PredicateId)>,
}

impl<'a> SymbolicState<'a> {
    fn new(arch: Arch, namespace: &'a str) -> Result<Self, AstError> {
        // Validate even when the path happens not to read an entry register.
        let _ = BvExpr::var(format!("{namespace}_probe"), 1)?;
        Ok(Self {
            arch,
            namespace,
            registers: BTreeMap::new(),
            entry_registers: BTreeMap::new(),
            assertions: Vec::new(),
            assertion_sources: Vec::new(),
        })
    }

    fn read_register(&mut self, register: &Reg) -> Result<BvExpr, GoalError> {
        let (kind, number) = parse_register(register)?;
        match self.arch {
            Arch::Bpf => {
                if !matches!(kind, 'w' | 'r') {
                    return Err(invalid_register(register, "BPF register must be wN or rN"));
                }
                let full = match self.registers.get(&number) {
                    Some(value) => value.clone(),
                    None => {
                        let name = format!("{}_entry_r{number}", self.namespace);
                        let value = BvExpr::var(name, 64)?;
                        self.registers.insert(number, value.clone());
                        self.entry_registers
                            .insert(format!("r{number}"), value.clone());
                        value
                    }
                };
                if kind == 'w' {
                    Ok(full.extract(31, 0)?)
                } else {
                    Ok(full)
                }
            }
            Arch::Rv32 => {
                if kind != 'w' {
                    return Err(invalid_register(register, "RV32 register must be wN"));
                }
                if number == 0 {
                    return Ok(BvExpr::constant(32, 0)?);
                }
                match self.registers.get(&number) {
                    Some(value) => Ok(value.clone()),
                    None => {
                        let name = format!("{}_entry_w{number}", self.namespace);
                        let value = BvExpr::var(name, 32)?;
                        self.registers.insert(number, value.clone());
                        self.entry_registers
                            .insert(format!("w{number}"), value.clone());
                        Ok(value)
                    }
                }
            }
        }
    }

    fn write_register(&mut self, register: &Reg, value: BvExpr) -> Result<(), GoalError> {
        let (kind, number) = parse_register(register)?;
        match self.arch {
            Arch::Bpf => match kind {
                'w' => {
                    let value = coerce(value, 32)?.zero_extend(64)?;
                    self.registers.insert(number, value);
                    Ok(())
                }
                'r' => {
                    self.registers.insert(number, coerce(value, 64)?);
                    Ok(())
                }
                _ => Err(invalid_register(register, "BPF register must be wN or rN")),
            },
            Arch::Rv32 => {
                if kind != 'w' {
                    return Err(invalid_register(register, "RV32 register must be wN"));
                }
                if number != 0 {
                    self.registers.insert(number, coerce(value, 32)?);
                }
                Ok(())
            }
        }
    }

    fn operand(&mut self, operand: &Operand) -> Result<BvExpr, GoalError> {
        match operand {
            Operand::Reg(register) => self.read_register(register),
            Operand::Imm(value) => bitvec(*value).map_err(Into::into),
        }
    }

    fn condition(
        &mut self,
        condition: &crate::predicate::Condition,
    ) -> Result<BoolExpr, GoalError> {
        let left = self.operand(&condition.lhs)?;
        let right = self.operand(&condition.rhs)?;
        let operation = match condition.op {
            CmpOp::Eq => BvCmpOp::Eq,
            CmpOp::Ne => BvCmpOp::Ne,
            CmpOp::Lt => BvCmpOp::Ult,
            CmpOp::Le => BvCmpOp::Ule,
            CmpOp::Gt => BvCmpOp::Ugt,
            CmpOp::Ge => BvCmpOp::Uge,
            CmpOp::Slt => BvCmpOp::Slt,
            CmpOp::Sle => BvCmpOp::Sle,
            CmpOp::Sgt => BvCmpOp::Sgt,
            CmpOp::Sge => BvCmpOp::Sge,
        };
        BoolExpr::compare(operation, left, right).map_err(Into::into)
    }
}

fn invalid_register(register: &Reg, reason: &str) -> GoalError {
    GoalError::Invalid {
        path_code: String::from("<register>"),
        reason: format!("{reason}: `{register}`"),
    }
}

fn parse_register(register: &Reg) -> Result<(char, u32), GoalError> {
    let mut chars = register.name.chars();
    let kind = chars
        .next()
        .ok_or_else(|| invalid_register(register, "empty register"))?;
    let number = chars
        .as_str()
        .parse::<u32>()
        .map_err(|_| invalid_register(register, "malformed register"))?;
    Ok((kind, number))
}

pub(super) fn bitvec(value: BitVec) -> Result<BvExpr, AstError> {
    match value {
        BitVec::Bv8(value) => BvExpr::constant(8, value.into()),
        BitVec::Bv16(value) => BvExpr::constant(16, value.into()),
        BitVec::Bv32(value) => BvExpr::constant(32, value.into()),
        BitVec::Bv64(value) => BvExpr::constant(64, value),
    }
}

pub(super) fn coerce(value: BvExpr, width: u32) -> Result<BvExpr, AstError> {
    match value.width().cmp(&width) {
        std::cmp::Ordering::Less => value.zero_extend(width),
        std::cmp::Ordering::Equal => Ok(value),
        std::cmp::Ordering::Greater => value.extract(width - 1, 0),
    }
}

fn shift_amount(value: BvExpr, width: u32) -> Result<BvExpr, AstError> {
    BvExpr::binary(
        BvBinaryOp::And,
        coerce(value, width)?,
        BvExpr::constant(width, (width - 1).into())?,
    )
}

fn bool_as_bv(value: BoolExpr, width: u32) -> Result<BvExpr, AstError> {
    BvExpr::ite(
        value,
        BvExpr::constant(width, 1)?,
        BvExpr::constant(width, 0)?,
    )
}

fn high_multiply(
    left: BvExpr,
    right: BvExpr,
    left_signed: bool,
    right_signed: bool,
) -> Result<BvExpr, AstError> {
    if left.width() != right.width() || left.width() > 32 {
        return Err(AstError(format!(
            "high multiply requires equal widths no greater than 32, found BV{} and BV{}",
            left.width(),
            right.width()
        )));
    }
    let width = left.width();
    let wide = width * 2;
    let left = if left_signed {
        left.sign_extend(wide)?
    } else {
        left.zero_extend(wide)?
    };
    let right = if right_signed {
        right.sign_extend(wide)?
    } else {
        right.zero_extend(wide)?
    };
    BvExpr::binary(BvBinaryOp::Mul, left, right)?.extract(wide - 1, width)
}

pub(super) fn apply_alu(operation: AluOp, left: BvExpr, right: BvExpr) -> Result<BvExpr, AstError> {
    let width = left.width();
    let right = coerce(right, width)?;
    match operation {
        AluOp::Add => BvExpr::binary(BvBinaryOp::Add, left, right),
        AluOp::Sub => BvExpr::binary(BvBinaryOp::Sub, left, right),
        AluOp::Mul => BvExpr::binary(BvBinaryOp::Mul, left, right),
        AluOp::And => BvExpr::binary(BvBinaryOp::And, left, right),
        AluOp::Or => BvExpr::binary(BvBinaryOp::Or, left, right),
        AluOp::Xor => BvExpr::binary(BvBinaryOp::Xor, left, right),
        AluOp::Shl => {
            let amount = shift_amount(right, width)?;
            BvExpr::binary(BvBinaryOp::Shl, left, amount)
        }
        AluOp::Lshr => {
            let amount = shift_amount(right, width)?;
            BvExpr::binary(BvBinaryOp::Lshr, left, amount)
        }
        AluOp::Ashr => {
            let amount = shift_amount(right, width)?;
            BvExpr::binary(BvBinaryOp::Ashr, left, amount)
        }
        AluOp::Slt => bool_as_bv(BoolExpr::compare(BvCmpOp::Slt, left, right)?, width),
        AluOp::Sltu => bool_as_bv(BoolExpr::compare(BvCmpOp::Ult, left, right)?, width),
        AluOp::Mulh => high_multiply(left, right, true, true),
        AluOp::Mulhu => high_multiply(left, right, false, false),
        AluOp::Mulhsu => high_multiply(left, right, true, false),
        AluOp::Div | AluOp::Divu | AluOp::Rem | AluOp::Remu => Err(AstError(format!(
            "{operation:?} requires ISA-specific zero/overflow semantics"
        ))),
    }
}

fn infer_arch(path: &Path) -> Result<Arch, GoalError> {
    let mut arch = None;
    for instruction in &path.insns {
        let current = match instruction.machine {
            Machine::Bpf(_) => Arch::Bpf,
            Machine::Rv32(_) | Machine::Rv16(_) => Arch::Rv32,
        };
        if let Some(previous) = arch
            && previous != current
        {
            return Err(GoalError::Invalid {
                path_code: path.code.clone(),
                reason: String::from("mixed BPF and RV32 machine words"),
            });
        }
        arch = Some(current);
    }
    arch.ok_or_else(|| GoalError::Invalid {
        path_code: path.code.clone(),
        reason: String::from("empty path"),
    })
}

fn unsupported(path: &Path, index: u32, id: PredicateId, reason: impl Into<String>) -> GoalError {
    GoalError::Unsupported {
        path_code: path.code.clone(),
        insn_index: index,
        predicate_id: id,
        reason: reason.into(),
    }
}

/// Compile the conjunction of every `Assert` on one structured path.
///
/// Non-assert register predicates update symbolic state. Effectful operations
/// that do not yet have a contract are rejected with provenance; they are
/// never replaced by unconstrained values or silently skipped.
pub fn compile_path_asserts(path: &Path, namespace: &str) -> Result<PathFormula, GoalError> {
    let arch = infer_arch(path)?;
    let mut state = SymbolicState::new(arch, namespace)?;

    for instruction in &path.insns {
        for node in &instruction.prefix.0 {
            match &node.predicate {
                Predicate::Set { dst, src } => {
                    let value = state.operand(src)?;
                    state.write_register(dst, value)?;
                }
                Predicate::AluAssign { dst, op, rhs } => {
                    if matches!(op, AluOp::Div | AluOp::Divu | AluOp::Rem | AluOp::Remu) {
                        return Err(unsupported(
                            path,
                            instruction.index,
                            node.id,
                            format!("{op:?} zero/overflow behavior is not modeled"),
                        ));
                    }
                    let left = state.read_register(dst)?;
                    let right = state.operand(rhs)?;
                    let value = apply_alu(*op, left, right)?;
                    state.write_register(dst, value)?;
                }
                Predicate::Alu { dst, op, lhs, rhs } => {
                    if matches!(op, AluOp::Div | AluOp::Divu | AluOp::Rem | AluOp::Remu) {
                        return Err(unsupported(
                            path,
                            instruction.index,
                            node.id,
                            format!("{op:?} zero/overflow behavior is not modeled"),
                        ));
                    }
                    let left = state.operand(lhs)?;
                    let right = state.operand(rhs)?;
                    let value = apply_alu(*op, left, right)?;
                    state.write_register(dst, value)?;
                }
                Predicate::AluCall {
                    dst,
                    name,
                    lhs,
                    rhs,
                } => {
                    let operation = match *name {
                        "slt" => AluOp::Slt,
                        "sltu" => AluOp::Sltu,
                        "mulh" => AluOp::Mulh,
                        "mulhu" => AluOp::Mulhu,
                        "mulhsu" => AluOp::Mulhsu,
                        other => {
                            return Err(unsupported(
                                path,
                                instruction.index,
                                node.id,
                                format!("unknown ALU call `{other}`"),
                            ));
                        }
                    };
                    let left = state.operand(lhs)?;
                    let right = state.operand(rhs)?;
                    let value = apply_alu(operation, left, right)?;
                    state.write_register(dst, value)?;
                }
                Predicate::Assert {
                    condition,
                    expected,
                } => {
                    let condition = state.condition(condition)?;
                    state.assertions.push(if *expected {
                        condition
                    } else {
                        BoolExpr::logical_not(condition)
                    });
                    state.assertion_sources.push((instruction.index, node.id));
                }
                Predicate::Goto { .. } | Predicate::Exit | Predicate::Empty => {}
                Predicate::Load { .. } => {
                    return Err(unsupported(
                        path,
                        instruction.index,
                        node.id,
                        "memory load requires a region/alias contract",
                    ));
                }
                Predicate::Store { .. } => {
                    return Err(unsupported(
                        path,
                        instruction.index,
                        node.id,
                        "memory store requires a region/alias contract",
                    ));
                }
                Predicate::Call { .. } => {
                    return Err(unsupported(
                        path,
                        instruction.index,
                        node.id,
                        "helper call requires an explicit call contract",
                    ));
                }
                Predicate::IfGoto { .. } => {
                    return Err(unsupported(
                        path,
                        instruction.index,
                        node.id,
                        "residual conditional control is not a linear assert path",
                    ));
                }
                Predicate::Trap { .. } => {
                    return Err(unsupported(
                        path,
                        instruction.index,
                        node.id,
                        "trap has no normal predicate behavior",
                    ));
                }
            }
        }
    }

    let input_origins = state
        .entry_registers
        .iter()
        .filter_map(|(register, value)| match value {
            BvExpr::Var { name, .. } => Some((name.clone(), format!("entry register {register}"))),
            _ => None,
        })
        .collect();
    Ok(PathFormula {
        path_code: path.code.clone(),
        assertion: BoolExpr::and(state.assertions),
        entry_registers: state.entry_registers,
        assertion_sources: state.assertion_sources,
        input_origins,
        observations: Vec::new(),
    })
}

fn source_comment(side: &str, formula: &PathFormula) -> String {
    let sources = formula
        .assertion_sources()
        .iter()
        .map(|(index, id)| format!("{index}/{}", id.0))
        .collect::<Vec<_>>()
        .join(",");
    format!("{side} assert sources (index/predicate): {sources}")
}

fn entry_comment(side: &str, formula: &PathFormula) -> String {
    let entries = formula
        .entry_registers()
        .iter()
        .map(|(register, value)| match value {
            BvExpr::Var { name, width } => format!("{register}={name}:BV{width}"),
            value => format!("{register}=<derived>:BV{}", value.width()),
        })
        .collect::<Vec<_>>()
        .join(",");
    format!("{side} entry registers: {entries}")
}

fn origin_comment(side: &str, formula: &PathFormula) -> String {
    let inputs = formula
        .input_origins()
        .iter()
        .map(|(name, origin)| format!("{name}={origin}"))
        .collect::<Vec<_>>()
        .join(",");
    format!("{side} semantic inputs: {inputs}")
}

fn observation_comment(side: &str, formula: &PathFormula) -> String {
    let observations = formula
        .observations()
        .iter()
        .map(|(name, value)| format!("{name}:BV{}", value.width()))
        .collect::<Vec<_>>()
        .join(",");
    format!("{side} intermediate observations: {observations}")
}

fn observation_difference(left: &PathFormula, right: &PathFormula) -> BoolExpr {
    if left.observations.len() != right.observations.len() {
        return BoolExpr::Const(true);
    }
    let mut differences = Vec::new();
    for ((left_name, left_value), (right_name, right_value)) in
        left.observations.iter().zip(&right.observations)
    {
        if left_name != right_name || left_value.width() != right_value.width() {
            return BoolExpr::Const(true);
        }
        differences.push(BoolExpr::Compare {
            op: BvCmpOp::Ne,
            left: Box::new(left_value.clone()),
            right: Box::new(right_value.clone()),
        });
    }
    BoolExpr::or(differences)
}

/// Build the SAT query for a counterexample to paired-path assert equality and
/// any required intermediate observations.  An `unsat` result establishes the
/// assertion-only equality under `contract` and the stronger observations.
pub fn inequivalence_query(
    left: &PathFormula,
    right: &PathFormula,
    contract: BoolExpr,
) -> QfbvQuery {
    let behavior_difference = BoolExpr::or([
        BoolExpr::xor(left.assertion.clone(), right.assertion.clone()),
        observation_difference(left, right),
    ]);
    QfbvQuery::new(BoolExpr::and([
        contract,
        behavior_difference,
    ]))
    .with_comment(format!("left path: {}", left.path_code))
    .with_comment(format!("right path: {}", right.path_code))
    .with_comment(source_comment("left", left))
    .with_comment(source_comment("right", right))
    .with_comment(entry_comment("left", left))
    .with_comment(entry_comment("right", right))
    .with_comment(origin_comment("left", left))
    .with_comment(origin_comment("right", right))
    .with_comment(observation_comment("left", left))
    .with_comment(observation_comment("right", right))
    .with_comment(
        "asserted formula: contract AND ((left_asserts XOR right_asserts) OR observations_differ)",
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate::{Condition, Insn, Origin, Prefix};
    use crate::qfbv::{QfbvStatus, check_qfbv_file_with};
    use std::process::Command;

    fn node(id: u64, predicate: Predicate) -> crate::predicate::PredicateNode {
        crate::predicate::PredicateNode {
            id: PredicateId(id),
            predicate,
            origin: Origin::stage("test"),
        }
    }

    fn bpf_path(predicates: Vec<Predicate>) -> Path {
        Path {
            code: String::from("01"),
            insns: vec![Insn {
                index: 7,
                machine: Machine::Bpf(0),
                prefix: Prefix(
                    predicates
                        .into_iter()
                        .enumerate()
                        .map(|(id, predicate)| node(id as u64, predicate))
                        .collect(),
                ),
            }],
        }
    }

    fn assert_eq(register: Reg, value: BitVec) -> Predicate {
        Predicate::Assert {
            condition: Condition {
                lhs: Operand::Reg(register),
                op: CmpOp::Eq,
                rhs: Operand::Imm(value),
            },
            expected: true,
        }
    }

    #[test]
    fn bpf_writes_zero_extend_into_the_r_alias() {
        let path = bpf_path(vec![
            Predicate::Set {
                dst: Reg::w(1),
                src: Operand::Imm(BitVec::Bv32(1)),
            },
            assert_eq(Reg::r(1), BitVec::Bv64(1)),
        ]);
        let formula = compile_path_asserts(&path, "left").unwrap();
        let text = QfbvQuery::new(formula.assertion).to_smt2().unwrap();
        assert!(text.contains("((_ zero_extend 32) (_ bv1 32))"));
        assert!(!text.contains("declare-fun"));
    }

    #[test]
    fn inequivalence_query_declares_entry_contract_and_xor() {
        let left_path = bpf_path(vec![assert_eq(Reg::w(1), BitVec::Bv32(9))]);
        let right_path = Path {
            code: String::from("00"),
            insns: vec![Insn {
                index: 3,
                machine: Machine::Rv32(0),
                prefix: Prefix(vec![node(1, assert_eq(Reg::w(5), BitVec::Bv32(9)))]),
            }],
        };
        let left = compile_path_asserts(&left_path, "left").unwrap();
        let right = compile_path_asserts(&right_path, "right").unwrap();
        let left_input = left
            .entry_register("r1")
            .unwrap()
            .clone()
            .extract(31, 0)
            .unwrap();
        let right_input = right.entry_register("w5").unwrap().clone();
        let contract = BoolExpr::compare(BvCmpOp::Eq, left_input, right_input).unwrap();
        let text = inequivalence_query(&left, &right, contract)
            .to_smt2()
            .unwrap();
        assert!(text.contains("(declare-fun left_entry_r1 () (_ BitVec 64))"));
        assert!(text.contains("(declare-fun right_entry_w5 () (_ BitVec 32))"));
        assert!(text.contains("(xor"));
        assert_eq!(text.matches("(check-sat)").count(), 1);
    }

    #[test]
    fn inequivalence_query_includes_intermediate_observations() {
        let path = bpf_path(vec![assert_eq(Reg::w(1), BitVec::Bv32(9))]);
        let mut left = compile_path_asserts(&path, "left").unwrap();
        let mut right = compile_path_asserts(&path, "right").unwrap();
        left.observations.push((
            String::from("map_lookup_0_map_3_key"),
            BvExpr::constant(32, 1).unwrap(),
        ));
        right.observations.push((
            String::from("map_lookup_0_map_3_key"),
            BvExpr::constant(32, 2).unwrap(),
        ));
        let text = inequivalence_query(&left, &right, BoolExpr::Const(true))
            .to_smt2()
            .unwrap();
        assert!(text.contains("(distinct (_ bv1 32) (_ bv2 32))"));
        assert!(text.contains("observations_differ"));
    }

    #[test]
    fn effectful_predicates_fail_closed_with_provenance() {
        let path = bpf_path(vec![Predicate::Load {
            dst: Reg::w(0),
            width: crate::predicate::MemWidth::U32,
            addr: crate::predicate::Address {
                base: Reg::r(1),
                offset: None,
            },
        }]);
        let error = compile_path_asserts(&path, "left").unwrap_err();
        assert!(matches!(
            error,
            GoalError::Unsupported {
                path_code,
                insn_index: 7,
                predicate_id: PredicateId(0),
                ..
            } if path_code == "01"
        ));
    }

    #[test]
    fn shifts_mask_the_amount_and_signed_comparisons_stay_signed() {
        let path = bpf_path(vec![
            Predicate::AluAssign {
                dst: Reg::w(1),
                op: AluOp::Shl,
                rhs: Operand::Reg(Reg::w(2)),
            },
            Predicate::Assert {
                condition: Condition {
                    lhs: Operand::Reg(Reg::w(1)),
                    op: CmpOp::Slt,
                    rhs: Operand::Imm(BitVec::Bv32(0)),
                },
                expected: true,
            },
        ]);
        let formula = compile_path_asserts(&path, "left").unwrap();
        let text = QfbvQuery::new(formula.assertion).to_smt2().unwrap();
        assert!(text.contains("bvslt"));
        assert!(text.contains("(bvand"));
        assert!(text.contains("(_ bv31 32)"));
    }

    #[test]
    fn emitted_equivalence_is_unsat_in_optional_z3_smoke_test() {
        if Command::new("z3").arg("-version").output().is_err() {
            return;
        }

        let left_path = bpf_path(vec![assert_eq(Reg::w(1), BitVec::Bv32(9))]);
        let right_path = Path {
            code: String::from("00"),
            insns: vec![Insn {
                index: 3,
                machine: Machine::Rv32(0),
                prefix: Prefix(vec![node(1, assert_eq(Reg::w(5), BitVec::Bv32(9)))]),
            }],
        };
        let left = compile_path_asserts(&left_path, "left").unwrap();
        let right = compile_path_asserts(&right_path, "right").unwrap();
        let left_input = left
            .entry_register("r1")
            .unwrap()
            .clone()
            .extract(31, 0)
            .unwrap();
        let right_input = right.entry_register("w5").unwrap().clone();
        let contract = BoolExpr::compare(BvCmpOp::Eq, left_input, right_input).unwrap();
        let query = inequivalence_query(&left, &right, contract);
        let path =
            std::env::temp_dir().join(format!("classifier-qfbv-smoke-{}.smt2", std::process::id()));
        query.write_smt2(&path).unwrap();
        let result = check_qfbv_file_with("z3", &path, false);
        let _ = std::fs::remove_file(&path);
        assert_eq!(result.unwrap(), QfbvStatus::Unsat);
    }
}
