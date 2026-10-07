//! XDP-specific predicate semantics shared by BPF and RV32 paths.
//!
//! Physical registers and pointer widths are hidden behind logical regions.
//! Both ISAs read the same context, packet bytes, map bytes, and lookup-result
//! variables. Stack storage remains private to each path.

use std::collections::BTreeMap;

use crate::pathgen::Path;
use crate::predicate::{
    Address, AluOp, BitVec, CmpOp, Machine, MemWidth, Operand, Predicate, PredicateId, Reg,
};
use crate::rv32::{Environment, Helper};

use super::ast::{AstError, BoolExpr, BvBinaryOp, BvCmpOp, BvExpr};
use super::goal::{GoalError, PathFormula, apply_alu, bitvec, coerce};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum XdpArch {
    Bpf,
    Rv32,
}

#[derive(Clone, Debug)]
enum Value {
    Bits(BvExpr),
    Context,
    Stack(i64),
    Packet(i64),
    PacketEnd,
    Map { lookup: u32, offset: i64 },
}

struct XdpState<'a> {
    arch: XdpArch,
    side: &'a str,
    path: &'a Path,
    environment: Option<&'a Environment>,
    registers: BTreeMap<u32, Value>,
    stack: BTreeMap<(i64, u32), Value>,
    packet_bytes: BTreeMap<i64, BvExpr>,
    map_bytes: BTreeMap<(u32, i64), BvExpr>,
    assertions: Vec<BoolExpr>,
    assertion_sources: Vec<(u32, PredicateId)>,
    input_origins: BTreeMap<String, String>,
    observations: Vec<(String, BvExpr)>,
    lookup_count: u32,
}

impl<'a> XdpState<'a> {
    fn new(
        arch: XdpArch,
        side: &'a str,
        path: &'a Path,
        environment: Option<&'a Environment>,
    ) -> Result<Self, GoalError> {
        let _ = BvExpr::var(format!("{side}_probe"), 1)?;
        let mut registers = BTreeMap::new();
        match arch {
            XdpArch::Bpf => {
                registers.insert(1, Value::Context);
                registers.insert(10, Value::Stack(0));
            }
            XdpArch::Rv32 => {
                let packet = environment
                    .and_then(|environment| environment.packet.as_ref())
                    .ok_or_else(|| {
                        invalid(path, "RV32 XDP compilation requires packet contract")
                    })?;
                registers.insert(packet.context_reg, Value::Context);
                registers.insert(2, Value::Stack(0));
            }
        }
        Ok(Self {
            arch,
            side,
            path,
            environment,
            registers,
            stack: BTreeMap::new(),
            packet_bytes: BTreeMap::new(),
            map_bytes: BTreeMap::new(),
            assertions: Vec::new(),
            assertion_sources: Vec::new(),
            input_origins: BTreeMap::new(),
            observations: Vec::new(),
            lookup_count: 0,
        })
    }

    fn shared_input(
        &mut self,
        name: impl Into<String>,
        width: u32,
        origin: impl Into<String>,
    ) -> Result<BvExpr, GoalError> {
        let name = name.into();
        self.input_origins
            .entry(name.clone())
            .or_insert(origin.into());
        Ok(BvExpr::var(name, width)?)
    }

    fn private_input(
        &mut self,
        name: impl Into<String>,
        width: u32,
        origin: impl Into<String>,
    ) -> Result<BvExpr, GoalError> {
        let name = format!("{}_{}", self.side, name.into());
        self.input_origins
            .entry(name.clone())
            .or_insert(origin.into());
        Ok(BvExpr::var(name, width)?)
    }

    fn read_register(&mut self, register: &Reg) -> Result<Value, GoalError> {
        let (kind, number) = parse_register(self.path, register)?;
        match self.arch {
            XdpArch::Bpf => {
                if !matches!(kind, 'w' | 'r') {
                    return Err(invalid(
                        self.path,
                        format!("invalid BPF register `{register}`"),
                    ));
                }
                let full = match self.registers.get(&number) {
                    Some(value) => value.clone(),
                    None => {
                        let value = Value::Bits(self.private_input(
                            format!("entry_r{number}"),
                            64,
                            format!("BPF entry r{number}"),
                        )?);
                        self.registers.insert(number, value.clone());
                        value
                    }
                };
                match (kind, full) {
                    ('w', Value::Bits(value)) => Ok(Value::Bits(value.extract(31, 0)?)),
                    (_, value) => Ok(value),
                }
            }
            XdpArch::Rv32 => {
                if kind != 'w' {
                    return Err(invalid(
                        self.path,
                        format!("invalid RV32 register `{register}`"),
                    ));
                }
                if number == 0 {
                    return Ok(Value::Bits(BvExpr::constant(32, 0)?));
                }
                match self.registers.get(&number) {
                    Some(value) => Ok(value.clone()),
                    None => {
                        let value = Value::Bits(self.private_input(
                            format!("entry_w{number}"),
                            32,
                            format!("RV32 entry w{number}"),
                        )?);
                        self.registers.insert(number, value.clone());
                        Ok(value)
                    }
                }
            }
        }
    }

    fn write_register(&mut self, register: &Reg, value: Value) -> Result<(), GoalError> {
        let (kind, number) = parse_register(self.path, register)?;
        match self.arch {
            XdpArch::Bpf => {
                let value = match (kind, value) {
                    ('w', Value::Bits(value)) => Value::Bits(coerce(value, 32)?.zero_extend(64)?),
                    ('r', Value::Bits(value)) => Value::Bits(coerce(value, 64)?),
                    ('w' | 'r', value) => value,
                    _ => {
                        return Err(invalid(
                            self.path,
                            format!("invalid BPF destination `{register}`"),
                        ));
                    }
                };
                self.registers.insert(number, value);
            }
            XdpArch::Rv32 => {
                if kind != 'w' {
                    return Err(invalid(
                        self.path,
                        format!("invalid RV32 destination `{register}`"),
                    ));
                }
                if number != 0 {
                    let value = match value {
                        Value::Bits(value) => Value::Bits(coerce(value, 32)?),
                        value => value,
                    };
                    self.registers.insert(number, value);
                }
            }
        }
        Ok(())
    }

    fn operand(&mut self, operand: &Operand) -> Result<Value, GoalError> {
        match operand {
            Operand::Reg(register) => self.read_register(register),
            Operand::Imm(value) => Ok(Value::Bits(bitvec(*value)?)),
        }
    }

    fn add_offset(&self, value: Value, offset: i64) -> Result<Value, GoalError> {
        let add = |base: i64| {
            base.checked_add(offset)
                .ok_or_else(|| invalid(self.path, "pointer offset overflow"))
        };
        Ok(match value {
            Value::Context if offset == 0 => Value::Context,
            Value::Context => {
                return Err(invalid(
                    self.path,
                    format!("arithmetic on context pointer by {offset:+}"),
                ));
            }
            Value::Stack(base) => Value::Stack(add(base)?),
            Value::Packet(base) => Value::Packet(add(base)?),
            Value::Map {
                lookup,
                offset: base,
            } => Value::Map {
                lookup,
                offset: add(base)?,
            },
            Value::PacketEnd => {
                return Err(invalid(self.path, "arithmetic on packet_end pointer"));
            }
            Value::Bits(_) => {
                return Err(invalid(self.path, "expected pointer for pointer addition"));
            }
        })
    }

    fn apply_alu_value(
        &self,
        operation: AluOp,
        left: Value,
        right: Value,
    ) -> Result<Value, GoalError> {
        match (operation, left, right) {
            (AluOp::Add, pointer, Value::Bits(offset)) if !matches!(pointer, Value::Bits(_)) => {
                self.add_offset(pointer, signed_constant(self.path, &offset)?)
            }
            (AluOp::Add, Value::Bits(offset), pointer) if !matches!(pointer, Value::Bits(_)) => {
                self.add_offset(pointer, signed_constant(self.path, &offset)?)
            }
            (AluOp::Sub, pointer, Value::Bits(offset)) if !matches!(pointer, Value::Bits(_)) => {
                self.add_offset(pointer, signed_constant(self.path, &offset)?.wrapping_neg())
            }
            (operation, Value::Bits(left), Value::Bits(right)) => {
                Ok(Value::Bits(apply_alu(operation, left, right)?))
            }
            (operation, left, right) => Err(invalid(
                self.path,
                format!("unsupported {operation:?} operands {left:?} and {right:?}"),
            )),
        }
    }

    fn address(&mut self, address: &Address) -> Result<Value, GoalError> {
        let base = self.read_register(&address.base)?;
        match address.offset {
            None => Ok(base),
            Some(offset) => self.add_offset(base, signed_bitvec(offset)),
        }
    }

    fn pointer_bits(&mut self, value: Value, width: u32) -> Result<BvExpr, GoalError> {
        let logical = match value {
            Value::Bits(value) => return Ok(coerce(value, width)?),
            Value::Context => self.private_input(
                "context_ptr",
                32,
                format!("{} physical context pointer", self.side),
            )?,
            Value::Stack(offset) => {
                let base = self.private_input(
                    "stack_top",
                    32,
                    format!("{} private stack top", self.side),
                )?;
                add_constant(base, offset)?
            }
            Value::Packet(offset) => {
                self.validate_packet_range(offset, 1)?;
                let base = self.shared_input("input_packet_base", 32, "XDP packet data pointer")?;
                add_constant(base, offset)?
            }
            Value::PacketEnd => {
                self.shared_input("input_packet_end", 32, "XDP packet end pointer")?
            }
            Value::Map { lookup, offset } => {
                let base = self.shared_input(
                    format!("input_lookup_{lookup}_ptr"),
                    32,
                    format!("MapLookupElem result L{lookup}"),
                )?;
                add_constant(base, offset)?
            }
        };
        Ok(coerce(logical, width)?)
    }

    fn validate_packet_range(&self, offset: i64, bytes: u32) -> Result<(), GoalError> {
        let packet = self
            .environment
            .and_then(|environment| environment.packet.as_ref())
            .ok_or_else(|| invalid(self.path, "packet access requires an Environment"))?;
        let last = offset
            .checked_add(i64::from(bytes.saturating_sub(1)))
            .ok_or_else(|| invalid(self.path, "packet range overflow"))?;
        if offset < 0
            || last > i64::from(u32::MAX)
            || packet.data_max.checked_add(last as u32).is_none()
        {
            return Err(invalid(
                self.path,
                format!("packet range {offset:+}..={last:+} is outside the no-wrap contract"),
            ));
        }
        Ok(())
    }

    fn condition(
        &mut self,
        condition: &crate::predicate::Condition,
    ) -> Result<BoolExpr, GoalError> {
        let width = operand_width(self.path, self.arch, &condition.lhs)?;
        let right_width = operand_width(self.path, self.arch, &condition.rhs)?;
        if width != right_width {
            return Err(invalid(
                self.path,
                format!("comparison width mismatch: BV{width} versus BV{right_width}"),
            ));
        }
        let left_value = self.operand(&condition.lhs)?;
        let right_value = self.operand(&condition.rhs)?;
        let left = self.pointer_bits(left_value, width)?;
        let right = self.pointer_bits(right_value, width)?;
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
        Ok(BoolExpr::compare(operation, left, right)?)
    }

    fn load(
        &mut self,
        address: Value,
        memory_width: MemWidth,
        destination: &Reg,
        index: u32,
        id: PredicateId,
    ) -> Result<Value, GoalError> {
        let (bytes, signed) = memory_width_info(memory_width);
        let destination_width = register_width(self.path, self.arch, destination)?;
        match address {
            Value::Context if bytes == 4 => Err(unsupported(
                self.path,
                index,
                id,
                "context load requires explicit +0 data or +4 data_end offset",
            )),
            Value::Context => Err(unsupported(
                self.path,
                index,
                id,
                "unsupported context load width",
            )),
            Value::Stack(offset) => self.stack.get(&(offset, bytes)).cloned().ok_or_else(|| {
                unsupported(
                    self.path,
                    index,
                    id,
                    format!("uninitialized stack load at {offset:+}/{bytes}"),
                )
            }),
            Value::Packet(offset) => {
                self.validate_packet_range(offset, bytes)?;
                let raw = self.load_packet_bytes(offset, bytes)?;
                Ok(Value::Bits(extend_load(raw, destination_width, signed)?))
            }
            Value::Map { lookup, offset } => {
                let raw = self.load_map_bytes(lookup, offset, bytes)?;
                Ok(Value::Bits(extend_load(raw, destination_width, signed)?))
            }
            Value::Bits(_) | Value::PacketEnd => Err(unsupported(
                self.path,
                index,
                id,
                "load address has no proved logical memory region",
            )),
        }
    }

    fn load_context(
        &mut self,
        base: Value,
        offset: i64,
        bytes: u32,
        index: u32,
        id: PredicateId,
    ) -> Result<Value, GoalError> {
        if !matches!(base, Value::Context) || bytes != 4 {
            return Err(unsupported(
                self.path,
                index,
                id,
                "context access must be a u32 load at +0 or +4",
            ));
        }
        match offset {
            0 => Ok(Value::Packet(0)),
            4 => Ok(Value::PacketEnd),
            _ => Err(unsupported(
                self.path,
                index,
                id,
                format!("unknown context field at {offset:+}"),
            )),
        }
    }

    fn load_packet_bytes(&mut self, offset: i64, bytes: u32) -> Result<BvExpr, GoalError> {
        let mut values = Vec::new();
        for byte in 0..bytes {
            let at = offset
                .checked_add(byte.into())
                .ok_or_else(|| invalid(self.path, "packet byte offset overflow"))?;
            let value = match self.packet_bytes.get(&at) {
                Some(value) => value.clone(),
                None => self.shared_input(
                    packet_byte_name(at)?,
                    8,
                    format!("initial packet byte at {at:+}"),
                )?,
            };
            values.push(value);
        }
        assemble_le(values).map_err(Into::into)
    }

    fn load_map_bytes(
        &mut self,
        lookup: u32,
        offset: i64,
        bytes: u32,
    ) -> Result<BvExpr, GoalError> {
        let mut values = Vec::new();
        for byte in 0..bytes {
            let at = offset
                .checked_add(byte.into())
                .ok_or_else(|| invalid(self.path, "map byte offset overflow"))?;
            let value = match self.map_bytes.get(&(lookup, at)) {
                Some(value) => value.clone(),
                None => self.shared_input(
                    map_byte_name(lookup, at)?,
                    8,
                    format!("initial map L{lookup} byte at {at:+}"),
                )?,
            };
            values.push(value);
        }
        assemble_le(values).map_err(Into::into)
    }

    fn store(
        &mut self,
        address: Value,
        memory_width: MemWidth,
        source: Value,
        index: u32,
        id: PredicateId,
    ) -> Result<(), GoalError> {
        let (bytes, signed) = memory_width_info(memory_width);
        if signed {
            return Err(unsupported(
                self.path,
                index,
                id,
                "signed store width is invalid",
            ));
        }
        match address {
            Value::Stack(offset) => {
                self.stack.insert((offset, bytes), source);
                Ok(())
            }
            Value::Packet(offset) => {
                self.validate_packet_range(offset, bytes)?;
                let Value::Bits(value) = source else {
                    return Err(unsupported(
                        self.path,
                        index,
                        id,
                        "storing a pointer into packet memory is unsupported",
                    ));
                };
                for (byte, value) in split_le(value, bytes)?.into_iter().enumerate() {
                    self.packet_bytes.insert(offset + byte as i64, value);
                }
                Ok(())
            }
            Value::Map { lookup, offset } => {
                let Value::Bits(value) = source else {
                    return Err(unsupported(
                        self.path,
                        index,
                        id,
                        "storing a pointer into map memory is unsupported",
                    ));
                };
                for (byte, value) in split_le(value, bytes)?.into_iter().enumerate() {
                    self.map_bytes.insert((lookup, offset + byte as i64), value);
                }
                Ok(())
            }
            _ => Err(unsupported(
                self.path,
                index,
                id,
                "store address has no proved writable logical region",
            )),
        }
    }

    fn call(&mut self, target: &str, index: u32, id: PredicateId) -> Result<(), GoalError> {
        match self.arch {
            XdpArch::Bpf => {
                if parse_u64(target) != Some(1) {
                    return Err(unsupported(
                        self.path,
                        index,
                        id,
                        format!("unknown BPF helper target `{target}`"),
                    ));
                }
                let environment = self
                    .environment
                    .ok_or_else(|| invalid(self.path, "BPF helper call requires an Environment"))?;
                if environment.maps.len() != 1 {
                    return Err(unsupported(
                        self.path,
                        index,
                        id,
                        "BPF relocation placeholder requires exactly one map contract",
                    ));
                }
                let key_size = environment.maps[0].key_size;
                let map_argument = self.read_register(&Reg::r(1))?;
                if !matches!(map_argument, Value::Bits(ref value) if constant_u64(value) == Some(0))
                {
                    return Err(unsupported(
                        self.path,
                        index,
                        id,
                        "BPF map argument is not the unresolved zero relocation placeholder",
                    ));
                }
                let key_argument = self.read_register(&Reg::r(2))?;
                let key = self.validate_lookup_key(key_argument, key_size, index, id)?;
                let lookup = self.lookup_count;
                self.observations.push((
                    format!("map_lookup_{lookup}_map_{}_key", environment.maps[0].id),
                    key,
                ));
                for register in 0..=5 {
                    self.registers.remove(&register);
                }
                self.lookup_count += 1;
                self.registers.insert(0, Value::Map { lookup, offset: 0 });
            }
            XdpArch::Rv32 => {
                let environment = self.environment.ok_or_else(|| {
                    invalid(self.path, "RV32 helper call requires an Environment")
                })?;
                let contract = environment
                    .call(index as usize)
                    .map_err(|error| unsupported(self.path, index, id, error.to_string()))?
                    .clone();
                if contract.helper != Helper::MapLookupElem {
                    return Err(unsupported(
                        self.path,
                        index,
                        id,
                        format!("unsupported helper {}", contract.helper.name()),
                    ));
                }
                if parse_u64(target) != Some(contract.target.into()) {
                    return Err(unsupported(
                        self.path,
                        index,
                        id,
                        "call target disagrees with Environment contract",
                    ));
                }
                if let Some(selector) = &contract.selector {
                    let value = self.read_register(&Reg::w(selector.reg))?;
                    if !matches!(value, Value::Bits(ref value) if constant_u64(value) == Some(u64::from(selector.value)))
                    {
                        return Err(unsupported(
                            self.path,
                            index,
                            id,
                            "dispatcher selector disagrees with Environment contract",
                        ));
                    }
                }
                let map_argument = self.read_register(&Reg::w(contract.arg_regs[0]))?;
                let Value::Bits(map_argument) = map_argument else {
                    return Err(unsupported(
                        self.path,
                        index,
                        id,
                        "RV32 map argument is not a scalar handle",
                    ));
                };
                let Some(handle) =
                    constant_u64(&map_argument).and_then(|value| u32::try_from(value).ok())
                else {
                    return Err(unsupported(
                        self.path,
                        index,
                        id,
                        "RV32 map handle is not a concrete u32",
                    ));
                };
                let map = environment
                    .map(handle)
                    .map_err(|error| unsupported(self.path, index, id, error.to_string()))?
                    .clone();
                let key_argument = self.read_register(&Reg::w(contract.arg_regs[1]))?;
                let key = self.validate_lookup_key(key_argument, map.key_size, index, id)?;
                let lookup = self.lookup_count;
                self.observations
                    .push((format!("map_lookup_{lookup}_map_{}_key", map.id), key));
                for register in [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17] {
                    self.registers.remove(&register);
                }
                self.lookup_count += 1;
                self.registers.insert(10, Value::Map { lookup, offset: 0 });
            }
        }
        Ok(())
    }

    fn validate_lookup_key(
        &self,
        key: Value,
        key_size: u32,
        index: u32,
        id: PredicateId,
    ) -> Result<BvExpr, GoalError> {
        let Value::Stack(offset) = key else {
            return Err(unsupported(
                self.path,
                index,
                id,
                "MapLookup key is not a private stack pointer",
            ));
        };
        match self.stack.get(&(offset, key_size)) {
            Some(Value::Bits(value)) if value.width() == key_size * 8 => Ok(value.clone()),
            _ => Err(unsupported(
                self.path,
                index,
                id,
                format!("MapLookup key stack slot {offset:+}/{key_size} is not initialized"),
            )),
        }
    }

    fn execute(&mut self) -> Result<(), GoalError> {
        for instruction in &self.path.insns {
            for node in &instruction.prefix.0 {
                match &node.predicate {
                    Predicate::Set { dst, src } => {
                        let value = self.operand(src)?;
                        self.write_register(dst, value)?;
                    }
                    Predicate::AluAssign { dst, op, rhs } => {
                        if matches!(op, AluOp::Div | AluOp::Divu | AluOp::Rem | AluOp::Remu) {
                            return Err(unsupported(
                                self.path,
                                instruction.index,
                                node.id,
                                format!("{op:?} zero/overflow behavior is not modeled"),
                            ));
                        }
                        let left = self.read_register(dst)?;
                        let right = self.operand(rhs)?;
                        let value = self.apply_alu_value(*op, left, right)?;
                        self.write_register(dst, value)?;
                    }
                    Predicate::Alu { dst, op, lhs, rhs } => {
                        if matches!(op, AluOp::Div | AluOp::Divu | AluOp::Rem | AluOp::Remu) {
                            return Err(unsupported(
                                self.path,
                                instruction.index,
                                node.id,
                                format!("{op:?} zero/overflow behavior is not modeled"),
                            ));
                        }
                        let left = self.operand(lhs)?;
                        let right = self.operand(rhs)?;
                        let value = self.apply_alu_value(*op, left, right)?;
                        self.write_register(dst, value)?;
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
                                    self.path,
                                    instruction.index,
                                    node.id,
                                    format!("unknown ALU call `{other}`"),
                                ));
                            }
                        };
                        let left = self.operand(lhs)?;
                        let right = self.operand(rhs)?;
                        let value = self.apply_alu_value(operation, left, right)?;
                        self.write_register(dst, value)?;
                    }
                    Predicate::Load { dst, width, addr } => {
                        let base = self.read_register(&addr.base)?;
                        let offset = addr.offset.map(signed_bitvec).unwrap_or(0);
                        let value = if matches!(base, Value::Context) {
                            let (bytes, _) = memory_width_info(*width);
                            self.load_context(base, offset, bytes, instruction.index, node.id)?
                        } else {
                            let address = self.add_offset(base, offset)?;
                            self.load(address, *width, dst, instruction.index, node.id)?
                        };
                        self.write_register(dst, value)?;
                    }
                    Predicate::Store { width, addr, src } => {
                        let address = self.address(addr)?;
                        let source = self.operand(src)?;
                        self.store(address, *width, source, instruction.index, node.id)?;
                    }
                    Predicate::Assert {
                        condition,
                        expected,
                    } => {
                        let condition = self.condition(condition)?;
                        self.assertions.push(if *expected {
                            condition
                        } else {
                            BoolExpr::logical_not(condition)
                        });
                        self.assertion_sources.push((instruction.index, node.id));
                    }
                    Predicate::Call { target } => {
                        self.call(target, instruction.index, node.id)?;
                    }
                    Predicate::Goto { .. } | Predicate::Exit | Predicate::Empty => {}
                    Predicate::IfGoto { .. } => {
                        return Err(unsupported(
                            self.path,
                            instruction.index,
                            node.id,
                            "residual conditional control is not a linear assert path",
                        ));
                    }
                    Predicate::Trap { .. } => {
                        return Err(unsupported(
                            self.path,
                            instruction.index,
                            node.id,
                            "trap has no normal predicate behavior",
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    fn finish(self) -> PathFormula {
        PathFormula {
            path_code: self.path.code.clone(),
            assertion: BoolExpr::and(self.assertions),
            entry_registers: BTreeMap::new(),
            assertion_sources: self.assertion_sources,
            input_origins: self.input_origins,
            observations: self.observations,
        }
    }
}

fn invalid(path: &Path, reason: impl Into<String>) -> GoalError {
    GoalError::Invalid {
        path_code: path.code.clone(),
        reason: reason.into(),
    }
}

fn unsupported(path: &Path, index: u32, id: PredicateId, reason: impl Into<String>) -> GoalError {
    GoalError::Unsupported {
        path_code: path.code.clone(),
        insn_index: index,
        predicate_id: id,
        reason: reason.into(),
    }
}

fn path_arch(path: &Path) -> Result<XdpArch, GoalError> {
    let mut arch = None;
    for instruction in &path.insns {
        let current = match instruction.machine {
            Machine::Bpf(_) => XdpArch::Bpf,
            Machine::Rv32(_) | Machine::Rv16(_) => XdpArch::Rv32,
        };
        if let Some(previous) = arch
            && previous != current
        {
            return Err(invalid(path, "mixed BPF and RV32 machine words"));
        }
        arch = Some(current);
    }
    arch.ok_or_else(|| invalid(path, "empty path"))
}

fn parse_register(path: &Path, register: &Reg) -> Result<(char, u32), GoalError> {
    let mut chars = register.name.chars();
    let kind = chars
        .next()
        .ok_or_else(|| invalid(path, "empty register"))?;
    let number = chars
        .as_str()
        .parse()
        .map_err(|_| invalid(path, format!("malformed register `{register}`")))?;
    Ok((kind, number))
}

fn register_width(path: &Path, arch: XdpArch, register: &Reg) -> Result<u32, GoalError> {
    let (kind, _) = parse_register(path, register)?;
    match (arch, kind) {
        (XdpArch::Bpf, 'w') | (XdpArch::Rv32, 'w') => Ok(32),
        (XdpArch::Bpf, 'r') => Ok(64),
        _ => Err(invalid(
            path,
            format!("register `{register}` is invalid for {arch:?}"),
        )),
    }
}

fn operand_width(path: &Path, arch: XdpArch, operand: &Operand) -> Result<u32, GoalError> {
    match operand {
        Operand::Reg(register) => register_width(path, arch, register),
        Operand::Imm(value) => Ok(value.width_bits()),
    }
}

fn memory_width_info(width: MemWidth) -> (u32, bool) {
    match width {
        MemWidth::U8 => (1, false),
        MemWidth::U16 => (2, false),
        MemWidth::U32 => (4, false),
        MemWidth::U64 => (8, false),
        MemWidth::S8 => (1, true),
        MemWidth::S16 => (2, true),
        MemWidth::S32 => (4, true),
    }
}

fn signed_bitvec(value: BitVec) -> i64 {
    match value {
        BitVec::Bv8(value) => i8::from_ne_bytes([value]) as i64,
        BitVec::Bv16(value) => i16::from_ne_bytes(value.to_ne_bytes()) as i64,
        BitVec::Bv32(value) => i32::from_ne_bytes(value.to_ne_bytes()) as i64,
        BitVec::Bv64(value) => i64::from_ne_bytes(value.to_ne_bytes()),
    }
}

fn signed_constant(path: &Path, value: &BvExpr) -> Result<i64, GoalError> {
    let BvExpr::Const { value, width } = value else {
        return Err(invalid(path, "symbolic pointer offset"));
    };
    let shift = 64 - width;
    Ok(((*value << shift) as i64) >> shift)
}

fn add_constant(base: BvExpr, offset: i64) -> Result<BvExpr, AstError> {
    let width = base.width();
    apply_alu(AluOp::Add, base, BvExpr::constant(width, offset as u64)?)
}

fn extend_load(value: BvExpr, width: u32, signed: bool) -> Result<BvExpr, AstError> {
    if value.width() > width {
        value.extract(width - 1, 0)
    } else if signed {
        value.sign_extend(width)
    } else {
        value.zero_extend(width)
    }
}

fn assemble_le(mut bytes: Vec<BvExpr>) -> Result<BvExpr, AstError> {
    let Some(mut value) = bytes.pop() else {
        return Err(AstError(String::from(
            "cannot assemble empty byte sequence",
        )));
    };
    while let Some(low) = bytes.pop() {
        value = BvExpr::concat(value, low)?;
    }
    Ok(value)
}

fn split_le(value: BvExpr, bytes: u32) -> Result<Vec<BvExpr>, AstError> {
    let value = coerce(value, bytes * 8)?;
    (0..bytes)
        .map(|byte| value.clone().extract(byte * 8 + 7, byte * 8))
        .collect()
}

fn packet_byte_name(offset: i64) -> Result<String, GoalError> {
    if offset < 0 {
        return Err(GoalError::Invalid {
            path_code: String::from("<packet>"),
            reason: format!("negative packet offset {offset}"),
        });
    }
    Ok(format!("input_packet_b{offset}"))
}

fn map_byte_name(lookup: u32, offset: i64) -> Result<String, GoalError> {
    if offset < 0 {
        return Err(GoalError::Invalid {
            path_code: String::from("<map>"),
            reason: format!("negative map offset {offset}"),
        });
    }
    Ok(format!("input_map_{lookup}_b{offset}"))
}

fn parse_u64(text: &str) -> Option<u64> {
    text.strip_prefix("0x")
        .or_else(|| text.strip_prefix("0X"))
        .and_then(|hex| u64::from_str_radix(hex, 16).ok())
        .or_else(|| text.parse().ok())
}

fn constant_u64(expression: &BvExpr) -> Option<u64> {
    let value = match expression {
        BvExpr::Const { value, .. } => *value,
        BvExpr::Binary {
            op, left, right, ..
        } => {
            let left = constant_u64(left)?;
            let right = constant_u64(right)?;
            match op {
                BvBinaryOp::Add => left.wrapping_add(right),
                BvBinaryOp::Sub => left.wrapping_sub(right),
                _ => return None,
            }
        }
        BvExpr::Extract {
            value, high, low, ..
        } => (constant_u64(value)? >> low) & width_mask(high - low + 1),
        BvExpr::Extend { value, signed, .. } if !signed => constant_u64(value)?,
        _ => return None,
    };
    Some(value & width_mask(expression.width()))
}

fn width_mask(width: u32) -> u64 {
    if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn compile_xdp_path(
    path: &Path,
    side: &str,
    expected_arch: XdpArch,
    environment: Option<&Environment>,
) -> Result<PathFormula, GoalError> {
    let arch = path_arch(path)?;
    if arch != expected_arch {
        return Err(invalid(
            path,
            format!("expected {expected_arch:?}, found {arch:?}"),
        ));
    }
    let mut state = XdpState::new(arch, side, path, environment)?;
    state.execute()?;
    Ok(state.finish())
}

pub fn compile_xdp_bpf_path_asserts(
    path: &Path,
    environment: &Environment,
) -> Result<PathFormula, GoalError> {
    compile_xdp_path(path, "left", XdpArch::Bpf, Some(environment))
}

pub fn compile_xdp_rv32_path_asserts(
    path: &Path,
    environment: &Environment,
) -> Result<PathFormula, GoalError> {
    compile_xdp_path(path, "right", XdpArch::Rv32, Some(environment))
}

pub fn compile_xdp_assert_pair(
    bpf: &Path,
    rv32: &Path,
    environment: &Environment,
) -> Result<(PathFormula, PathFormula), GoalError> {
    Ok((
        compile_xdp_bpf_path_asserts(bpf, environment)?,
        compile_xdp_rv32_path_asserts(rv32, environment)?,
    ))
}

/// QF_BV form of the packet-address assumptions used by the logical XDP
/// pointer model.  In particular, `data_max` rules out 32-bit wraparound for
/// the bounded packet offsets exercised by the configured program.
pub fn xdp_environment_contract(environment: &Environment) -> Result<BoolExpr, GoalError> {
    let packet = environment
        .packet
        .as_ref()
        .ok_or_else(|| GoalError::Invalid {
            path_code: String::from("<environment>"),
            reason: String::from("XDP equivalence requires a packet contract"),
        })?;
    if environment.maps.len() != 1 {
        return Err(GoalError::Invalid {
            path_code: String::from("<environment>"),
            reason: String::from("current XDP equivalence requires exactly one map contract"),
        });
    }
    let base = BvExpr::var("input_packet_base", 32)?;
    let end = BvExpr::var("input_packet_end", 32)?;
    let data_max = BvExpr::constant(32, packet.data_max.into())?;
    let zero = BvExpr::constant(32, 0)?;
    let alignment_mask = BvExpr::constant(32, u64::from(packet.alignment - 1))?;
    let aligned = BvExpr::binary(BvBinaryOp::And, base.clone(), alignment_mask)?;
    Ok(BoolExpr::and([
        BoolExpr::compare(BvCmpOp::Ule, base.clone(), end)?,
        BoolExpr::compare(BvCmpOp::Ule, base, data_max)?,
        BoolExpr::compare(BvCmpOp::Eq, aligned, zero)?,
    ]))
}
