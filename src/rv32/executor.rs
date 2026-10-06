//! Isla single-instruction step adapter: state continuation + symbolic forks.
//!
//! RISC-V decode/execute semantics come from Sail IR (`isla_footprint_no_init`).
//! This module only schedules Isla tasks and carries `PhysicalState`.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, bail, Context, Result};
use isla_lib::bitvector::b129::B129;
use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::executor::{self, LocalFrame, Run, TaskId, TaskState};
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::{AssertionMode, IRTypeInfo, Loc, Name, Reset, SharedState, Symtab, UVal, Val};
use isla_lib::ir_lexer::new_ir_lexer;
use isla_lib::ir_parser;
use isla_lib::memory::Memory;
use isla_lib::smt::smtlib::{self, Exp, Ty};
use isla_lib::smt::{self, Checkpoint, Event, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;

use super::environment::Environment;
use super::footprint::{
    ensure_riscv32_toolchain_stubs, opcode_bytes, patch_rv32imc_ir, FootprintOpts,
};
use super::instruction::DecodedInstruction;
use super::state::PhysicalState;

const XLEN: u32 = 32;
const PACKET_CONTEXT_BASE: u32 = 0x4_0000;
const PACKET_DATA_BASE: u32 = 0x5_0000;
const STACK_SLAB_BYTES: u64 = 0x1000;
const PACKET_CONTEXT_BYTES: u64 = 0x40;
const PACKET_DATA_BYTES: u64 = 0x800;
const MAX_STEP_SIBLINGS: usize = 8;

const ABI: [&str; 32] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];

/// Pretty name for the initial symbolic value of GPR `x{i}`.
pub fn initial_gpr_name(i: u32) -> String {
    if i == 0 {
        return "0".into();
    }
    let abi = ABI[i as usize];
    if abi.chars().last().is_some_and(|c| c.is_ascii_digit()) {
        abi.to_string()
    } else {
        format!("{abi}0")
    }
}

/// Options for loading the Sail IR / ISA config used by the executor.
#[derive(Debug, Clone)]
pub struct ExecutorOpts {
    pub arch_ir: PathBuf,
    pub config: PathBuf,
    pub timeout: Option<u64>,
}

impl Default for ExecutorOpts {
    fn default() -> Self {
        let fp = FootprintOpts::default();
        Self {
            arch_ir: fp.arch_ir,
            config: fp.config,
            timeout: Some(5),
        }
    }
}

impl From<&FootprintOpts> for ExecutorOpts {
    fn from(fp: &FootprintOpts) -> Self {
        Self {
            arch_ir: fp.arch_ir.clone(),
            config: fp.config.clone(),
            timeout: Some(fp.timeout.unwrap_or(5).min(5)),
        }
    }
}

/// One successor after executing a single architecture instruction.
#[derive(Clone)]
pub struct StepResult {
    pub state: PhysicalState,
    pub events: Vec<Event<B129>>,
    /// Architectural PC after this step (`nextPC` committed as if `tick_pc` ran).
    pub pc: Val<B129>,
}

struct ArchStatic {
    iarch: Initialized<'static, B129>,
    footprint_id: Name,
    pc_name: Name,
    next_pc_name: Name,
    /// `x1`..`x31` (this Sail model has no `x0` register).
    gpr_names: [Name; 31],
}

/// Loaded Isla architecture + register name table for single-instruction steps.
pub struct IslaExecutor {
    arch: &'static ArchStatic,
    timeout: Option<u64>,
}

impl IslaExecutor {
    pub fn load(opts: &ExecutorOpts) -> Result<Self> {
        ensure_riscv32_toolchain_stubs()?;
        let arch = load_arch_static(opts)?;
        Ok(Self {
            arch,
            timeout: opts.timeout,
        })
    }

    pub fn pc_name(&self) -> Name {
        self.arch.pc_name
    }

    pub fn gpr_names(&self) -> &[Name; 31] {
        &self.arch.gpr_names
    }

    /// Build the initial symbolic state at `entry` (instruction table entry index).
    pub fn initial_state(
        &self,
        env: &Environment,
        entry_pc: u32,
    ) -> Result<PhysicalState> {
        let (checkpoint, regs) = build_initial_regs(self.arch, env, entry_pc)?;
        let memory = build_initial_memory(env);
        Ok(PhysicalState::new(checkpoint, regs, memory))
    }

    /// Execute one instruction under `state`, returning 0..N feasible successors.
    ///
    /// Seeds `nextPC = PC + insn.len` (fetch prelude that footprint skips), runs
    /// `isla_footprint_no_init`, then commits `PC ← nextPC` on each successor.
    pub fn step(
        &self,
        state: &PhysicalState,
        insn: &DecodedInstruction,
    ) -> Result<Vec<StepResult>> {
        let arch = self.arch;
        let shared_state: &SharedState<'static, B129> = &arch.iarch.shared_state;
        let pc_before = state
            .regs
            .get(&arch.pc_name)
            .and_then(concrete_u32)
            .ok_or_else(|| anyhow!("PC must be concrete before step"))?;
        let expected = insn.address;
        if pc_before != expected {
            bail!(
                "step PC {pc_before:#x} does not match instruction address {expected:#x} (index {})",
                insn.index
            );
        }

        let opcode_val = Val::Bits(opcode_bytes(insn.bytes.clone(), true)?);

        // Match the proven symexec pattern: only GPRs + PC go through
        // reset_registers. CSRs re-seed from model init; nextPC is handled
        // after execute (fetch prelude / tick), not via a wide reset map that
        // multiplies Sail forks.
        let mut reset: HashMap<Loc<Name>, Reset<B129>> = HashMap::new();
        for name in arch.gpr_names.iter().copied().chain([arch.pc_name]) {
            if let Some(val) = state.regs.get(&name) {
                reset.insert(Loc::Id(name), const_reset(val.clone()));
            }
        }
        // Fetch prelude that footprint skips: nextPC = PC + len.
        let fallthrough = Val::Bits(B129::from_u32(pc_before.wrapping_add(insn.len as u32)));
        reset.insert(Loc::Id(arch.next_pc_name), const_reset(fallthrough.clone()));

        let task_state = TaskState::new()
            .with_reset_registers(reset)
            .with_zero_announce_exit(false);

        let (args, ret_ty, instrs) = shared_state
            .functions
            .get(&arch.footprint_id)
            .ok_or_else(|| anyhow!("isla_footprint_no_init body missing"))?;

        let mut frame = LocalFrame::new(
            arch.footprint_id,
            args,
            ret_ty,
            Some(&[opcode_val]),
            instrs,
        );
        frame.add_lets(&arch.iarch.lets);
        frame.add_regs(&arch.iarch.regs);
        for (name, val) in &state.regs {
            if frame.regs().contains_key(*name) {
                frame.regs_mut().assign(*name, val.clone(), shared_state);
            } else {
                frame
                    .regs_mut()
                    .insert(*name, false, UVal::Init(val.clone()));
            }
        }
        // Ensure nextPC is visible even if not already in the snap.
        if frame.regs().contains_key(arch.next_pc_name) {
            frame
                .regs_mut()
                .assign(arch.next_pc_name, fallthrough.clone(), shared_state);
        } else {
            frame
                .regs_mut()
                .insert(arch.next_pc_name, false, UVal::Init(fallthrough.clone()));
        }
        frame.set_memory(state.memory.clone());

        let parent_len = state
            .checkpoint
            .trace()
            .as_ref()
            .map(|t| t.to_vec().len())
            .unwrap_or(0);
        let prev_regs = state.regs.clone();
        let task = frame.task_with_checkpoint(TaskId::fresh(), &task_state, state.checkpoint.clone());

        let collected = Arc::new(Mutex::new(Vec::<StepResult>::new()));
        let pc_name = arch.pc_name;
        let next_pc_name = arch.next_pc_name;
        let gpr_names = arch.gpr_names;
        let insn_len = insn.len as u32;

        executor::start_multi(
            1,
            self.timeout,
            vec![task],
            shared_state,
            collected.clone(),
            &move |_tid, _task_id, result, _ss, mut solver, bag| {
                match result {
                    Ok((Run::Finished(Val::Bool(true)), frame)) => {
                        let mut bag = bag.lock().unwrap();
                        if bag.len() >= MAX_STEP_SIBLINGS {
                            return;
                        }
                        let all = solver.trace().to_vec();
                        let new_count = all.len().saturating_sub(parent_len);
                        let mut events: Vec<Event<B129>> =
                            all.into_iter().take(new_count).cloned().collect();
                        events.reverse();
                        if let Some(i) = events.iter().rposition(|e| matches!(e, Event::Cycle)) {
                            events = events.split_off(i + 1);
                        }

                        let mut regs = HashMap::new();
                        for name in gpr_names
                            .iter()
                            .copied()
                            .chain([pc_name, next_pc_name])
                        {
                            if let Some(v) = frame.regs().get_last_if_initialized(name) {
                                regs.insert(name, v.clone());
                            }
                        }
                        // Carry prior GPRs/PC only — do not absorb ephemeral Isla
                        // frame regs (CSRs etc.); those churn every step and break
                        // loop fixed-point equality.
                        for (name, old) in &prev_regs {
                            regs.entry(*name).or_insert_with(|| old.clone());
                        }

                        // Commit tick_pc using nextPC / branch announce / fallthrough.
                        let next_pc = resolve_next_pc(
                            &events,
                            pc_before,
                            insn_len,
                            pc_name,
                            next_pc_name,
                            &regs,
                            &fallthrough,
                        );
                        regs.insert(pc_name, next_pc.clone());
                        regs.insert(next_pc_name, next_pc.clone());

                        let mut memory = frame.memory().clone();
                        // Concrete WriteMem → update zero slabs (Isla concrete
                        // regions do not auto-forward store events).
                        for ev in &events {
                            if let Event::WriteMem {
                                address,
                                data,
                                bytes,
                                ..
                            } = ev
                            {
                                if let (Some(a), Some(v)) =
                                    (concrete_u64(address), concrete_u64(data))
                                {
                                    for i in 0..*bytes as u64 {
                                        let b = ((v >> (8 * i)) & 0xff) as u8;
                                        memory.write_byte(a + i, b);
                                    }
                                }
                            }
                        }

                        let checkpoint = smt::checkpoint(&mut solver);
                        bag.push(StepResult {
                            state: PhysicalState::new(checkpoint, regs, memory),
                            events,
                            pc: next_pc,
                        });
                    }
                    Ok((Run::Finished(_) | Run::Exit | Run::Dead | Run::Suspended, _)) => {}
                    Err(_) => {}
                }
            },
        );

        Ok(match Arc::try_unwrap(collected) {
            Ok(m) => m.into_inner().unwrap(),
            Err(a) => std::mem::take(&mut *a.lock().unwrap()),
        })
    }

    /// Read a concrete u32 from `val` if possible.
    pub fn concrete_pc(val: &Val<B129>) -> Option<u32> {
        concrete_u32(val)
    }

    /// Symbolic id of a GPR value, if any (for continuity tests).
    pub fn symbolic_id(val: &Val<B129>) -> Option<Sym> {
        match val {
            Val::Symbolic(s) => Some(*s),
            _ => None,
        }
    }
}

fn load_arch_static(opts: &ExecutorOpts) -> Result<&'static ArchStatic> {
    let ir_text = patch_rv32imc_ir(
        &std::fs::read_to_string(&opts.arch_ir)
            .with_context(|| format!("read architecture IR {}", opts.arch_ir.display()))?,
    );
    let ir_text: &'static str = Box::leak(ir_text.into_boxed_str());
    let config_text = std::fs::read_to_string(&opts.config)
        .with_context(|| format!("read config {}", opts.config.display()))?;

    let mut symtab = Symtab::new();
    let arch = ir_parser::IrParser::new()
        .parse(&mut symtab, new_ir_lexer(ir_text))
        .map_err(|e| anyhow!("IR parse error: {e}"))?;
    let arch: &'static mut [_] = Box::leak(arch.into_boxed_slice());
    let type_info = IRTypeInfo::new(arch);

    let isa_config = ISAConfig::<B129>::parse(&config_text, None, &symtab, &type_info)
        .map_err(|e| anyhow!("{}: {e}", opts.config.display()))?;

    let iarch = initialize_architecture(
        arch,
        symtab,
        type_info,
        &isa_config,
        AssertionMode::Optimistic,
        true,
    );

    let footprint_z = zencode::encode("isla_footprint_no_init");
    let footprint_id = iarch
        .shared_state
        .symtab
        .get(&footprint_z)
        .ok_or_else(|| anyhow!("isla_footprint_no_init not found in IR"))?;

    let pc_name = iarch
        .shared_state
        .symtab
        .get(&zencode::encode("PC"))
        .ok_or_else(|| anyhow!("PC register not found"))?;
    let next_pc_name = iarch
        .shared_state
        .symtab
        .get(&zencode::encode("nextPC"))
        .ok_or_else(|| anyhow!("nextPC register not found"))?;

    let mut gpr_names = [Name::from_u32(0); 31];
    for i in 1..=31u32 {
        let z = zencode::encode(&format!("x{i}"));
        gpr_names[(i - 1) as usize] = iarch
            .shared_state
            .symtab
            .get(&z)
            .ok_or_else(|| anyhow!("register x{i} not found"))?;
    }

    Ok(Box::leak(Box::new(ArchStatic {
        iarch,
        footprint_id,
        pc_name,
        next_pc_name,
        gpr_names,
    })))
}

fn build_initial_memory(env: &Environment) -> Memory<B129> {
    let mut memory = Memory::new();
    if let Some(stack) = &env.stack {
        let top = stack.top_min as u64;
        let start = top.saturating_sub(STACK_SLAB_BYTES);
        let end = top.saturating_add(0x20);
        memory.add_zero_region(start..end);
    }
    if let Some(packet) = &env.packet {
        let ctx = PACKET_CONTEXT_BASE as u64;
        memory.add_zero_region(ctx..ctx + PACKET_CONTEXT_BYTES);
        let data = PACKET_DATA_BASE as u64;
        let data_len = PACKET_DATA_BYTES.min(packet.data_max as u64).max(64);
        memory.add_zero_region(data..data + data_len);
        write_u32_le(&mut memory, ctx, PACKET_DATA_BASE);
        write_u32_le(
            &mut memory,
            ctx + 4,
            PACKET_DATA_BASE.wrapping_add(data_len as u32),
        );
    }
    memory
}

fn write_u32_le(memory: &mut Memory<B129>, addr: u64, val: u32) {
    let bytes = val.to_le_bytes();
    for (i, b) in bytes.iter().enumerate() {
        memory.write_byte(addr + i as u64, *b);
    }
}

fn build_initial_regs(
    arch: &ArchStatic,
    env: &Environment,
    entry_pc: u32,
) -> Result<(Checkpoint<B129>, HashMap<Name, Val<B129>>)> {
    let cfg = smt::Config::new();
    let ctx = smt::Context::new(cfg);
    let mut solver = smt::Solver::<B129>::new(&ctx);
    let mut regs = HashMap::new();

    for i in 1..=31u32 {
        let reg = arch.gpr_names[(i - 1) as usize];
        let sym = solver.declare_const(Ty::BitVec(XLEN), SourceLoc::unknown());
        if i == 2 {
            if let Some(stack) = &env.stack {
                solver.assert(Exp::Eq(
                    Box::new(Exp::Var(sym)),
                    Box::new(smtlib::bits64(stack.top_min as u64, XLEN)),
                ));
            }
        } else if let Some(packet) = &env.packet {
            if i == packet.context_reg {
                solver.assert(Exp::Eq(
                    Box::new(Exp::Var(sym)),
                    Box::new(smtlib::bits64(PACKET_CONTEXT_BASE as u64, XLEN)),
                ));
            }
        }
        let val = Val::Symbolic(sym);
        regs.insert(reg, val.clone());
        solver.add_event(Event::AssumeReg(reg, vec![], val));
    }

    let pc_val = Val::Bits(B129::from_u32(entry_pc));
    regs.insert(arch.pc_name, pc_val.clone());
    solver.add_event(Event::AssumeReg(arch.pc_name, vec![], pc_val));

    let next = Val::Bits(B129::from_u32(entry_pc));
    regs.insert(arch.next_pc_name, next.clone());
    solver.add_event(Event::AssumeReg(arch.next_pc_name, vec![], next));

    Ok((smt::checkpoint(&mut solver), regs))
}

fn resolve_next_pc(
    events: &[Event<B129>],
    pc_before: u32,
    insn_len: u32,
    pc_name: Name,
    next_pc_name: Name,
    regs: &HashMap<Name, Val<B129>>,
    fallthrough: &Val<B129>,
) -> Val<B129> {
    let mut wrote_pc: Option<Val<B129>> = None;
    let mut branch: Option<Val<B129>> = None;
    for ev in events {
        match ev {
            Event::WriteReg(name, _, val) if *name == pc_name || *name == next_pc_name => {
                wrote_pc = Some(val.clone());
            }
            Event::Branch { address } => {
                branch = Some(address.clone());
            }
            _ => {}
        }
    }
    if let Some(v) = wrote_pc {
        if concrete_u32(&v).map(|p| p != pc_before).unwrap_or(true) {
            return v;
        }
    }
    if let Some(v) = regs.get(&next_pc_name) {
        if concrete_u32(v).map(|p| p != pc_before).unwrap_or(true) {
            return v.clone();
        }
    }
    if let Some(v) = branch {
        return v;
    }
    let _ = insn_len;
    fallthrough.clone()
}

fn concrete_u32(val: &Val<B129>) -> Option<u32> {
    match val {
        Val::Bits(b) => Some(b.lower_u64() as u32),
        _ => None,
    }
}

fn concrete_u64(val: &Val<B129>) -> Option<u64> {
    match val {
        Val::Bits(b) => Some(b.lower_u64()),
        _ => None,
    }
}

fn const_reset(v: Val<B129>) -> Reset<B129> {
    Arc::new(move |_, _, _| Ok(v.clone()))
}
