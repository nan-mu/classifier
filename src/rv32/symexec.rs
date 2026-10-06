//! Stateful RV32IMC symbolic execution via Isla `LocalFrame` / `Checkpoint`.
//!
//! Each architecture instruction runs `isla_footprint_no_init` once (IR patched
//! for C `ExecuteAs`), carrying registers via `TaskState::with_reset_registers`,
//! memory, and the SMT checkpoint. Model init runs once in
//! `initialize_architecture`; re-entering `isla_footprint`/`zinit` every step
//! bloated checkpoints and multiplied Sail forks. Sail-internal forks become
//! sibling path snapshots; symbolic PC targets are enumerated by the caller.
//! Paths explore under a tokio semaphore.

use std::collections::{BTreeMap, HashMap};
use std::fs::OpenOptions;
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

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
use isla_lib::smt::smtlib::{self, Def, Exp, Ty};
use isla_lib::smt::{self, Checkpoint, Event, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use tokio::sync::{mpsc, Semaphore};

use super::environment::Environment;
use super::footprint::{
    decode_rv32imc, ensure_riscv32_toolchain_stubs, opcode_bytes, patch_rv32imc_ir, DecodedInsn,
    FootprintOpts,
};

const XLEN: u32 = 32;
const MAX_SYMBOLIC_PC_TARGETS: usize = 32;
/// Concrete base for the pinned `xdp_md` slab when `Environment.packet` is set.
/// Kept clear of the default stack top (`0x10000`) and typical low image bases.
const PACKET_CONTEXT_BASE: u32 = 0x4_0000;
/// Concrete packet buffer pointed to by the seeded `data` / `data_end` fields.
const PACKET_DATA_BASE: u32 = 0x5_0000;
/// Bytes reserved below `stack.top_min` for the concrete stack slab.
const STACK_SLAB_BYTES: u64 = 0x1000;
/// Bytes reserved for the pinned `xdp_md` (+ pointers) slab.
const PACKET_CONTEXT_BYTES: u64 = 0x40;
/// Default packet buffer size when `Environment.packet` is set.
const PACKET_DATA_BYTES: u64 = 0x800;
/// Hard cap on Sail forks kept from a single architecture instruction.
const MAX_STEP_SIBLINGS: usize = 8;

// #region agent log
fn agent_log(hypothesis_id: &str, location: &str, message: &str, data: &str) {
    let ts = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis())
        .unwrap_or(0);
    let line = format!(
        "{{\"sessionId\":\"439aa1\",\"hypothesisId\":\"{hypothesis_id}\",\"location\":\"{location}\",\"message\":\"{message}\",\"data\":{data},\"timestamp\":{ts}}}\n"
    );
    if let Ok(mut f) = OpenOptions::new()
        .create(true)
        .append(true)
        .open("/Users/nan/bs/classifier/.cursor/debug-439aa1.log")
    {
        let _ = f.write_all(line.as_bytes());
    }
}
// #endregion

static STEP_COUNTER: AtomicUsize = AtomicUsize::new(0);
static MAX_INFLIGHT: AtomicUsize = AtomicUsize::new(0);
static MAX_SIBLINGS: AtomicUsize = AtomicUsize::new(0);
static MAX_CKPT_EVENTS: AtomicUsize = AtomicUsize::new(0);

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

/// Options for the stateful tree explorer.
#[derive(Debug, Clone)]
pub struct SymexecOpts {
    pub footprint: FootprintOpts,
    /// Cap concurrent Isla steps (default: min(4, available parallelism)).
    pub tokens: usize,
    /// Soft cap on finished paths for symexec (min'd with `Environment.max_paths`).
    /// Default 128 — the legacy string pipeline still uses the full env budget.
    pub path_budget: usize,
}

impl Default for SymexecOpts {
    fn default() -> Self {
        let n = std::thread::available_parallelism()
            .map(usize::from)
            .unwrap_or(1);
        Self {
            footprint: FootprintOpts::default(),
            tokens: n.min(4).max(1),
            path_budget: 128,
        }
    }
}

/// One finished root-to-leaf path, ready to format.
#[derive(Debug, Clone)]
pub struct ExecPath {
    pub tree_key: Vec<u8>,
    pub steps: Vec<StepRecord>,
}

#[derive(Debug, Clone)]
pub struct StepRecord {
    pub insn_index: usize,
    pub lines: Vec<String>,
    pub state_lines: Vec<String>,
}

struct ArchStatic {
    iarch: Initialized<'static, B129>,
    footprint_id: Name,
    pc_name: Name,
    /// `x1`..`x31` (this Sail model has no `x0` register).
    gpr_names: [Name; 31],
}

struct SharedCtx {
    arch: &'static ArchStatic,
    insns: Vec<DecodedInsn>,
    offset_to_index: HashMap<usize, usize>,
    image_base: u32,
    code_start: u32,
    code_end: u32,
    max_paths: usize,
    max_path_len: usize,
    /// Per-instruction Isla exploration timeout (seconds).
    step_timeout: Option<u64>,
    /// Cap on simultaneously live exploring tasks (not only finished paths).
    max_inflight: usize,
}

#[derive(Clone)]
struct PathSnap {
    checkpoint: Checkpoint<B129>,
    regs: HashMap<Name, Val<B129>>,
    memory: Memory<B129>,
    tree_key: Vec<u8>,
    steps: Vec<StepRecord>,
    state_regs: BTreeMap<String, String>,
    state_mem: BTreeMap<String, String>,
    /// Sym → pretty expression / initial name.
    sym_names: HashMap<Sym, String>,
    path_len: usize,
    pc_visits: HashMap<u32, usize>,
}

struct RawStep {
    regs: HashMap<Name, Val<B129>>,
    memory: Memory<B129>,
    checkpoint: Checkpoint<B129>,
    events: Vec<Event<B129>>,
    /// Isla `Event::Fork` branch numbers seen on this path (0 = true/taken).
    fork_branches: Vec<u8>,
}

/// Load IR once, leak to `'static`, explore from `env.entry`, return sorted paths.
pub fn explore_bin(bin: &[u8], env: &Environment, opts: &SymexecOpts) -> Result<Vec<ExecPath>> {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .context("build tokio runtime")?;
    rt.block_on(explore_bin_async(bin, env, opts))
}

async fn explore_bin_async(
    bin: &[u8],
    env: &Environment,
    opts: &SymexecOpts,
) -> Result<Vec<ExecPath>> {
    ensure_riscv32_toolchain_stubs()?;
    let insns = decode_rv32imc(bin)?;
    if insns.is_empty() {
        bail!("no instructions decoded from image ({} bytes)", bin.len());
    }
    if env.entry >= insns.len() {
        bail!(
            "environment entry {} out of range ({} instructions)",
            env.entry,
            insns.len()
        );
    }

    let arch = load_arch_static(&opts.footprint)?;
    let mut offset_to_index = HashMap::new();
    for (i, insn) in insns.iter().enumerate() {
        offset_to_index.insert(insn.offset, i);
    }
    let last = insns.last().unwrap();
    let code_end = env
        .image_base
        .wrapping_add(last.offset as u32)
        .wrapping_add(last.bytes.len() as u32);

    let (initial_checkpoint, regs, sym_names, state_regs) =
        build_initial_state(arch, env, &insns[env.entry])?;

    // Opcodes are caller-supplied. Map concrete stack / xdp_md slabs as zeroed
    // RAM (Isla's `--zero-memory` idea, scoped) so SP-/context-relative loads
    // do not fall into default `read_symbolic` and explode into forks. Pinning
    // SP and a0 keeps those addresses out of unconstrained alias checks.
    let memory = build_initial_memory(env);

    let max_paths = env.max_paths.min(opts.path_budget).max(1);
    let tokens = opts.tokens.max(1);
    let max_inflight = (tokens.saturating_mul(4)).clamp(4, max_paths);

    let shared = Arc::new(SharedCtx {
        arch,
        insns,
        offset_to_index,
        image_base: env.image_base,
        code_start: env.image_base,
        code_end,
        max_paths,
        max_path_len: env.max_path_len,
        // Bound Sail fork storms per insn; default 2s keeps interactive runs responsive.
        step_timeout: Some(opts.footprint.timeout.unwrap_or(2).min(2)),
        max_inflight,
    });

    let root = PathSnap {
        checkpoint: initial_checkpoint,
        regs,
        memory,
        tree_key: Vec::new(),
        steps: Vec::new(),
        state_regs,
        state_mem: BTreeMap::new(),
        sym_names,
        path_len: 0,
        pc_visits: HashMap::new(),
    };

    let tokens = opts.tokens.max(1);
    // #region agent log
    STEP_COUNTER.store(0, Ordering::SeqCst);
    MAX_INFLIGHT.store(0, Ordering::SeqCst);
    MAX_SIBLINGS.store(0, Ordering::SeqCst);
    MAX_CKPT_EVENTS.store(0, Ordering::SeqCst);
    agent_log(
        "C",
        "symexec.rs:explore_bin_async",
        "explore_start",
        &format!(
            "{{\"tokens\":{tokens},\"max_paths\":{},\"max_path_len\":{},\"insns\":{}}}",
            env.max_paths,
            env.max_path_len,
            shared.insns.len()
        ),
    );
    // #endregion
    let sem = Arc::new(Semaphore::new(tokens));
    let finished = Arc::new(Mutex::new(Vec::<ExecPath>::new()));
    let inflight = Arc::new(AtomicUsize::new(0));
    let (done_tx, mut done_rx) = mpsc::unbounded_channel::<Result<()>>();

    inflight.fetch_add(1, Ordering::SeqCst);
    spawn_path(
        root,
        shared.clone(),
        sem,
        finished.clone(),
        inflight.clone(),
        done_tx,
    );

    let mut first_err: Option<anyhow::Error> = None;
    while inflight.load(Ordering::SeqCst) > 0 {
        // #region agent log
        let inf = inflight.load(Ordering::SeqCst);
        MAX_INFLIGHT.fetch_max(inf, Ordering::SeqCst);
        let fin = finished.lock().unwrap().len();
        let steps = STEP_COUNTER.load(Ordering::SeqCst);
        if steps > 0 && steps % 25 == 0 {
            agent_log(
                "C",
                "symexec.rs:explore_wait",
                "progress",
                &format!(
                    "{{\"inflight\":{inf},\"finished\":{fin},\"steps\":{steps},\"max_inflight\":{},\"max_siblings\":{},\"max_ckpt\":{}}}",
                    MAX_INFLIGHT.load(Ordering::SeqCst),
                    MAX_SIBLINGS.load(Ordering::SeqCst),
                    MAX_CKPT_EVENTS.load(Ordering::SeqCst)
                ),
            );
        }
        // #endregion
        match done_rx.recv().await {
            Some(Ok(())) => {}
            Some(Err(e)) => {
                if first_err.is_none() {
                    first_err = Some(e);
                }
            }
            None => break,
        }
    }
    if let Some(e) = first_err {
        return Err(e);
    }

    let mut paths = finished.lock().unwrap().clone();
    paths.sort_by(|a, b| a.tree_key.cmp(&b.tree_key));
    // #region agent log
    agent_log(
        "C",
        "symexec.rs:explore_bin_async",
        "explore_done",
        &format!(
            "{{\"paths\":{},\"steps\":{},\"max_inflight\":{},\"max_siblings\":{},\"max_ckpt\":{}}}",
            paths.len(),
            STEP_COUNTER.load(Ordering::SeqCst),
            MAX_INFLIGHT.load(Ordering::SeqCst),
            MAX_SIBLINGS.load(Ordering::SeqCst),
            MAX_CKPT_EVENTS.load(Ordering::SeqCst)
        ),
    );
    // #endregion
    unsafe {
        isla_lib::smt::finalize_solver();
    }
    Ok(paths)
}

fn spawn_path(
    snap: PathSnap,
    shared: Arc<SharedCtx>,
    sem: Arc<Semaphore>,
    finished: Arc<Mutex<Vec<ExecPath>>>,
    inflight: Arc<AtomicUsize>,
    done_tx: mpsc::UnboundedSender<Result<()>>,
) {
    tokio::spawn(async move {
        let result =
            run_path(snap, shared, sem, finished, inflight.clone(), done_tx.clone()).await;
        inflight.fetch_sub(1, Ordering::SeqCst);
        let _ = done_tx.send(result);
    });
}

async fn run_path(
    mut snap: PathSnap,
    shared: Arc<SharedCtx>,
    sem: Arc<Semaphore>,
    finished: Arc<Mutex<Vec<ExecPath>>>,
    inflight: Arc<AtomicUsize>,
    done_tx: mpsc::UnboundedSender<Result<()>>,
) -> Result<()> {
    let permit = sem.clone().acquire_owned().await.expect("semaphore open");

    loop {
        if snap.path_len >= shared.max_path_len {
            record_finished(&shared, &finished, snap);
            return Ok(());
        }
        if finished.lock().unwrap().len() >= shared.max_paths {
            return Ok(());
        }

        let shared_step = shared.clone();
        let step_snap = snap.clone();
        let raws = tokio::task::spawn_blocking(move || isla_step(step_snap, &shared_step))
            .await
            .context("join spawn_blocking")??;

        if raws.is_empty() {
            return Ok(());
        }

        let sibling_count = raws.len();
        // #region agent log
        let n = STEP_COUNT.fetch_add(1, Ordering::SeqCst) + 1;
        MAX_SIBLINGS.fetch_max(sibling_count, Ordering::SeqCst);
        let inf = inflight.load(Ordering::SeqCst);
        MAX_INFLIGHT.fetch_max(inf, Ordering::SeqCst);
        let ckpt = snap
            .checkpoint
            .trace()
            .as_ref()
            .map(|t| t.to_vec().len())
            .unwrap_or(0);
        MAX_CKPT_EVENTS.fetch_max(ckpt, Ordering::SeqCst);
        let fin = finished.lock().unwrap().len();
        if sibling_count > 2 || n <= 5 || n % 20 == 0 {
            agent_log(
                "A",
                "symexec.rs:run_path",
                "step",
                &format!(
                    "{{\"n\":{n},\"siblings\":{sibling_count},\"path_len\":{},\"ckpt_events\":{ckpt},\"inflight\":{inf},\"finished\":{fin},\"children_pending\":0}}",
                    snap.path_len
                ),
            );
        }
        // #endregion
        let mut children: Vec<PathSnap> = Vec::new();
        for (i, raw) in raws.into_iter().enumerate() {
            let mut child = apply_step(snap.clone(), raw, &shared, i as u8, sibling_count)?;
            match next_action(&mut child, &shared)? {
                Action::Finish => {
                    record_finished(&shared, &finished, child);
                }
                Action::Continue => children.push(child),
                Action::Fork(more) => {
                    // #region agent log
                    if more.len() > 1 {
                        agent_log(
                            "A",
                            "symexec.rs:run_path",
                            "symbolic_pc_fork",
                            &format!("{{\"more\":{}}}", more.len()),
                        );
                    }
                    // #endregion
                    children.extend(more);
                }
            }
        }

        if children.is_empty() {
            return Ok(());
        }
        if children.len() == 1 {
            snap = children.into_iter().next().unwrap();
            continue;
        }

        // #region agent log
        agent_log(
            "C",
            "symexec.rs:run_path",
            "spawn_siblings",
            &format!(
                "{{\"children\":{},\"inflight_before\":{},\"finished\":{}}}",
                children.len(),
                inflight.load(Ordering::SeqCst),
                finished.lock().unwrap().len()
            ),
        );
        // #endregion

        // Release token before spawning siblings.
        drop(permit);
        for child in children {
            // Budget live work (finished + still exploring), not only completed paths.
            let fin = finished.lock().unwrap().len();
            let inf = inflight.load(Ordering::SeqCst);
            if fin >= shared.max_paths
                || fin + inf >= shared.max_paths
                || inf >= shared.max_inflight
            {
                // #region agent log
                agent_log(
                    "D",
                    "symexec.rs:run_path",
                    "live_over_budget",
                    &format!(
                        "{{\"live\":{},\"max_paths\":{},\"max_inflight\":{},\"inflight\":{inf},\"finished\":{fin}}}",
                        fin + inf,
                        shared.max_paths,
                        shared.max_inflight
                    ),
                );
                // #endregion
                break;
            }
            inflight.fetch_add(1, Ordering::SeqCst);
            spawn_path(
                child,
                shared.clone(),
                sem.clone(),
                finished.clone(),
                inflight.clone(),
                done_tx.clone(),
            );
        }
        return Ok(());
    }
}

enum Action {
    Finish,
    Continue,
    Fork(Vec<PathSnap>),
}

fn next_action(snap: &mut PathSnap, shared: &SharedCtx) -> Result<Action> {
    let pc_val = snap
        .regs
        .get(&shared.arch.pc_name)
        .cloned()
        .ok_or_else(|| anyhow!("PC missing after step"))?;

    match concrete_u32(&pc_val) {
        Some(pc) => {
            *snap.pc_visits.entry(pc).or_insert(0) += 1;
            if snap.pc_visits[&pc] > shared.max_path_len {
                return Ok(Action::Finish);
            }
            if pc < shared.code_start || pc >= shared.code_end {
                return Ok(Action::Finish);
            }
            let offset = pc.wrapping_sub(shared.image_base) as usize;
            if !shared.offset_to_index.contains_key(&offset) {
                return Ok(Action::Finish);
            }
            Ok(Action::Continue)
        }
        None => Ok(Action::Fork(enumerate_symbolic_pc(snap.clone(), shared)?)),
    }
}

fn enumerate_symbolic_pc(snap: PathSnap, shared: &SharedCtx) -> Result<Vec<PathSnap>> {
    let pc_name = shared.arch.pc_name;
    let pc_val = snap
        .regs
        .get(&pc_name)
        .cloned()
        .ok_or_else(|| anyhow!("PC missing for symbolic enumeration"))?;
    let Val::Symbolic(pc_sym) = pc_val else {
        bail!("expected symbolic PC");
    };

    if shared.insns.len() > MAX_SYMBOLIC_PC_TARGETS {
        bail!(
            "symbolic PC has {} in-range targets (cap {MAX_SYMBOLIC_PC_TARGETS})",
            shared.insns.len()
        );
    }

    let mut out = Vec::new();
    for (enum_i, insn) in shared.insns.iter().enumerate() {
        let addr = shared.image_base.wrapping_add(insn.offset as u32);
        let mut child = snap.clone();
        child.tree_key.push(enum_i as u8);

        let cfg = smt::Config::new();
        let ctx = smt::Context::new(cfg);
        let mut solver = smt::Solver::from_checkpoint(&ctx, child.checkpoint.clone());
        solver.assert(Exp::Eq(
            Box::new(Exp::Var(pc_sym)),
            Box::new(smtlib::bits64(addr as u64, XLEN)),
        ));
        if !solver
            .check_sat(SourceLoc::unknown())
            .is_sat()
            .map_err(|e| anyhow!("Z3 check_sat: {e}"))?
        {
            continue;
        }
        child.checkpoint = smt::checkpoint(&mut solver);
        child.regs.insert(pc_name, Val::Bits(B129::from_u32(addr)));
        out.push(child);
    }
    Ok(out)
}

fn record_finished(shared: &SharedCtx, finished: &Mutex<Vec<ExecPath>>, snap: PathSnap) {
    let mut g = finished.lock().unwrap();
    if g.len() >= shared.max_paths {
        return;
    }
    g.push(ExecPath {
        tree_key: snap.tree_key,
        steps: snap.steps,
    });
}

fn load_arch_static(opts: &FootprintOpts) -> Result<&'static ArchStatic> {
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
        gpr_names,
    })))
}

fn build_initial_memory(env: &Environment) -> Memory<B129> {
    let mut memory = Memory::new();
    if let Some(stack) = &env.stack {
        let top = stack.top_min as u64;
        let start = top.saturating_sub(STACK_SLAB_BYTES);
        // Inclusive of a few bytes above SP for ABI red-zone style accesses.
        let end = top.saturating_add(0x20);
        memory.add_zero_region(start..end);
    }
    if let Some(packet) = &env.packet {
        let ctx = PACKET_CONTEXT_BASE as u64;
        memory.add_zero_region(ctx..ctx + PACKET_CONTEXT_BYTES);
        let data = PACKET_DATA_BASE as u64;
        let data_len = PACKET_DATA_BYTES.min(packet.data_max as u64).max(64);
        memory.add_zero_region(data..data + data_len);
        // Seed xdp_md.{data,data_end} so loads do not see null and then take
        // the unconstrained symbolic-address path into the Sail memory model.
        write_u32_le(&mut memory, ctx, PACKET_DATA_BASE);
        write_u32_le(&mut memory, ctx + 4, PACKET_DATA_BASE.wrapping_add(data_len as u32));
    }
    memory
}

fn write_u32_le(memory: &mut Memory<B129>, addr: u64, val: u32) {
    let bytes = val.to_le_bytes();
    for (i, b) in bytes.iter().enumerate() {
        memory.write_byte(addr + i as u64, *b);
    }
}

fn build_initial_state(
    arch: &ArchStatic,
    env: &Environment,
    entry_insn: &DecodedInsn,
) -> Result<(
    Checkpoint<B129>,
    HashMap<Name, Val<B129>>,
    HashMap<Sym, String>,
    BTreeMap<String, String>,
)> {
    let cfg = smt::Config::new();
    let ctx = smt::Context::new(cfg);
    let mut solver = smt::Solver::new(&ctx);

    let mut regs = HashMap::new();
    let mut sym_names = HashMap::new();
    let mut state_regs = BTreeMap::new();

    // Seed non-GPR registers from the architecture init (CSRs, etc.).
    for (name, reg) in arch.iarch.regs.iter() {
        if let Some(value) = reg.read_last_if_initialized() {
            solver.add_event(Event::AssumeReg(*name, vec![], value.clone()));
            regs.insert(*name, value.clone());
        }
    }

    // x0 is hardwired; this IR has no zx0 register.
    state_regs.insert("x0".into(), "0".into());

    for i in 1..=31u32 {
        let reg = arch.gpr_names[(i - 1) as usize];
        let sym = solver.declare_const(Ty::BitVec(XLEN), SourceLoc::unknown());
        let name = initial_gpr_name(i);
        sym_names.insert(sym, name.clone());
        // Pin SP / packet context to concrete slab bases (keep symbol names in dumps).
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
        state_regs.insert(format!("x{i}"), name);
        solver.add_event(Event::AssumeReg(reg, vec![], val));
    }

    let entry_pc = env.image_base.wrapping_add(entry_insn.offset as u32);
    let pc_val = Val::Bits(B129::from_u32(entry_pc));
    regs.insert(arch.pc_name, pc_val.clone());
    solver.add_event(Event::AssumeReg(arch.pc_name, vec![], pc_val));

    Ok((smt::checkpoint(&mut solver), regs, sym_names, state_regs))
}

fn isla_step(snap: PathSnap, shared: &SharedCtx) -> Result<Vec<RawStep>> {
    let arch = shared.arch;
    let shared_state: &SharedState<'static, B129> = &arch.iarch.shared_state;

    let pc_val = snap
        .regs
        .get(&arch.pc_name)
        .ok_or_else(|| anyhow!("PC missing before step"))?;
    let pc = concrete_u32(pc_val).ok_or_else(|| anyhow!("PC still symbolic at isla_step"))?;
    let offset = pc.wrapping_sub(shared.image_base) as usize;
    let insn_index = *shared
        .offset_to_index
        .get(&offset)
        .ok_or_else(|| anyhow!("no instruction at PC {pc:#x}"))?;
    let insn = &shared.insns[insn_index];
    let opcode_val = Val::Bits(opcode_bytes(insn.bytes.clone(), true)?);

    let mut reset: HashMap<Loc<Name>, Reset<B129>> = HashMap::new();
    // Only carry GPRs + PC through reset_registers; CSRs re-seed from model init.
    for i in 0..31 {
        let name = arch.gpr_names[i];
        if let Some(val) = snap.regs.get(&name) {
            reset.insert(Loc::Id(name), const_reset(val.clone()));
        }
    }
    if let Some(val) = snap.regs.get(&arch.pc_name) {
        reset.insert(Loc::Id(arch.pc_name), const_reset(val.clone()));
    }
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
    for (name, val) in &snap.regs {
        if frame.regs().contains_key(*name) {
            frame.regs_mut().assign(*name, val.clone(), shared_state);
        } else {
            frame
                .regs_mut()
                .insert(*name, false, UVal::Init(val.clone()));
        }
    }
    frame.set_memory(snap.memory);

    let parent_len = snap
        .checkpoint
        .trace()
        .as_ref()
        .map(|t| t.to_vec().len())
        .unwrap_or(0);
    let prev_regs = snap.regs;
    let task =
        frame.task_with_checkpoint(TaskId::fresh(), &task_state, snap.checkpoint);

    let collected = Arc::new(Mutex::new(Vec::<RawStep>::new()));
    let gpr_names = arch.gpr_names;
    let pc_name = arch.pc_name;
    let capped = AtomicUsize::new(0);

    // start_multi (1 worker + short timeout) so a Sail fork storm cannot run
    // unbounded like start_single's Timeout::unlimited().
    executor::start_multi(
        1,
        shared.step_timeout,
        vec![task],
        shared_state,
        collected.clone(),
        &move |_tid, _task_id, result, _ss, mut solver, bag| {
            match result {
                Ok((Run::Finished(Val::Bool(true)), frame)) => {
                    let mut bag = bag.lock().unwrap();
                    if bag.len() >= MAX_STEP_SIBLINGS {
                        if capped.fetch_add(1, Ordering::SeqCst) == 0 {
                            // #region agent log
                            agent_log(
                                "A",
                                "symexec.rs:isla_step",
                                "sibling_cap",
                                &format!("{{\"cap\":{MAX_STEP_SIBLINGS}}}"),
                            );
                            // #endregion
                        }
                        return;
                    }
                    let all = solver.trace().to_vec();
                    let new_count = all.len().saturating_sub(parent_len);
                    // #region agent log
                    let step_n = STEP_COUNT.load(Ordering::SeqCst);
                    if step_n < 8 || new_count > 200 || all.len() > 2000 || bag.len() > 2 {
                        agent_log(
                            "B",
                            "symexec.rs:isla_step",
                            "trace_sizes",
                            &format!(
                                "{{\"parent_len\":{parent_len},\"new_count\":{new_count},\"total\":{},\"results_so_far\":{}}}",
                                all.len(),
                                bag.len()
                            ),
                        );
                    }
                    // #endregion
                    let mut events: Vec<Event<B129>> =
                        all.into_iter().take(new_count).cloned().collect();
                    events.reverse();
                    // Keep effects after the last Cycle (skip zinit / reset noise).
                    if let Some(i) = events.iter().rposition(|e| matches!(e, Event::Cycle)) {
                        events = events.split_off(i + 1);
                    }

                    let mut fork_branches = Vec::new();
                    for ev in &events {
                        if let Event::Fork(_, _, branch, _) = ev {
                            fork_branches.push(*branch as u8);
                        }
                    }

                    let mut regs = HashMap::new();
                    for name in gpr_names.iter().copied().chain(std::iter::once(pc_name)) {
                        if let Some(v) = frame.regs().get_last_if_initialized(name) {
                            regs.insert(name, v.clone());
                        }
                    }
                    for (name, old) in &prev_regs {
                        regs.entry(*name).or_insert_with(|| old.clone());
                    }
                    for (name, reg) in frame.regs().iter() {
                        if let Some(v) = reg.read_last_if_initialized() {
                            regs.entry(*name).or_insert_with(|| v.clone());
                        }
                    }

                    let checkpoint = smt::checkpoint(&mut solver);
                    bag.push(RawStep {
                        regs,
                        memory: frame.memory().clone(),
                        checkpoint,
                        events,
                        fork_branches,
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

fn apply_step(
    mut snap: PathSnap,
    mut raw: RawStep,
    shared: &SharedCtx,
    sibling_index: u8,
    sibling_count: usize,
) -> Result<PathSnap> {
    let arch = shared.arch;
    let pc_before = snap
        .regs
        .get(&arch.pc_name)
        .and_then(concrete_u32)
        .ok_or_else(|| anyhow!("PC concrete required to index step"))?;
    let offset = pc_before.wrapping_sub(shared.image_base) as usize;
    let insn_index = *shared.offset_to_index.get(&offset).unwrap();
    let insn_len = shared.insns[insn_index].bytes.len() as u32;

    // isla_footprint* does not run the fetch loop — advance PC ourselves unless
    // the step already wrote PC or announced a branch target.
    let next_pc_val = resolve_next_pc(&raw.events, pc_before, insn_len, arch);
    raw.regs.insert(arch.pc_name, next_pc_val);

    // Extend tree key only at real forks (taken-first / sibling order).
    if !raw.fork_branches.is_empty() {
        snap.tree_key.extend(raw.fork_branches.iter().copied());
    } else if sibling_count > 1 {
        snap.tree_key.push(sibling_index);
    }

    // Fold SMT definitions into sym_names for pretty printing.
    for ev in &raw.events {
        if let Event::Smt(Def::DefineConst(sym, exp), _, _) = ev {
            let pretty = format_exp(exp, &snap.sym_names);
            snap.sym_names.insert(*sym, pretty);
        }
    }

    let mut lines = Vec::new();
    for ev in &raw.events {
        match ev {
            Event::ReadReg(name, _, val) => {
                if let Some(reg) = data_reg_name(name, shared_state_symtab(shared)) {
                    lines.push(format!(
                        "read-reg {reg} {}",
                        format_val(val, &snap.sym_names)
                    ));
                }
            }
            Event::WriteReg(name, _, val) => {
                if let Some(reg) = data_reg_name(name, shared_state_symtab(shared)) {
                    let expr = format_val(val, &snap.sym_names);
                    lines.push(format!("write-reg {reg} {expr}"));
                    if reg != "x0" && reg != "PC" {
                        snap.state_regs.insert(reg, expr);
                    }
                }
            }
            Event::ReadMem {
                value,
                address,
                bytes,
                ..
            } => {
                lines.push(format!(
                    "read-mem {} {} {bytes}",
                    format_val(address, &snap.sym_names),
                    format_val(value, &snap.sym_names),
                ));
            }
            Event::WriteMem {
                address,
                data,
                bytes,
                ..
            } => {
                let addr = format_val(address, &snap.sym_names);
                let data_s = format_val(data, &snap.sym_names);
                lines.push(format!("write-mem {addr} {data_s} {bytes}"));
                snap.state_mem.insert(addr, data_s);
            }
            Event::Smt(Def::Assert(exp), _, _) => {
                let text = format_exp(exp, &snap.sym_names);
                // Drop model-internal asserts that did not pretty-print.
                if text.contains("Bits([") || text.contains("Sym {") {
                    continue;
                }
                lines.push(format!("assert {text}"));
            }
            _ => {}
        }
    }

    let mut state_lines = Vec::new();
    for (k, v) in &snap.state_regs {
        state_lines.push(format!("{k} = {v}"));
    }
    for (k, v) in &snap.state_mem {
        state_lines.push(format!("mem[{k}] = {v}"));
    }

    snap.steps.push(StepRecord {
        insn_index,
        lines,
        state_lines,
    });
    snap.regs = raw.regs;
    snap.memory = raw.memory;
    // Concrete store → update the zero slab so later loads see the bytes
    // (Isla Concrete regions do not auto-forward WriteMem events).
    for ev in &raw.events {
        if let Event::WriteMem {
            address,
            data,
            bytes,
            ..
        } = ev
        {
            if let (Some(a), Some(v)) = (concrete_u64(address), concrete_u64(data)) {
                for i in 0..*bytes as u64 {
                    let b = ((v >> (8 * i)) & 0xff) as u8;
                    snap.memory.write_byte(a + i, b);
                }
            }
        }
    }
    snap.checkpoint = raw.checkpoint;
    snap.path_len += 1;
    Ok(snap)
}

fn resolve_next_pc(
    events: &[Event<B129>],
    pc_before: u32,
    insn_len: u32,
    arch: &ArchStatic,
) -> Val<B129> {
    let mut wrote_pc: Option<Val<B129>> = None;
    let mut branch: Option<Val<B129>> = None;
    for ev in events {
        match ev {
            Event::WriteReg(name, _, val) if *name == arch.pc_name => {
                wrote_pc = Some(val.clone());
            }
            Event::Branch { address } => {
                branch = Some(address.clone());
            }
            _ => {}
        }
    }
    // Prefer an architectural PC write; else a branch announce; else fallthrough.
    if let Some(v) = wrote_pc {
        if concrete_u32(&v).map(|p| p != pc_before).unwrap_or(true) {
            return v;
        }
    }
    if let Some(v) = branch {
        return v;
    }
    Val::Bits(B129::from_u32(pc_before.wrapping_add(insn_len)))
}

fn shared_state_symtab(shared: &SharedCtx) -> &isla_lib::ir::Symtab<'static> {
    &shared.arch.iarch.shared_state.symtab
}

fn data_reg_name(name: &Name, symtab: &Symtab<'_>) -> Option<String> {
    let demangled = zencode::decode(symtab.to_str(*name));
    if demangled == "PC" {
        return Some("PC".into());
    }
    let rest = demangled.strip_prefix('x')?;
    if !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit()) {
        Some(demangled)
    } else {
        None
    }
}

fn concrete_u32(val: &Val<B129>) -> Option<u32> {
    match val {
        Val::Bits(b) if b.len() <= 32 => Some(b.lower_u64() as u32),
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

fn format_val(val: &Val<B129>, names: &HashMap<Sym, String>) -> String {
    match val {
        Val::Symbolic(s) => names
            .get(s)
            .cloned()
            .unwrap_or_else(|| format!("v{s}")),
        Val::Bits(b) => format_bits(b),
        Val::Bool(b) => b.to_string(),
        Val::I64(i) => i.to_string(),
        Val::I128(i) => i.to_string(),
        other => format!("{other:?}"),
    }
}

fn format_bits(b: &B129) -> String {
    let len = b.len();
    let v = b.lower_u64();
    if len <= 32 {
        format!("0x{v:08x}")
    } else {
        format!("0x{v:x}")
    }
}

fn format_exp(exp: &Exp<Sym>, names: &HashMap<Sym, String>) -> String {
    use Exp::*;
    match exp {
        Var(s) => names
            .get(s)
            .cloned()
            .unwrap_or_else(|| format!("v{s}")),
        Bits64(bv) => {
            let v = bv.lower_u64();
            if bv.len() <= 32 {
                format!("0x{v:08x}")
            } else {
                format!("0x{v:x}")
            }
        }
        Bits(bits) => {
            let mut v = 0u64;
            for (i, b) in bits.iter().enumerate().take(64) {
                if *b {
                    v |= 1 << i;
                }
            }
            format!("0x{v:x}")
        }
        Bool(b) => b.to_string(),
        Not(e) => format!("!({})", format_exp(e, names)),
        Eq(a, b) => format!("{} == {}", format_exp(a, names), format_exp(b, names)),
        Neq(a, b) => format!("{} != {}", format_exp(a, names), format_exp(b, names)),
        And(a, b) => format!("({} & {})", format_exp(a, names), format_exp(b, names)),
        Or(a, b) => format!("({} | {})", format_exp(a, names), format_exp(b, names)),
        Bvadd(a, b) => format_add_sub(a, b, names, false),
        Bvsub(a, b) => format_add_sub(a, b, names, true),
        Bvand(a, b) => format!("({} & {})", format_exp(a, names), format_exp(b, names)),
        Bvor(a, b) => format!("({} | {})", format_exp(a, names), format_exp(b, names)),
        Bvxor(a, b) => format!("({} ^ {})", format_exp(a, names), format_exp(b, names)),
        Ite(c, t, e) => format!(
            "ite({}, {}, {})",
            format_exp(c, names),
            format_exp(t, names),
            format_exp(e, names)
        ),
        Bvult(a, b) => format!("({} <u {})", format_exp(a, names), format_exp(b, names)),
        Bvule(a, b) => format!("({} <=u {})", format_exp(a, names), format_exp(b, names)),
        Bvslt(a, b) => format!("({} <s {})", format_exp(a, names), format_exp(b, names)),
        Bvsle(a, b) => format!("({} <=s {})", format_exp(a, names), format_exp(b, names)),
        Bvugt(a, b) => format!("({} >u {})", format_exp(a, names), format_exp(b, names)),
        Bvuge(a, b) => format!("({} >=u {})", format_exp(a, names), format_exp(b, names)),
        Bvsgt(a, b) => format!("({} >s {})", format_exp(a, names), format_exp(b, names)),
        Bvsge(a, b) => format!("({} >=s {})", format_exp(a, names), format_exp(b, names)),
        _ => format!("{exp:?}"),
    }
}

fn format_add_sub(a: &Exp<Sym>, b: &Exp<Sym>, names: &HashMap<Sym, String>, sub: bool) -> String {
    let left = format_exp(a, names);
    let right = format_exp(b, names);
    // Pretty `(sp0 - 48)` when RHS is a small concrete immediate.
    if let Some(imm) = concrete_exp_i64(b) {
        if sub {
            return format!("({left} - {imm})");
        }
        if imm < 0 {
            return format!("({left} - {})", -imm);
        }
        return format!("({left} + {imm})");
    }
    if sub {
        format!("({left} - {right})")
    } else {
        format!("({left} + {right})")
    }
}

fn concrete_exp_i64(exp: &Exp<Sym>) -> Option<i64> {
    match exp {
        Exp::Bits64(bv) => {
            let len = bv.len();
            let v = bv.lower_u64();
            if len == 0 {
                return Some(0);
            }
            let signed = if len < 64 && (v >> (len - 1)) & 1 == 1 {
                (v as i64) | (!0i64 << len)
            } else {
                v as i64
            };
            Some(signed)
        }
        _ => None,
    }
}

/// Format paths as the human-readable tree dump.
pub fn format_paths(paths: &[ExecPath]) -> String {
    let mut out = String::new();
    for (i, path) in paths.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        out.push_str(&format!("path {i}:\n\n"));
        for step in &path.steps {
            out.push_str(&format!("{}:\n", step.insn_index));
            for line in &step.lines {
                out.push_str(&format!("  {line}\n"));
            }
            out.push('\n');
            out.push_str("state:\n");
            for line in &step.state_lines {
                out.push_str(&format!("  {line}\n"));
            }
            out.push('\n');
        }
    }
    out
}

/// Write `trace.txt` (+ manifest) under `dir`, replacing the directory.
pub fn write_trace(dir: &std::path::Path, paths: &[ExecPath]) -> Result<()> {
    if dir.exists() {
        std::fs::remove_dir_all(dir)
            .with_context(|| format!("remove RV32 output directory {}", dir.display()))?;
    }
    std::fs::create_dir_all(dir)
        .with_context(|| format!("create RV32 output directory {}", dir.display()))?;
    std::fs::write(dir.join("trace.txt"), format_paths(paths))?;
    std::fs::write(
        dir.join("manifest.txt"),
        format!(
            "isa = rv32imc\nmode = symexec-tree\npaths = {}\n",
            paths.len()
        ),
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initial_names_abi() {
        assert_eq!(initial_gpr_name(0), "0");
        assert_eq!(initial_gpr_name(1), "ra0");
        assert_eq!(initial_gpr_name(2), "sp0");
        assert_eq!(initial_gpr_name(10), "a0");
        assert_eq!(initial_gpr_name(8), "s0");
    }

    #[test]
    fn format_paths_shape() {
        let paths = vec![ExecPath {
            tree_key: vec![0],
            steps: vec![StepRecord {
                insn_index: 0,
                lines: vec![
                    "read-reg x2 sp0".into(),
                    "write-reg x2 (sp0 - 48)".into(),
                ],
                state_lines: vec!["x2 = (sp0 - 48)".into()],
            }],
        }];
        let text = format_paths(&paths);
        assert!(text.contains("path 0:"));
        assert!(text.contains("0:"));
        assert!(text.contains("read-reg x2 sp0"));
        assert!(text.contains("state:"));
        assert!(text.contains("x2 = (sp0 - 48)"));
    }

    #[test]
    fn tree_key_sort_order() {
        let mut paths = vec![
            ExecPath {
                tree_key: vec![1, 0],
                steps: vec![],
            },
            ExecPath {
                tree_key: vec![0, 1],
                steps: vec![],
            },
            ExecPath {
                tree_key: vec![0, 0],
                steps: vec![],
            },
        ];
        paths.sort_by(|a, b| a.tree_key.cmp(&b.tree_key));
        assert_eq!(paths[0].tree_key, vec![0, 0]);
        assert_eq!(paths[1].tree_key, vec![0, 1]);
        assert_eq!(paths[2].tree_key, vec![1, 0]);
    }

    #[test]
    fn format_exp_sub() {
        let mut names = HashMap::new();
        names.insert(Sym::from_u32(1), "sp0".into());
        let exp = Exp::Bvsub(
            Box::new(Exp::Var(Sym::from_u32(1))),
            Box::new(smtlib::bits64(48, 32)),
        );
        assert_eq!(format_exp(&exp, &names), "(sp0 - 48)");
    }
}
