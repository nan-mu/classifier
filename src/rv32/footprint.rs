#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_mixed_c_and_32() {
        // c.addi sp,-16 (4111) then addi a0,a0,3 as LE bytes 13 05 35 00
        let bin = [0x41, 0x11, 0x13, 0x05, 0x35, 0x00];
        let insns = decode_rv32imc(&bin).unwrap();
        assert_eq!(insns.len(), 2);
        assert_eq!(insns[0].hex, "4111");
        assert_eq!(insns[0].offset, 0);
        assert_eq!(insns[1].hex, "13053500");
        assert_eq!(insns[1].offset, 2);
        #[test]
    fn collapse_strips_trace_wrapper() {
        let s = collapse_trace_line(
            "(trace\n  (read-reg |x10| nil v1)\n  (write-reg |x10| nil v2))\n",
        );
        assert_eq!(s, "(read-reg |x10| nil v1) (write-reg |x10| nil v2)");
    }
}

    #[test]
    fn decode_stops_before_gpl() {
        let mut bin = vec![0x82, 0x80]; // c.jr ra
        bin.extend_from_slice(b"GPL\0trailer");
        let insns = decode_rv32imc(&bin).unwrap();
        assert_eq!(insns.len(), 1);
        assert_eq!(insns[0].hex, "8280");
    }

    #[test]
    fn decode_esp32c3_bin_smoke() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("esp32c3.bin");
        if !path.exists() {
            return;
        }
        let bin = fs::read(&path).unwrap();
        let insns = decode_rv32imc(&bin).unwrap();
        assert!(!insns.is_empty());
        assert!(insns.iter().all(|i| i.bytes.len() == 2 || i.bytes.len() == 4));
        // Offsets must be strictly increasing by insn length.
        let mut expected = 0usize;
        for i in &insns {
            assert_eq!(i.offset, expected);
            expected += i.bytes.len();
        }
    }

    #[test]
    fn collapse_strips_trace_wrapper() {
        let s = collapse_trace_line(
            "(trace\n  (read-reg |x10| nil v1)\n  (write-reg |x10| nil v2))\n",
        );
        assert_eq!(s, "(read-reg |x10| nil v1) (write-reg |x10| nil v2)");
    }
}
//! Hex / raw-bin footprint via `isla-lib` (same core path as `isla-footprint -x`).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr;
use std::sync::Arc;

use anyhow::{anyhow, bail, Context, Result};
use crossbeam::queue::SegQueue;
use isla_lib::bitvector::b129::B129;
use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::executor::{self, LocalFrame, TaskId, TaskState};
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::{AssertionMode, IRTypeInfo, Name, SharedState, Symtab, Val};
use isla_lib::ir_lexer::new_ir_lexer;
use isla_lib::ir_parser;
use isla_lib::memory::Memory;
use isla_lib::simplify::{self, WriteOpts};
use isla_lib::smt::{self, Event};
use isla_lib::zencode;

use super::instruction::{decode_rv32imc, DecodedInsn};

/// Options for hex / bin footprint runs.
#[derive(Debug, Clone)]
pub struct FootprintOpts {
    pub arch_ir: PathBuf,
    pub config: PathBuf,
    pub simplify: bool,
    /// Drop init/enum noise; keep post-cycle data-plane effects (default).
    pub summary: bool,
    pub timeout: Option<u64>,
    pub little_endian: bool,
    pub threads: usize,
}

impl Default for FootprintOpts {
    fn default() -> Self {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        Self {
            arch_ir: root.join("config/rv32d.ir"),
            config: root.join("config/riscv32.toml"),
            simplify: true,
            summary: true,
            timeout: Some(60),
            little_endian: true,
            threads: std::thread::available_parallelism()
                .map(usize::from)
                .unwrap_or(1),
        }
    }
}

/// Result of footprinting one decoded insn (errors are captured for batch runs).
#[derive(Debug, Clone)]
pub struct InsnFootprint {
    pub insn: DecodedInsn,
    pub trace: Result<String, String>,
}

/// Ensure `riscv32-elf-{as,objdump,ld,nm}` exist on `PATH` so `ISAConfig` parses.
/// Missing tools get disposable temp-dir stubs (exit 1); never written into the repo.
pub fn ensure_riscv32_toolchain_stubs() -> Result<()> {
    const TOOLS: &[&str] = &[
        "riscv32-elf-as",
        "riscv32-elf-objdump",
        "riscv32-elf-ld",
        "riscv32-elf-nm",
    ];

    let missing: Vec<&str> = TOOLS
        .iter()
        .copied()
        .filter(|t| !tool_on_path(t))
        .collect();
    if missing.is_empty() {
        return Ok(());
    }

    let dir = std::env::temp_dir().join("classifier-isla-riscv32-stubs");
    fs::create_dir_all(&dir).with_context(|| format!("create stub dir {}", dir.display()))?;
    for name in &missing {
        let path = dir.join(name);
        if !path.exists() {
            fs::write(&path, "#!/bin/sh\nexit 1\n")
                .with_context(|| format!("write stub {}", path.display()))?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                fs::set_permissions(&path, fs::Permissions::from_mode(0o755))?;
            }
        }
    }

    let mut prefixed = dir.into_os_string();
    prefixed.push(":");
    prefixed.push(std::env::var_os("PATH").unwrap_or_default());
    // PATH is process-local; required so ISAConfig can resolve toolchain names.
    unsafe {
        std::env::set_var("PATH", prefixed);
    }
    Ok(())
}

fn tool_on_path(name: &str) -> bool {
    Command::new("which")
        .arg(name)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Stock `isla_footprint_no_init` calls `execute` once. Compressed (and some
/// other) clauses return `ExecuteAs(ast')`; `step.sail` re-executes once, but
/// footprint did not — C footprints were empty. Apply the same single unwrap.
///
/// Also forces `hartSupports(Ext_A) = false` so the model matches RV32IMC
/// (I+M+C, no A). Idempotent if the snapshot was already patched.
pub(crate) fn patch_rv32imc_ir(ir: &str) -> String {
    let ir = patch_footprint_execute_as(ir);
    patch_hart_supports_no_a(&ir)
}

fn patch_hart_supports_no_a(ir: &str) -> String {
    const MARKER: &str = "  jump @neq(zExt_A, zmergez3var) goto 7 `28 41:29-41:34;\n  zz40 = true `28 41:38-41:67;\n  goto 705;";
    const REPL: &str = "  jump @neq(zExt_A, zmergez3var) goto 7 `28 41:29-41:34;\n  zz40 = false `28 41:38-41:67;\n  goto 705;";
    if ir.contains(REPL) || !ir.contains(MARKER) {
        return ir.to_string();
    }
    ir.replacen(MARKER, REPL, 1)
}

/// Idempotent: no-op if the snapshot was already patched.
fn patch_footprint_execute_as(ir: &str) -> String {
    if ir.contains("jump zz411 is zExecuteAs goto 43") {
        return ir.to_string();
    }
    const MARKER: &str = "  zz411 = zexecute(zz43) `153 43:12-43:26;\n  jump have_exception goto 34 `153 43:12-43:26;\n  goto 35;\n  goto 38;\n  zz412 : %bool `153 43:4-44:8;";
    const REPL: &str = "  zz411 = zexecute(zz43) `153 43:12-43:26;\n  jump have_exception goto 34 `153 43:12-43:26;\n  goto 35;\n  goto 49;\n  zz413 : %union zExecutionResult;\n  jump zz411 is zExecuteAs goto 43;\n  zz414 : %union zinstruction;\n  zz414 = zz411 as zExecuteAs;\n  zz413 = zexecute(zz414);\n  jump have_exception goto 42;\n  goto 46;\n  goto 49;\n  zz415 : %union zExecutionResult;\n  zz415 = zz411;\n  zz413 = zz415;\n  zz412 : %bool `153 43:4-44:8;";
    if !ir.contains(MARKER) {
        return ir.to_string();
    }
    ir.replace(MARKER, REPL)
        .replace(
            "  jump have_exception goto 22 `153 41:6-41:24;\n  goto 23;\n  goto 38;\n  goto 30;",
            "  jump have_exception goto 22 `153 41:6-41:24;\n  goto 23;\n  goto 49;\n  goto 30;",
        )
        .replace(
            "  jump have_exception goto 29 `153 39:6-39:35;\n  goto 30;\n  goto 38;",
            "  jump have_exception goto 29 `153 39:6-39:35;\n  goto 30;\n  goto 49;",
        )
        .replace(
            "  jump @not(have_exception) goto 41 `153 34:2-47:3;",
            "  jump @not(have_exception) goto 52 `153 34:2-47:3;",
        )
}

fn hex_bytes(s: &str) -> Result<Vec<u8>> {
    let s = s.trim();
    if s.len() % 2 != 0 {
        bail!("hex opcode length must be even, got {} chars", s.len());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&s[i..i + 2], 16)
                .with_context(|| format!("invalid hex at index {i}"))
        })
        .collect()
}

pub(crate) fn opcode_bytes(opcode: Vec<u8>, little_endian: bool) -> Result<B129> {
    if opcode.len() > 8 {
        bail!("instructions longer than 8 bytes are not supported");
    }
    Ok(if opcode.len() == 2 {
        let arr: [u8; 2] = opcode.as_slice().try_into()?;
        B129::from_u16(if little_endian {
            u16::from_le_bytes(arr)
        } else {
            u16::from_be_bytes(arr)
        })
    } else if opcode.len() == 4 {
        let arr: [u8; 4] = opcode.as_slice().try_into()?;
        B129::from_u32(if little_endian {
            u32::from_le_bytes(arr)
        } else {
            u32::from_be_bytes(arr)
        })
    } else {
        B129::from_bytes(&opcode)
    })
}

/// GPRs / PC only — drop CSR / decode-probe reads in summary mode.
fn is_data_reg(demangled: &str) -> bool {
    if demangled == "PC" {
        return true;
    }
    let Some(rest) = demangled.strip_prefix('x') else {
        return false;
    };
    !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
}

fn summarize_events(events: Vec<Event<B129>>, shared_state: &SharedState<'_, B129>) -> Vec<Event<B129>> {
    let mut past_cycle = false;
    let mut out = Vec::new();
    for ev in events {
        match &ev {
            Event::Cycle => {
                past_cycle = true;
                continue;
            }
            _ if !past_cycle => continue,
            Event::AssumeReg(..)
            | Event::Assume(_)
            | Event::AssumeFun { .. }
            | Event::UseFunAssumption { .. }
            | Event::Function { .. }
            | Event::Smt(..) => continue,
            Event::ReadReg(name, _, _) | Event::WriteReg(name, _, _) => {
                let demangled = zencode::decode(shared_state.symtab.to_str(*name));
                if is_data_reg(&demangled) {
                    out.push(ev);
                }
            }
            Event::ReadMem { .. }
            | Event::WriteMem { .. }
            | Event::Branch { .. }
            | Event::AddressAnnounce { .. }
            | Event::Instr(_)
            | Event::MarkReg { .. } => out.push(ev),
            Event::Fork(..) | Event::Abstract { .. } => continue,
        }
    }
    out
}

fn events_to_trace_string(
    events: &[Event<B129>],
    shared_state: &SharedState<'_, B129>,
    opts: &FootprintOpts,
) -> Result<String> {
    let write_opts = WriteOpts {
        define_enum: !opts.simplify && !opts.summary,
        locations: !opts.summary,
        ..WriteOpts::default()
    };
    let mut out = Vec::new();
    simplify::write_events_with_opts(&mut out, events, shared_state, &write_opts)
        .map_err(|e| anyhow!("write events: {e}"))?;
    let text = String::from_utf8(out).context("footprint trace is not valid UTF-8")?;
    if opts.summary {
        Ok(collapse_trace_line(&text))
    } else {
        Ok(text)
    }
}

/// Flatten a multi-line `(trace …)` blob into one whitespace-collapsed line.
fn collapse_trace_line(text: &str) -> String {
    let flat: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    // Strip outer `(trace …)` wrapper when present so the indexed line stays short.
    let flat = flat.trim();
    if let Some(rest) = flat.strip_prefix("(trace") {
        let rest = rest.trim_start();
        if let Some(inner) = rest.strip_suffix(')') {
            return inner.trim().to_string();
        }
    }
    flat.to_string()
}

fn run_footprint_on_val(
    opcode_val: Val<B129>,
    opts: &FootprintOpts,
    iarch: &Initialized<'_, B129>,
) -> Result<String> {
    let regs = &iarch.regs;
    let lets = &iarch.lets;
    let shared_state = &iarch.shared_state;

    let memory = Memory::new();
    let memory_checkpoint = smt::Checkpoint::new();

    let (initial_checkpoint, opcode_val) = {
        let solver_cfg = smt::Config::new();
        let solver_ctx = smt::Context::new(solver_cfg);
        let mut solver = smt::Solver::from_checkpoint(&solver_ctx, memory_checkpoint);
        let mut sorted_regs: Vec<(&Name, _)> = regs.iter().collect();
        sorted_regs.sort_by_key(|(name, _)| *name);
        for (name, reg) in sorted_regs {
            if let Some(value) = reg.read_last_if_initialized() {
                solver.add_event(Event::AssumeReg(*name, vec![], value.clone()));
            }
        }
        (smt::checkpoint(&mut solver), opcode_val)
    };

    let footprint_function = zencode::encode("isla_footprint");
    let function_id = shared_state
        .symtab
        .get(&footprint_function)
        .ok_or_else(|| anyhow!("function isla_footprint not found in IR"))?;
    let (args, ret_ty, instrs) = shared_state
        .functions
        .get(&function_id)
        .ok_or_else(|| anyhow!("isla_footprint body missing"))?;

    let task_state = TaskState::new();
    let mut frame = LocalFrame::new(function_id, args, ret_ty, Some(&[opcode_val.clone()]), instrs);
    frame.add_lets(lets);
    frame.add_regs(regs);
    frame.set_memory(memory);
    let task = frame.task_with_checkpoint(TaskId::fresh(), &task_state, initial_checkpoint);

    let queue = Arc::new(SegQueue::new());
    executor::start_multi(
        opts.threads,
        opts.timeout,
        vec![task],
        shared_state,
        queue.clone(),
        &executor::trace_collector,
    );

    let mut saw_ok = false;
    let mut last_err: Option<String> = None;
    let mut traces = Vec::new();

    loop {
        match queue.pop() {
            Some(Ok((_, mut events))) => {
                if opts.simplify {
                    simplify::hide_initialization(&mut events);
                    simplify::remove_unused(&mut events);
                    simplify::propagate_forwards_used_once(&mut events);
                    simplify::commute_extract(&mut events);
                    simplify::eval(&mut events);
                }
                let mut events: Vec<Event<B129>> = events.drain(..).rev().collect();
                if opts.summary {
                    events = summarize_events(events, shared_state);
                }
                traces.push(events_to_trace_string(&events, shared_state, opts)?);
                saw_ok = true;
            }
            Some(Err(err)) => {
                last_err = Some(format!("{err}"));
            }
            None => break,
        }
    }

    if !saw_ok {
        bail!(
            "no successful footprint traces{}",
            last_err
                .map(|e| format!(" (last error: {e})"))
                .unwrap_or_default()
        );
    }
    Ok(pick_summary_line(traces, opts.summary))
}

fn pick_summary_line(traces: Vec<String>, summary: bool) -> String {
    if !summary || traces.len() <= 1 {
        return traces.join(" | ");
    }
    // Prefer a path that touched memory; otherwise first non-empty fork.
    traces
        .iter()
        .find(|t| t.contains("read-mem") || t.contains("write-mem"))
        .or_else(|| traces.iter().find(|t| !t.is_empty()))
        .cloned()
        .unwrap_or_default()
}

/// Run `isla_footprint` on one hex opcode; return SMT+effects text (optionally simplified).
pub fn footprint_hex(hex: &str, opts: &FootprintOpts) -> Result<String> {
    ensure_riscv32_toolchain_stubs()?;

    let ir_text = patch_rv32imc_ir(
        &fs::read_to_string(&opts.arch_ir)
            .with_context(|| format!("read architecture IR {}", opts.arch_ir.display()))?,
    );
    let config_text = fs::read_to_string(&opts.config)
        .with_context(|| format!("read config {}", opts.config.display()))?;

    let mut symtab = Symtab::new();
    let mut arch = ir_parser::IrParser::new()
        .parse(&mut symtab, new_ir_lexer(&ir_text))
        .map_err(|e| anyhow!("IR parse error: {e}"))?;
    let type_info = IRTypeInfo::new(&arch);

    let isa_config = ISAConfig::<B129>::parse(&config_text, None, &symtab, &type_info)
        .map_err(|e| anyhow!("{}: {e}", opts.config.display()))?;

    let iarch = initialize_architecture(
        &mut arch,
        symtab,
        type_info,
        &isa_config,
        AssertionMode::Optimistic,
        true,
    );

    let opcode_val = Val::Bits(opcode_bytes(hex_bytes(hex)?, opts.little_endian)?);
    let trace = run_footprint_on_val(opcode_val, opts, &iarch);

    unsafe {
        isla_lib::smt::finalize_solver();
    }

    trace
}

/// Footprint each hex opcode (reloads IR per opcode — prefer [`footprint_bin`] for images).
pub fn footprint_hex_batch(hexes: &[String], opts: &FootprintOpts) -> Result<Vec<String>> {
    hexes.iter().map(|h| footprint_hex(h, opts)).collect()
}

/// Decode a raw RV32IMC image and footprint every instruction (IR loaded once).
pub fn footprint_bin(bin: &[u8], opts: &FootprintOpts) -> Result<Vec<InsnFootprint>> {
    let insns = decode_rv32imc(bin)?;
    if insns.is_empty() {
        bail!("no instructions decoded from image ({} bytes)", bin.len());
    }

    ensure_riscv32_toolchain_stubs()?;

    let ir_text = patch_rv32imc_ir(
        &fs::read_to_string(&opts.arch_ir)
            .with_context(|| format!("read architecture IR {}", opts.arch_ir.display()))?,
    );
    let config_text = fs::read_to_string(&opts.config)
        .with_context(|| format!("read config {}", opts.config.display()))?;

    let mut symtab = Symtab::new();
    let mut arch = ir_parser::IrParser::new()
        .parse(&mut symtab, new_ir_lexer(&ir_text))
        .map_err(|e| anyhow!("IR parse error: {e}"))?;
    let type_info = IRTypeInfo::new(&arch);

    let isa_config = ISAConfig::<B129>::parse(&config_text, None, &symtab, &type_info)
        .map_err(|e| anyhow!("{}: {e}", opts.config.display()))?;

    let iarch = initialize_architecture(
        &mut arch,
        symtab,
        type_info,
        &isa_config,
        AssertionMode::Optimistic,
        true,
    );

    let total = insns.len();
    let mut results = Vec::with_capacity(total);
    for (i, insn) in insns.into_iter().enumerate() {
        eprintln!(
            "footprint [{}/{}] +{:#x} {} ({} B)",
            i + 1,
            total,
            insn.offset,
            insn.hex,
            insn.bytes.len()
        );
        let opcode_val = match opcode_bytes(insn.bytes.clone(), opts.little_endian) {
            Ok(bv) => Val::Bits(bv),
            Err(e) => {
                results.push(InsnFootprint {
                    insn,
                    trace: Err(e.to_string()),
                });
                continue;
            }
        };
        let trace = run_footprint_on_val(opcode_val, opts, &iarch).map_err(|e| e.to_string());
        results.push(InsnFootprint { insn, trace });
    }

    unsafe {
        isla_lib::smt::finalize_solver();
    }

    Ok(results)
}

/// Write all insn footprints into one file: `index: <one-line summary>` per line.
pub fn write_bin_footprints(out_path: &Path, results: &[InsnFootprint]) -> Result<()> {
    if let Some(parent) = out_path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)
                .with_context(|| format!("create {}", parent.display()))?;
        }
    }

    let mut ok = 0usize;
    let mut err = 0usize;
    let mut body = String::new();
    for (i, r) in results.iter().enumerate() {
        let line = match &r.trace {
            Ok(t) => {
                ok += 1;
                let t = t.trim();
                if t.is_empty() {
                    format!("{i}:")
                } else {
                    format!("{i}: {t}")
                }
            }
            Err(e) => {
                err += 1;
                // Keep ERROR on one line (no newlines in message).
                let e = e.replace(['\n', '\r'], " ");
                format!("{i}: ERROR {e}")
            }
        };
        body.push_str(&line);
        body.push('\n');
    }

    fs::write(out_path, &body).with_context(|| format!("write {}", out_path.display()))?;
    eprintln!(
        "wrote {} lines to {} (ok={ok} err={err})",
        results.len(),
        out_path.display()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_mixed_c_and_32() {
        // c.addi sp,-16 (4111) then addi a0,a0,3 as LE bytes 13 05 35 00
        let bin = [0x41, 0x11, 0x13, 0x05, 0x35, 0x00];
        let insns = decode_rv32imc(&bin).unwrap();
        assert_eq!(insns.len(), 2);
        assert_eq!(insns[0].hex, "4111");
        assert_eq!(insns[0].offset, 0);
        assert_eq!(insns[1].hex, "13053500");
        assert_eq!(insns[1].offset, 2);
    }

    #[test]
    fn decode_stops_before_gpl() {
        let mut bin = vec![0x82, 0x80]; // c.jr ra
        bin.extend_from_slice(b"GPL\0trailer");
        let insns = decode_rv32imc(&bin).unwrap();
        assert_eq!(insns.len(), 1);
        assert_eq!(insns[0].hex, "8280");
    }
}
