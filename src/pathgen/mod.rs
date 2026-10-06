//! Path generation (document T0): expand forward `IfGoto` into `Assert` paths.

mod expand;
mod offset;

use anyhow::{ensure, Result};

use crate::predicate::Insn;
use crate::rv32::Environment;

pub use expand::{expand, ExpandConfig, GotoPolicy};

/// Task directory name under `out/<arch>/`.
pub const TASK_PATHGEN: &str = "pathgen";

/// One syntax path with Huffman-style branch filename code.
///
/// `code` starts as `"0"`. Only a forward conditional appends a bit:
/// taken → `'1'`, fallthrough → `'0'`. File name is `{code}.txt`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Path {
    pub code: String,
    pub insns: Vec<Insn>,
}

impl Path {
    fn at_entry() -> Self {
        Self {
            code: String::from("0"),
            insns: Vec::new(),
        }
    }
}

/// BPF pathgen: entry at first instruction; backward `goto` does not follow target.
pub fn pathgen_bpf(insns: &[Insn]) -> Result<Vec<Path>> {
    expand(
        insns,
        ExpandConfig {
            entry_pos: 0,
            goto: GotoPolicy::Bpf,
            max_paths: 65536,
            max_path_len: 65536,
        },
    )
}

/// RV32IMC pathgen: `Environment.entry` + budgets; unconditional `goto` always follows.
pub fn pathgen_rv32(insns: &[Insn], env: &Environment) -> Result<Vec<Path>> {
    ensure!(!insns.is_empty(), "pathgen: empty program");
    let entry_pos = insns
        .iter()
        .position(|i| i.index as usize == env.entry)
        .ok_or_else(|| anyhow::anyhow!("pathgen: entry index {} not in program", env.entry))?;
    expand(
        insns,
        ExpandConfig {
            entry_pos,
            goto: GotoPolicy::Rv32,
            max_paths: env.max_paths,
            max_path_len: env.max_path_len,
        },
    )
}
