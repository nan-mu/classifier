//! Runtime contract for RV32IMC lower / prefixgen / pathgen.
//!
//! Values come from an explicit TOML file (see `config/esp32c3.environment.toml`).
//! They are assumptions about the firmware ABI, not facts proved from the binary.

use anyhow::{ensure, Context, Result};
use serde::Deserialize;
use std::path::Path;

/// Full environment contract used by lower and path budgets.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Environment {
    pub entry: usize,
    pub image_base: u32,
    #[serde(default = "default_paths")]
    pub max_paths: usize,
    #[serde(default = "default_length")]
    pub max_path_len: usize,
    /// Max revisits to a loop-header instruction with a different arch state
    /// (BPF `BPF_COMPLEXITY_LIMIT_INSNS` = 1_000_000). Unused by prefixgen/pathgen.
    #[serde(default = "default_loop_depth")]
    pub max_loop_depth: usize,
    #[serde(default)]
    pub stack: Option<StackContract>,
    #[serde(default)]
    pub packet: Option<PacketContract>,
    #[serde(default)]
    pub calls: Vec<CallContract>,
    #[serde(default)]
    pub maps: Vec<MapContract>,
    #[serde(default)]
    pub return_values: Option<Vec<u32>>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StackContract {
    pub top_min: u32,
    pub size: u32,
    #[serde(default)]
    pub separated_ram: bool,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PacketContract {
    pub context_reg: u8,
    pub data_max: u32,
    #[serde(default)]
    pub alignment: u32,
    #[serde(default)]
    pub separated_ram: bool,
    #[serde(default)]
    pub writable: bool,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallContract {
    pub index: usize,
    pub target: u32,
    pub helper: Helper,
    #[serde(default)]
    pub arg_regs: Vec<u8>,
    #[serde(default)]
    pub result_bits: u8,
    #[serde(default = "default_true")]
    pub returns_normally: bool,
    #[serde(default = "default_true")]
    pub preserves_stack: bool,
    #[serde(default = "default_true")]
    pub preserves_packet: bool,
    #[serde(default)]
    pub selector: Option<Selector>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MapContract {
    pub handle: u32,
    pub id: u32,
    pub key_size: u32,
    pub value_size: u32,
    #[serde(default)]
    pub value_alignment: u32,
    #[serde(default)]
    pub value_base_max: u32,
    #[serde(default)]
    pub separated_ram: bool,
    #[serde(default)]
    pub writable: bool,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Selector {
    pub reg: u8,
    pub value: u32,
}

/// Named helper at a contract call site (string form in TOML).
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "PascalCase")]
pub enum Helper {
    MapLookupElem,
    MapUpdateElem,
    MapDeleteElem,
    #[serde(other)]
    Other,
}

fn default_paths() -> usize {
    4096
}
fn default_length() -> usize {
    65536
}
fn default_loop_depth() -> usize {
    1_000_000
}
fn default_true() -> bool {
    true
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            entry: 0,
            image_base: 0,
            max_paths: default_paths(),
            max_path_len: default_length(),
            max_loop_depth: default_loop_depth(),
            stack: None,
            packet: None,
            calls: vec![],
            maps: vec![],
            return_values: None,
        }
    }
}

impl Environment {
    pub fn from_toml(text: &str) -> Result<Self> {
        let env: Self = toml::from_str(text).context("parse Environment TOML")?;
        env.validate()?;
        Ok(env)
    }

    pub fn load(path: &Path) -> Result<Self> {
        let text = std::fs::read_to_string(path)
            .with_context(|| format!("read environment {}", path.display()))?;
        Self::from_toml(&text)
    }

    pub fn validate(&self) -> Result<()> {
        ensure!(
            self.max_paths > 0 && self.max_path_len > 0 && self.max_loop_depth > 0,
            "path / loop budgets must be positive"
        );
        if let Some(stack) = &self.stack {
            ensure!(stack.size > 0, "stack.size must be positive");
        }
        if let Some(packet) = &self.packet {
            ensure!(packet.context_reg < 32, "packet.context_reg must be a GPR");
            ensure!(packet.data_max > 0, "packet.data_max must be positive");
        }
        let mut seen = std::collections::BTreeSet::new();
        for c in &self.calls {
            ensure!(seen.insert(c.index), "duplicate call contract at index {}", c.index);
            ensure!(c.result_bits == 0 || c.result_bits == 32 || c.result_bits == 64,
                "call {} result_bits must be 0, 32, or 64", c.index);
            for r in &c.arg_regs {
                ensure!(*r < 32, "call {} arg_reg out of range", c.index);
            }
            if let Some(sel) = c.selector {
                ensure!(sel.reg < 32, "call {} selector.reg out of range", c.index);
            }
        }
        Ok(())
    }

    pub fn call(&self, index: usize) -> Result<&CallContract> {
        self.calls
            .iter()
            .find(|c| c.index == index)
            .ok_or_else(|| anyhow::anyhow!("no call contract for instruction index {index}"))
    }
}
