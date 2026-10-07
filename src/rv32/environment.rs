//! Explicit assumptions about the embedding runtime, not facts inferred from Isla.
use anyhow::{Context, Result, ensure};
use serde::Deserialize;
use std::collections::BTreeSet;

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Environment {
    #[serde(default)]
    pub entry: usize,
    #[serde(default)]
    pub image_base: u32,
    #[serde(default = "default_paths")]
    pub max_paths: usize,
    #[serde(default = "default_length")]
    pub max_path_len: usize,
    pub stack: Option<StackContract>,
    pub packet: Option<PacketContract>,
    #[serde(default)]
    pub calls: Vec<CallContract>,
    #[serde(default)]
    pub maps: Vec<MapContract>,
    pub return_values: Option<Vec<u32>>,
}
fn default_paths() -> usize {
    4096
}
fn default_length() -> usize {
    65536
}
impl Default for Environment {
    fn default() -> Self {
        Self {
            entry: 0,
            image_base: 0,
            max_paths: default_paths(),
            max_path_len: default_length(),
            stack: None,
            packet: None,
            calls: vec![],
            maps: vec![],
            return_values: None,
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StackContract {
    /// Minimum possible incoming S; S is assumed 16-byte aligned.
    pub top_min: u32,
    pub size: u32,
    /// Stack RAM is writable and disjoint from context, packet, and map storage.
    pub separated_ram: bool,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PacketContract {
    pub context_reg: u32,
    /// Runtime guarantees data <= data_end <= u32::MAX and data <= data_max.
    pub data_max: u32,
    pub alignment: u32,
    /// Context fields +0/+4 are readable u32 pointers; packet is separated RAM.
    pub separated_ram: bool,
    pub writable: bool,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
pub enum Helper {
    MapLookupElem,
    MapUpdateElem,
    MapDeleteElem,
    XdpAdjustTail,
    Scalar,
}
impl Helper {
    pub fn name(self) -> &'static str {
        match self {
            Self::MapLookupElem => "MapLookupElem",
            Self::MapUpdateElem => "MapUpdateElem",
            Self::MapDeleteElem => "MapDeleteElem",
            Self::XdpAdjustTail => "XdpAdjustTail",
            Self::Scalar => "Scalar",
        }
    }
    pub fn arg_count(self) -> usize {
        match self {
            Self::MapLookupElem | Self::MapDeleteElem | Self::XdpAdjustTail => 2,
            Self::MapUpdateElem => 4,
            Self::Scalar => 0,
        }
    }
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Selector {
    pub reg: u32,
    pub value: u32,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallContract {
    pub index: usize,
    /// Absolute target, checked against decoded control flow (including image_base).
    pub target: u32,
    pub helper: Helper,
    pub arg_regs: Vec<u32>,
    pub selector: Option<Selector>,
    pub result_bits: u32,
    pub returns_normally: bool,
    /// Current domain only supports calls that never write the caller's frame.
    pub preserves_stack: bool,
    /// Must be false for AdjustTail, true for other supported contracts.
    pub preserves_packet: bool,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MapContract {
    pub handle: u32,
    pub id: u32,
    pub key_size: u32,
    pub value_size: u32,
    pub value_alignment: u32,
    pub value_base_max: u32,
    /// Non-null values are valid separated RAM until a modeled invalidation.
    pub separated_ram: bool,
    pub writable: bool,
}

impl Environment {
    pub fn from_toml(text: &str) -> Result<Self> {
        let env: Self = toml::from_str(text).context("parse RV32 environment")?;
        env.validate()?;
        Ok(env)
    }

    pub fn load(path: &std::path::Path) -> Result<Self> {
        let text = std::fs::read_to_string(path)
            .with_context(|| format!("read environment {}", path.display()))?;
        Self::from_toml(&text)
    }

    pub fn validate(&self) -> Result<()> {
        ensure!(
            self.image_base % 2 == 0,
            "image_base must be 2-byte aligned"
        );
        ensure!(
            self.max_paths > 0 && self.max_path_len > 0,
            "path budgets must be positive"
        );
        if let Some(s) = &self.stack {
            ensure!(
                s.separated_ram && s.size > 0 && s.size % 16 == 0 && s.top_min >= s.size,
                "invalid stack RAM/range contract"
            );
        }
        if let Some(p) = &self.packet {
            ensure!(
                p.context_reg > 0 && p.context_reg < 32 && ![1, 2, 3, 4].contains(&p.context_reg),
                "invalid context register"
            );
            ensure!(
                p.separated_ram && p.alignment.is_power_of_two(),
                "invalid packet RAM/alignment contract"
            );
        }
        let mut sites = BTreeSet::new();
        for c in &self.calls {
            ensure!(
                sites.insert(c.index),
                "duplicate call contract at {}",
                c.index
            );
            ensure!(
                c.target % 2 == 0 && c.result_bits == 32 && c.returns_normally && c.preserves_stack,
                "call {} requires aligned target, normal u32 return and preserved caller frame",
                c.index
            );
            ensure!(
                c.preserves_packet == (c.helper != Helper::XdpAdjustTail),
                "call {} has incompatible packet effect",
                c.index
            );
            ensure!(
                c.arg_regs.len() == c.helper.arg_count()
                    && c.arg_regs.iter().all(|r| (10..=17).contains(r)),
                "call {} has unsupported argument layout",
                c.index
            );
            if let Some(s) = &c.selector {
                ensure!(
                    (10..=17).contains(&s.reg),
                    "invalid dispatcher selector register"
                );
            }
        }
        let (mut handles, mut ids) = (BTreeSet::new(), BTreeSet::new());
        for m in &self.maps {
            ensure!(
                handles.insert(m.handle) && ids.insert(m.id),
                "duplicate map handle or id"
            );
            ensure!(
                m.separated_ram
                    && m.key_size > 0
                    && m.key_size % 4 == 0
                    && m.value_size > 0
                    && m.value_size % 4 == 0,
                "unsupported map object sizes/RAM contract"
            );
            ensure!(
                m.value_alignment.is_power_of_two()
                    && m.value_base_max.checked_add(m.value_size).is_some(),
                "invalid map address range/alignment"
            );
        }
        Ok(())
    }
    pub(crate) fn call(&self, index: usize) -> Result<&CallContract> {
        self.calls
            .iter()
            .find(|c| c.index == index)
            .with_context(|| format!("missing call contract at index {index}"))
    }
    pub(crate) fn map(&self, handle: u32) -> Result<&MapContract> {
        self.maps
            .iter()
            .find(|m| m.handle == handle)
            .with_context(|| format!("unknown map handle {handle:#x}"))
    }
}
