//! Offline string pipeline (T-1 → T0 → T1–T5) locked by fixture tests.
//! Not used by `rv32-classify`; kept for `classify_to` / `rv32-footprint` consumers.

mod model;
mod state;
mod t0;
mod t1;
mod t2;
mod t3;
mod t4;
mod t5;
mod t_minus1;

use anyhow::{Context, Result};
use std::fmt;
use std::path::Path;

use super::environment::Environment;
use super::footprint::InsnFootprint;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Stage {
    TMinus1,
    T0,
    T1,
    T2,
    T3,
    T4,
    T5,
}
impl Stage {
    pub fn parse(s: &str) -> Result<Self> {
        Ok(match s.to_ascii_lowercase().as_str() {
            "t-1" | "tm1" => Self::TMinus1,
            "t0" => Self::T0,
            "t1" => Self::T1,
            "t2" => Self::T2,
            "t3" => Self::T3,
            "t4" => Self::T4,
            "t5" => Self::T5,
            _ => anyhow::bail!("unknown RV32 stage {s}; expected t-1 or t0..t5"),
        })
    }
}
impl fmt::Display for Stage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::TMinus1 => "t-1",
            Self::T0 => "t0",
            Self::T1 => "t1",
            Self::T2 => "t2",
            Self::T3 => "t3",
            Self::T4 => "t4",
            Self::T5 => "t5",
        })
    }
}

/// Canonical finite output model for fixed footprints, environment and stage.
#[derive(Debug)]
pub struct OutputModel {
    stage: Stage,
    paths: Vec<Vec<String>>,
}
impl OutputModel {
    pub fn stage(&self) -> Stage {
        self.stage
    }
    pub fn paths(&self) -> &[Vec<String>] {
        &self.paths
    }
    pub fn accepts(&self, path: &[String]) -> bool {
        self.paths.iter().any(|p| p == path)
    }
    pub fn accepts_family(&self, paths: &[Vec<String>]) -> bool {
        self.paths == paths
    }
}

pub fn classify(input: &[InsnFootprint], env: &Environment) -> Result<Vec<Vec<String>>> {
    Ok(classify_to(input, env, Stage::T5)?.paths)
}

pub fn classify_to(
    input: &[InsnFootprint],
    env: &Environment,
    stage: Stage,
) -> Result<OutputModel> {
    let table = t_minus1::run(input, env)?;
    if stage == Stage::TMinus1 {
        return Ok(OutputModel {
            stage,
            paths: vec![table.iter().map(model::Line::text).collect()],
        });
    }
    let mut paths = t0::run(&table, env)?;
    type Transform = fn(&mut [model::Line], &Environment) -> Result<()>;
    let stages: [(Stage, Transform); 5] = [
        (Stage::T1, t1::run),
        (Stage::T2, t2::run),
        (Stage::T3, t3::run),
        (Stage::T4, t4::run),
        (Stage::T5, t5::run),
    ];
    for (current, transform) in stages {
        if current > stage {
            break;
        }
        for (i, path) in paths.iter_mut().enumerate() {
            transform(path, env).with_context(|| format!("RV32 {current} path {i}"))?;
        }
    }
    Ok(OutputModel {
        stage,
        paths: paths
            .iter()
            .map(|p| p.iter().map(model::Line::text).collect())
            .collect(),
    })
}

pub fn write_classification(dir: &Path, model: &OutputModel) -> Result<()> {
    if dir.exists() {
        std::fs::remove_dir_all(dir)
            .with_context(|| format!("remove RV32 output directory {}", dir.display()))?;
    }
    std::fs::create_dir_all(dir)
        .with_context(|| format!("create RV32 output directory {}", dir.display()))?;
    for (i, path) in model.paths.iter().enumerate() {
        std::fs::write(
            dir.join(format!("{i:04}.txt")),
            format!("{}\n", path.join("\n")),
        )?;
    }
    std::fs::write(
        dir.join("manifest.txt"),
        format!(
            "isa = rv32imc\nstage = {}\npaths = {}\ncontracts = caller-supplied\n",
            model.stage,
            model.paths.len()
        ),
    )?;
    Ok(())
}
