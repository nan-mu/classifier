//! BPF string pipeline T0–T5.

mod t0;
mod t1;
mod t2;
mod t3;
mod t4;
mod t5;
pub mod text;

use anyhow::Result;
use std::fmt;

pub use t0::t0;
pub use t1::t1;
pub use t2::t2;
pub use t3::t3;
pub use t4::t4;
pub use t5::t5;

/// Pipeline stop stage for CLI / tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Stage {
    T0,
    T1,
    T2,
    T3,
    T4,
    T5,
}

impl Stage {
    pub fn parse(s: &str) -> Result<Self> {
        Ok(match s {
            "t0" | "T0" => Self::T0,
            "t1" | "T1" => Self::T1,
            "t2" | "T2" => Self::T2,
            "t3" | "T3" => Self::T3,
            "t4" | "T4" => Self::T4,
            "t5" | "T5" => Self::T5,
            other => anyhow::bail!("unknown stage {other}; expected t0..t5"),
        })
    }
}

impl fmt::Display for Stage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::T0 => "t0",
            Self::T1 => "t1",
            Self::T2 => "t2",
            Self::T3 => "t3",
            Self::T4 => "t4",
            Self::T5 => "t5",
        })
    }
}

fn map_paths(paths: Vec<Vec<String>>, f: impl Fn(&[String]) -> Vec<String>) -> Vec<Vec<String>> {
    paths.into_iter().map(|p| f(&p)).collect()
}

/// Run the full BPF pipeline through T5.
pub fn classify(lines: &[String]) -> Result<Vec<Vec<String>>> {
    classify_to(lines, Stage::T5)
}

/// Run the BPF pipeline, stopping after `stage`.
pub fn classify_to(lines: &[String], stage: Stage) -> Result<Vec<Vec<String>>> {
    let mut paths = t0(lines)?;
    if stage == Stage::T0 {
        return Ok(paths);
    }
    paths = map_paths(paths, t1);
    if stage == Stage::T1 {
        return Ok(paths);
    }
    paths = map_paths(paths, t2);
    if stage == Stage::T2 {
        return Ok(paths);
    }
    paths = map_paths(paths, t3);
    if stage == Stage::T3 {
        return Ok(paths);
    }
    paths = map_paths(paths, t4);
    if stage == Stage::T4 {
        return Ok(paths);
    }
    Ok(map_paths(paths, t5))
}
