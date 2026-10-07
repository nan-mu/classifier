//! File-level driver for the standalone CoqQFBV executable.

pub mod ast;
pub mod family;
pub mod goal;
pub mod smtlib;
pub mod xdp;

use std::ffi::OsStr;
use std::fmt;
use std::path::Path;
use std::process::Command;

use anyhow::{Context, Result, bail};

pub use ast::{AstError, BoolExpr, BvBinaryOp, BvCmpOp, BvExpr, BvUnaryOp};
pub use family::{
    PathFamilyEvidence, PathFamilyMatching, PathPair, discover_path_family_matching_with,
    verify_path_family_matching_with, write_path_family_evidence,
};
pub use goal::{GoalError, PathFormula, compile_path_asserts, inequivalence_query};
pub use smtlib::QfbvQuery;
pub use xdp::{
    compile_xdp_assert_pair, compile_xdp_bpf_path_asserts, compile_xdp_rv32_path_asserts,
    xdp_environment_contract,
};

pub const DEFAULT_COQQFBV: &str = "coqQFBV.exe";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QfbvStatus {
    Sat,
    Unsat,
}

impl fmt::Display for QfbvStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sat => f.write_str("sat"),
            Self::Unsat => f.write_str("unsat"),
        }
    }
}

/// Run `coqQFBV.exe <query>` using the executable found on `PATH`.
pub fn check_qfbv_file(query: impl AsRef<Path>) -> Result<QfbvStatus> {
    check_qfbv_file_with(DEFAULT_COQQFBV, query, false)
}

/// Run a standalone CoqQFBV executable on one SMT-LIB2 QF_BV file.
///
/// Only an exact, unambiguous `sat` or `unsat` status line from a successful
/// process is accepted. Parser errors, failed certification, missing tools,
/// non-zero exits, and ambiguous output are returned as errors.
pub fn check_qfbv_file_with(
    executable: impl AsRef<OsStr>,
    query: impl AsRef<Path>,
    split_conjs: bool,
) -> Result<QfbvStatus> {
    let executable = executable.as_ref();
    let query = query.as_ref();
    if !query.is_file() {
        bail!("QF_BV query is not a file: {}", query.display());
    }

    let mut command = Command::new(executable);
    if split_conjs {
        command.arg("-split-conjs");
    }
    let output = command.arg(query).output().with_context(|| {
        format!(
            "run {} on {}",
            executable.to_string_lossy(),
            query.display()
        )
    })?;

    if !output.status.success() {
        bail!(
            "{} failed on {} with {}: {}",
            executable.to_string_lossy(),
            query.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }

    let stdout = String::from_utf8(output.stdout).context("CoqQFBV stdout is not UTF-8")?;
    parse_status(&stdout)
}

fn parse_status(stdout: &str) -> Result<QfbvStatus> {
    let mut status = None;
    for line in stdout.lines().map(str::trim) {
        let current = match line {
            "sat" => Some(QfbvStatus::Sat),
            "unsat" => Some(QfbvStatus::Unsat),
            _ => None,
        };
        if let Some(current) = current {
            match status {
                None => status = Some(current),
                Some(previous) => {
                    bail!("multiple CoqQFBV status lines: first {previous}, then {current}")
                }
            }
        }
    }
    status.context("CoqQFBV output contains no exact sat/unsat status line")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_certified_solver_status() {
        assert_eq!(parse_status("sat\n").unwrap(), QfbvStatus::Sat);
        assert_eq!(
            parse_status("UNSAT proof certified: true\nunsat\n").unwrap(),
            QfbvStatus::Unsat
        );
    }

    #[test]
    fn rejects_missing_or_multiple_statuses() {
        assert!(parse_status("UNSAT proof certified: true\n").is_err());
        assert!(parse_status("sat\nunsat\n").is_err());
        assert!(parse_status("sat\nsat\n").is_err());
    }
}
