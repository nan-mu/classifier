//! Path-family matching and evidence emission.
//!
//! Path codes are traversal identifiers, not semantic identities.  This
//! module discovers a bijection using UNSAT inequivalence queries and then
//! checks every selected edge again with a caller-supplied authoritative
//! backend.  In production that backend must be standalone CoqQFBV.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Result, bail, ensure};

use super::{BoolExpr, PathFormula, QfbvQuery, QfbvStatus, inequivalence_query};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PathPair {
    pub left: usize,
    pub right: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathFamilyMatching {
    pub checked_pairs: usize,
    pub equivalent_edges: usize,
    pub pairs: Vec<PathPair>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathFamilyEvidence {
    matching: PathFamilyMatching,
}

impl PathFamilyEvidence {
    pub fn matching(&self) -> &PathFamilyMatching {
        &self.matching
    }
}

/// Classify every possible pair and find a perfect matching among the pairs
/// whose inequivalence query is UNSAT.
///
/// `classify` may be a fast, untrusted discovery oracle.  Its results do not
/// become evidence until [`verify_path_family_matching_with`] checks every
/// selected edge using an authoritative backend.
pub fn discover_path_family_matching_with<F>(
    left: &[PathFormula],
    right: &[PathFormula],
    contract: &BoolExpr,
    mut classify: F,
) -> Result<PathFamilyMatching>
where
    F: FnMut(&QfbvQuery) -> Result<QfbvStatus>,
{
    ensure!(
        left.len() == right.len(),
        "path-family cardinality mismatch: left has {}, right has {}",
        left.len(),
        right.len()
    );

    let mut checked_pairs = 0usize;
    let mut equivalent_edges = 0usize;
    let mut edges = vec![Vec::new(); left.len()];
    for (left_index, left_formula) in left.iter().enumerate() {
        for (right_index, right_formula) in right.iter().enumerate() {
            let query = inequivalence_query(left_formula, right_formula, contract.clone());
            checked_pairs += 1;
            if classify(&query)? == QfbvStatus::Unsat {
                equivalent_edges += 1;
                edges[left_index].push(right_index);
            }
        }
        ensure!(
            !edges[left_index].is_empty(),
            "left path {} has no assertion-equivalent right candidate",
            left_formula.path_code
        );
    }

    let mut right_match = vec![None; right.len()];
    for (left_index, left_formula) in left.iter().enumerate() {
        let mut seen = vec![false; right.len()];
        ensure!(
            augment(left_index, &edges, &mut seen, &mut right_match),
            "no injective assertion-equivalent matching at left path {}",
            left_formula.path_code
        );
    }

    let mut pairs = right_match
        .into_iter()
        .enumerate()
        .map(|(right, left)| {
            left.map(|left| PathPair { left, right })
                .ok_or_else(|| anyhow::anyhow!("internal error: unmatched right path {right}"))
        })
        .collect::<Result<Vec<_>>>()?;
    pairs.sort_by_key(|pair| pair.left);
    Ok(PathFamilyMatching {
        checked_pairs,
        equivalent_edges,
        pairs,
    })
}

fn augment(
    left: usize,
    edges: &[Vec<usize>],
    seen: &mut [bool],
    right_match: &mut [Option<usize>],
) -> bool {
    for &right in &edges[left] {
        if seen[right] {
            continue;
        }
        seen[right] = true;
        let can_assign = match right_match[right] {
            None => true,
            Some(previous_left) => augment(previous_left, edges, seen, right_match),
        };
        if can_assign {
            right_match[right] = Some(left);
            return true;
        }
    }
    false
}

fn validate_matching_shape(
    left: &[PathFormula],
    right: &[PathFormula],
    matching: &PathFamilyMatching,
) -> Result<()> {
    ensure!(
        left.len() == right.len(),
        "path-family cardinality mismatch: left has {}, right has {}",
        left.len(),
        right.len()
    );
    ensure!(
        matching.pairs.len() == left.len(),
        "matching covers {} of {} left paths",
        matching.pairs.len(),
        left.len()
    );
    let mut left_codes = BTreeSet::new();
    for formula in left {
        ensure!(
            left_codes.insert(&formula.path_code),
            "duplicate left path code: {}",
            formula.path_code
        );
    }
    let mut right_codes = BTreeSet::new();
    for formula in right {
        ensure!(
            right_codes.insert(&formula.path_code),
            "duplicate right path code: {}",
            formula.path_code
        );
    }

    let mut seen_left = BTreeSet::new();
    let mut seen_right = BTreeSet::new();
    for pair in &matching.pairs {
        ensure!(pair.left < left.len(), "left matching index out of bounds");
        ensure!(
            pair.right < right.len(),
            "right matching index out of bounds"
        );
        ensure!(
            seen_left.insert(pair.left),
            "duplicate left path in matching: {}",
            left[pair.left].path_code
        );
        ensure!(
            seen_right.insert(pair.right),
            "duplicate right path in matching: {}",
            right[pair.right].path_code
        );
    }
    Ok(())
}

/// Recheck every edge of a structurally complete matching.
///
/// Soundness depends on the supplied checker.  The CLI binds this callback to
/// the standalone CoqQFBV process.  Any SAT result or checker error aborts the
/// whole family claim; partial evidence is never returned.
pub fn verify_path_family_matching_with<F>(
    left: &[PathFormula],
    right: &[PathFormula],
    contract: &BoolExpr,
    matching: PathFamilyMatching,
    mut check: F,
) -> Result<PathFamilyEvidence>
where
    F: FnMut(&QfbvQuery) -> Result<QfbvStatus>,
{
    validate_matching_shape(left, right, &matching)?;
    for pair in &matching.pairs {
        let query = inequivalence_query(&left[pair.left], &right[pair.right], contract.clone());
        if check(&query)? != QfbvStatus::Unsat {
            bail!(
                "selected pair left {} / right {} has a counterexample",
                left[pair.left].path_code,
                right[pair.right].path_code
            );
        }
    }
    Ok(PathFamilyEvidence { matching })
}

/// Write the exact matched obligations plus a small, deterministic manifest.
/// The manifest is written last, so its presence indicates that every listed
/// query was emitted successfully.
pub fn write_path_family_evidence(
    root: impl AsRef<Path>,
    left: &[PathFormula],
    right: &[PathFormula],
    contract: &BoolExpr,
    evidence: &PathFamilyEvidence,
    discovery_backend: &str,
    verification_backend: &str,
) -> Result<PathBuf> {
    validate_matching_shape(left, right, &evidence.matching)?;
    let root = root.as_ref();
    let query_dir = root.join("queries");
    fs::create_dir_all(&query_dir)?;

    let mut manifest = String::from(
        "format=classifier-xdp-assert-equivalence-v1\n\
         status=complete\n\
         claim=bijective equality of selected path assertion behavior\n\
         excluded=whole-machine semantics, unobserved effects, Rust implementation correctness\n",
    );
    manifest.push_str(&format!("left_paths={}\n", left.len()));
    manifest.push_str(&format!("right_paths={}\n", right.len()));
    manifest.push_str(&format!(
        "discovery_checked_pairs={}\n",
        evidence.matching.checked_pairs
    ));
    manifest.push_str(&format!(
        "discovery_unsat_edges={}\n",
        evidence.matching.equivalent_edges
    ));
    manifest.push_str(&format!("discovery_backend={discovery_backend}\n"));
    manifest.push_str(&format!("verification_backend={verification_backend}\n"));
    if root.join("inputs/bpf/pathgen").is_dir() {
        manifest.push_str("left_path_artifacts=inputs/bpf/pathgen\n");
    }
    if root.join("inputs/rv32imc/pathgen").is_dir() {
        manifest.push_str("right_path_artifacts=inputs/rv32imc/pathgen\n");
    }

    for (ordinal, pair) in evidence.matching.pairs.iter().enumerate() {
        let left_formula = &left[pair.left];
        let right_formula = &right[pair.right];
        let file_name = format!(
            "match-{ordinal:04}-left-{}-right-{}.smt2",
            safe_component(&left_formula.path_code),
            safe_component(&right_formula.path_code)
        );
        let query = inequivalence_query(left_formula, right_formula, contract.clone());
        query.write_smt2(query_dir.join(&file_name))?;
        manifest.push_str(&format!(
            "match={ordinal}\tleft={}\tright={}\tresult=unsat\tquery=queries/{file_name}\n",
            left_formula.path_code, right_formula.path_code
        ));
    }

    let manifest_path = root.join("manifest.txt");
    fs::write(&manifest_path, manifest)?;
    Ok(manifest_path)
}

fn safe_component(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || matches!(character, '-' | '_') {
                character
            } else {
                '_'
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn formula(code: &str, assertion: BoolExpr) -> PathFormula {
        PathFormula {
            path_code: code.to_owned(),
            assertion,
            entry_registers: Default::default(),
            assertion_sources: Vec::new(),
            input_origins: Default::default(),
            observations: Vec::new(),
        }
    }

    #[test]
    fn matching_uses_semantics_instead_of_path_codes() {
        let left = vec![
            formula("00", BoolExpr::Const(true)),
            formula("01", BoolExpr::Const(false)),
        ];
        let right = vec![
            formula("00", BoolExpr::Const(false)),
            formula("01", BoolExpr::Const(true)),
        ];
        let classify = |query: &QfbvQuery| {
            Ok(if query.assertion == BoolExpr::Const(false) {
                QfbvStatus::Unsat
            } else {
                QfbvStatus::Sat
            })
        };
        let matching =
            discover_path_family_matching_with(&left, &right, &BoolExpr::Const(true), classify)
                .unwrap();
        assert_eq!(
            matching.pairs,
            vec![
                PathPair { left: 0, right: 1 },
                PathPair { left: 1, right: 0 }
            ]
        );
    }

    #[test]
    fn evidence_is_not_constructed_from_a_sat_edge() {
        let left = vec![formula("0", BoolExpr::Const(true))];
        let right = vec![formula("1", BoolExpr::Const(true))];
        let matching = PathFamilyMatching {
            checked_pairs: 1,
            equivalent_edges: 1,
            pairs: vec![PathPair { left: 0, right: 0 }],
        };
        let result = verify_path_family_matching_with(
            &left,
            &right,
            &BoolExpr::Const(true),
            matching,
            |_| Ok(QfbvStatus::Sat),
        );
        assert!(result.is_err());
    }
}
