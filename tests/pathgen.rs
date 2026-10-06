//! Integration checks for prefixgen → pathgen.

use std::path::PathBuf;

use classifier::predicate::print::print_prefix;
use classifier::predicate::Predicate;
use classifier::{
    pathgen_bpf, pathgen_rv32, prefixgen_bpf_object, prefixgen_rv32_elf, Environment,
};

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn is_forward_offset(offset: &str) -> bool {
    let s = offset.trim();
    if s.starts_with('-') {
        return false;
    }
    // `+0x0` / `0` is a self/next-style edge; treat non-negative as forward.
    true
}

#[test]
fn just_tx_pathgen_yields_63_paths() {
    let env = Environment::from_toml(
        &std::fs::read_to_string(manifest_dir().join("config/esp32c3.environment.toml")).unwrap(),
    )
    .unwrap();
    let insns = prefixgen_rv32_elf(&manifest_dir().join("example/just_tx.elf"), &env).unwrap();
    let paths = pathgen_rv32(&insns, &env).unwrap();
    assert_eq!(paths.len(), 63, "expected 63 syntactic paths for just_tx");

    for path in &paths {
        for insn in &path.insns {
            for node in &insn.prefix.0 {
                if let Predicate::IfGoto { offset, .. } = &node.predicate {
                    assert!(
                        !is_forward_offset(offset),
                        "forward IfGoto must be replaced: index {} offset {offset}",
                        insn.index
                    );
                }
            }
        }
        assert!(
            !path.code.is_empty() && path.code.bytes().all(|b| b == b'0' || b == b'1'),
            "invalid Huffman code {}",
            path.code
        );
        assert!(
            path.code.starts_with('0'),
            "Huffman code must start with 0: {}",
            path.code
        );
    }
    // Taken-first means lexicographic order is not required, but every code is unique.
    let mut codes: Vec<_> = paths.iter().map(|p| p.code.as_str()).collect();
    codes.sort_unstable();
    codes.dedup();
    assert_eq!(codes.len(), paths.len(), "duplicate Huffman path codes");
}

#[test]
fn bpf_object_pathgen_nonempty_forward_asserts() {
    let insns = prefixgen_bpf_object(&manifest_dir().join("example/bpf.o")).unwrap();
    let paths = pathgen_bpf(&insns).unwrap();
    assert!(!paths.is_empty());
    let has_assert = paths.iter().any(|p| {
        p.insns.iter().any(|i| {
            i.prefix
                .0
                .iter()
                .any(|n| matches!(n.predicate, Predicate::Assert { .. }))
        })
    });
    assert!(has_assert, "expected at least one Assert after pathgen");

    for path in &paths {
        for insn in &path.insns {
            let text = print_prefix(&insn.prefix);
            if let Some(Predicate::IfGoto { offset, .. }) =
                insn.prefix.0.first().map(|n| &n.predicate)
            {
                assert!(
                    !is_forward_offset(offset),
                    "forward if left in path: {text}"
                );
            }
        }
    }
}
