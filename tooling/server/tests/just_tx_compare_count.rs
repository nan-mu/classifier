//! Product dual expand + compare-tree.
//! `just_tx` matches on predicate kind counts; the VLAN disjunction is expr-incomplete.
//! `just_drop` fails where a return is glued onto one side of the IPv4 test.
use lean_binding::ebpf;
use server::bpf_image;
use server::expand::{Arch, Session};
use server::pred_tree::{self, ListEntry, SnapRun};
use server::rv32_image;

const JUST_DROP_ELF: &[u8] = include_bytes!("../../test/xdp/just_drop/just_drop.elf");
const JUST_DROP_BPF: &[u8] = include_bytes!("../../test/xdp/just_drop/just_drop.bpf.o");

#[test]
fn just_tx_product_compare_fail_count() {
    let elf = rv32_image::parse_xdp_elf(rv32_image::DEFAULT_ELF).unwrap();
    let mut rv = Session::new("rv", 1024, Arch::Rv32imc, "just_tx.elf".into(), elf);
    rv.run_all();
    let bpf = bpf_image::extract_insn_words(bpf_image::DEFAULT_BPF).unwrap();
    let mut eb = Session::new_ebpf(
        "eb",
        1024,
        "just_tx.bpf.o".into(),
        bpf,
        ebpf::Meta::just_tx_product(),
    );
    eb.run_all();
    assert_eq!(rv.snapshot().status, "complete");
    assert_eq!(eb.snapshot().status, "complete");

    let left: SnapRun = serde_json::from_value(snap_run(&rv)).unwrap();
    let right: SnapRun = serde_json::from_value(snap_run(&eb)).unwrap();
    let report = pred_tree::build_compare_tree(&left, &right);
    let fails: Vec<_> = report
        .nodes
        .iter()
        .filter(|n| matches!(n.match_status, pred_tree::MatchStatus::Fail))
        .collect();
    // VLAN `||` has the same branch count on both sides, so the segment passes.
    // The TPID literals stay expr-incomplete.
    assert_eq!(fails.len(), 0, "kind counts match on just_tx");
    assert!(report.nodes.iter().any(|n| {
        n.left.len() >= 3
            && n.right.len() >= 3
            && matches!(n.expr_status, pred_tree::ExprStatus::Incomplete)
    }));
}

#[test]
fn just_drop_lookup_compare_fail_count() {
    let elf = rv32_image::parse_xdp_elf(JUST_DROP_ELF).unwrap();
    let mut rv = Session::new(
        "rv",
        1024,
        Arch::Rv32imc,
        "just_drop.elf".into(),
        elf.clone(),
    );
    rv.run_all();
    let bpf = bpf_image::extract_insn_words(JUST_DROP_BPF).unwrap();
    let mut eb = Session::new_ebpf(
        "eb",
        1024,
        "just_drop.bpf.o".into(),
        bpf,
        drop_meta(JUST_DROP_BPF, &elf),
    );
    eb.run_all();
    assert_eq!(rv.snapshot().status, "complete");
    assert_eq!(eb.snapshot().status, "complete");

    let left: SnapRun = serde_json::from_value(snap_run(&rv)).unwrap();
    let right: SnapRun = serde_json::from_value(snap_run(&eb)).unwrap();
    let report = pred_tree::build_compare_tree(&left, &right);
    let fails = report
        .nodes
        .iter()
        .filter(|n| matches!(n.match_status, pred_tree::MatchStatus::Fail))
        .count();
    let (lookups, others) = helper_observation_counts(&report);
    assert!(lookups > 0, "just_drop compare produced no lookup helpers");
    assert_eq!(others, 0, "lookup fell through to CrossHelper.other");
    assert_eq!(fails, 0, "just_drop compare fail want 0");
}

fn drop_meta(bpf: &[u8], elf: &rv32_image::Rv32Program) -> ebpf::Meta {
    let slots = bpf_image::map_lddw_slots(bpf).unwrap();
    let map = elf.maps.first().expect("just_drop map");
    ebpf::Meta {
        entry: ebpf::Entry::just_tx(),
        resource_locations: slots
            .iter()
            .map(|slot| ebpf::ResourceLocation {
                slot: *slot,
                term: Some(map.map_id.to_string()),
            })
            .collect(),
        maps: elf.maps.clone(),
    }
}

fn helper_observation_counts(report: &pred_tree::TreeReport) -> (usize, usize) {
    let mut lookups = 0;
    let mut others = 0;
    for node in &report.nodes {
        for side in [&node.left, &node.right] {
            for entry in side {
                let ListEntry::Pred { atom } = entry else {
                    continue;
                };
                if atom.kind != "helper" {
                    continue;
                }
                if atom.fingerprint.contains("\"kind\":\"lookup\"") {
                    lookups += 1;
                }
                if atom.fingerprint.contains("\"kind\":\"other\"") {
                    others += 1;
                }
            }
        }
    }
    (lookups, others)
}

fn snap_run(s: &Session) -> serde_json::Value {
    let snap = serde_json::to_value(s.snapshot()).unwrap();
    serde_json::json!({
        "arch": snap.get("arch").cloned().unwrap_or(serde_json::json!("")),
        "nodes": snap.get("nodes").cloned().unwrap_or(serde_json::json!([])),
        "edges": snap.get("edges").cloned().unwrap_or(serde_json::json!([])),
    })
}
