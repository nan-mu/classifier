//! just_tx dual expand + compare-tree must stay at fail=0 (host packetBound assoc + VLAN).
use lean_binding::ebpf;
use server::bpf_image;
use server::expand::{Arch, Session};
use server::pred_tree::{self, SnapRun};
use server::rv32_image;

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
    let fails = report
        .nodes
        .iter()
        .filter(|n| matches!(n.match_status, pred_tree::MatchStatus::Fail))
        .count();
    assert_eq!(fails, 0, "expected fail=0 on just_tx product meta");
}

fn snap_run(s: &Session) -> serde_json::Value {
    let snap = serde_json::to_value(s.snapshot()).unwrap();
    serde_json::json!({
        "arch": snap.get("arch").cloned().unwrap_or(serde_json::json!("")),
        "nodes": snap.get("nodes").cloned().unwrap_or(serde_json::json!([])),
        "edges": snap.get("edges").cloned().unwrap_or(serde_json::json!([])),
    })
}
