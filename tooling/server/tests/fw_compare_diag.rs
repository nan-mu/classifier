//! Product firewall dual expand + compare-tree must stay at fail=0.
use server::bpf_image;
use server::expand::{zip_ebpf_maps, Arch, Session};
use server::pred_tree::{self, SnapRun};
use server::rv32_image;

const ELF: &[u8] = include_bytes!("../../test/xdp/firewall/firewall.elf");
const BPF: &[u8] = include_bytes!("../../test/xdp/firewall/firewall.bpf.o");

#[test]
fn firewall_product_compare_fail_count() {
    let elf = rv32_image::parse_xdp_elf(ELF).unwrap();
    let slots = bpf_image::map_lddw_slots(BPF).unwrap();
    let bound = zip_ebpf_maps(&slots, &elf.maps).unwrap();
    let mut rv = Session::new("rv", 512, Arch::Rv32imc, "firewall.elf".into(), elf);
    rv.run_all();
    assert_eq!(rv.snapshot().status, "complete");

    let bpf = bpf_image::extract_insn_words(BPF).unwrap();
    let mut eb = Session::new_ebpf("eb", 512, "firewall.bpf.o".into(), bpf, bound);
    eb.run_all();
    assert_eq!(eb.snapshot().status, "complete");

    let left: SnapRun = serde_json::from_value(snap_run(&rv)).unwrap();
    let right: SnapRun = serde_json::from_value(snap_run(&eb)).unwrap();
    let report = pred_tree::build_compare_tree(&left, &right);
    let fails = report
        .nodes
        .iter()
        .filter(|n| matches!(n.match_status, pred_tree::MatchStatus::Fail))
        .count();
    assert_eq!(fails, 0, "expected fail=0 on simplified firewall dual");
}

fn snap_run(s: &Session) -> serde_json::Value {
    let snap = serde_json::to_value(s.snapshot()).unwrap();
    serde_json::json!({
        "arch": snap.get("arch").cloned().unwrap_or(serde_json::json!("")),
        "nodes": snap.get("nodes").cloned().unwrap_or(serde_json::json!([])),
        "edges": snap.get("edges").cloned().unwrap_or(serde_json::json!([])),
    })
}
