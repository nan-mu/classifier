//! Integration tests that call Lean4 modules through the Rust FFI surface.

use lean_binding::{common_math, rv32};

#[test]
fn common_math_add_wraps_at_32() {
    assert_eq!(common_math::add32(0xffff_ffff, 2), 1);
}

#[test]
fn common_math_sub_wraps() {
    assert_eq!(common_math::sub32(0, 1), 0xffff_ffff);
}

#[test]
fn common_math_and() {
    assert_eq!(common_math::and32(0b1100, 0b1010), 0b1000);
}

#[test]
fn common_math_divu_by_zero_is_all_ones() {
    assert_eq!(common_math::divu32(42, 0), 0xffff_ffff);
}

#[test]
fn common_math_tq_toward_zero() {
    // TQ(-7, 2) = -3 → bit pattern
    assert_eq!(common_math::tq32((-7i32) as u32, 2), (-3i32) as u32);
}

#[test]
fn path_demo_section18_budget() {
    assert!(common_math::path_demo_check());
    assert_eq!(common_math::path_demo_nodes(11), 12);
    assert_eq!(common_math::path_demo_nodes(10), 0);
}

#[test]
fn path_demo_snapshot_complete_and_limit() {
    assert!(common_math::path_demo_check());

    let done: serde_json::Value =
        serde_json::from_str(&common_math::path_demo_snapshot(11, 11)).expect("json");
    assert_eq!(done["status"], "complete");
    assert_eq!(done["reason"], serde_json::Value::Null);
    assert_eq!(done["fuel"], 0);
    let nodes = done["nodes"].as_array().expect("nodes");
    assert_eq!(nodes.len(), 12);
    assert_eq!(nodes[11]["loc"], "exit");
    let exprs = nodes[11]["exprs"].as_array().expect("exprs");
    assert_eq!(exprs.len(), 1);
    assert_eq!(exprs[0]["reg"], "real32:1");
    assert_eq!(exprs[0]["rel"], "eq");
    assert_eq!(exprs[0]["term"], "3");
    // Predicate class merge is undefined until Phase 3; Demo keeps empty Pi.
    let preds = nodes[11]["predicates"].as_array().expect("predicates");
    assert!(preds.is_empty());

    // After 10 successful expandOnes with B=10, fuel is 0 and work remains (running).
    // The next expandOne observes LimitExceeded.
    let at_limit: serde_json::Value =
        serde_json::from_str(&common_math::path_demo_snapshot(10, 10)).expect("json");
    assert_eq!(at_limit["status"], "running");
    assert_eq!(at_limit["fuel"], 0);
    assert_eq!(at_limit["work"], serde_json::json!([10]));

    let limited: serde_json::Value =
        serde_json::from_str(&common_math::path_demo_snapshot(11, 10)).expect("json");
    assert_eq!(limited["status"], "fail");
    assert_eq!(limited["reason"], "LimitExceeded");
    assert_eq!(limited["fuel"], 0);
    let limited_nodes = limited["nodes"].as_array().expect("nodes");
    assert_eq!(limited_nodes.len(), 11);
    assert!(limited_nodes.iter().all(|n| n["loc"] != "exit"));
}

#[test]
fn decode_addi() {
    // addi x1, x2, 5  → 0x00510093
    assert_eq!(rv32::decode32(0x0051_0093), rv32::tag::ADDI);
}

#[test]
fn decode_lui() {
    // lui x1, 0x1
    assert_eq!(rv32::decode32(0x0000_10b7), rv32::tag::LUI);
}

#[test]
fn decode_add() {
    // add x3, x1, x2 → 0x002081b3
    assert_eq!(rv32::decode32(0x0020_81b3), rv32::tag::ADD);
}

#[test]
fn decode_c_nop() {
    assert_eq!(rv32::decode16(0x0001), rv32::tag::C_NOP);
}

#[test]
fn value_addi_concrete() {
    // x2=10, addi x1, x2, 5 → 15
    assert_eq!(rv32::value_addi(10, 5, 2, 1), 15);
}

#[test]
fn value_addi_sign_extend_imm() {
    // imm = -1 as 12-bit (0xfff), rs1=5 → 4
    assert_eq!(rv32::value_addi(5, 0xfff, 2, 1), 4);
}

#[test]
fn value_addi_to_x0_is_discarded() {
    assert_eq!(rv32::value_addi(10, 5, 2, 0), 0);
}

#[test]
fn value_add_concrete() {
    assert_eq!(rv32::value_add(7, 9, 1, 2, 3), 16);
}

#[test]
fn value_lui() {
    // uimm20=1 → 0x1000
    assert_eq!(rv32::value_lui(1, 1), 0x1000);
}

#[test]
fn value_auipc() {
    // pc=0x1000, uimm20=1 → 0x1000 + 0x1000 = 0x2000
    assert_eq!(rv32::value_auipc(0x1000, 1, 1), 0x2000);
}

#[test]
fn value_div_by_zero() {
    assert_eq!(rv32::value_div(100, 0), 0xffff_ffff);
}

#[test]
fn ecall_is_rejected() {
    assert!(rv32::ecall_rejects());
}

#[test]
fn expr_override_replaces_same_key_keeps_others() {
    assert!(rv32::expr_override_keeps());
}

#[test]
fn rv32_expand_esp32c3_root_and_opening() {
    let root: serde_json::Value =
        serde_json::from_str(&rv32::expand_snapshot(0, 48)).expect("json");
    assert_eq!(root["status"], "running");
    assert_eq!(root["fuel"], 48);
    assert_eq!(root["work"], serde_json::json!([0]));
    let nodes = root["nodes"].as_array().expect("nodes");
    assert_eq!(nodes.len(), 1);
    assert_eq!(nodes[0]["loc"], "0");
    let exprs = nodes[0]["exprs"].as_array().expect("exprs");
    assert_eq!(exprs.len(), 28);
    assert!(exprs.iter().any(|e| e["reg"] == "real32:0" && e["term"] == "0"));
    assert!(exprs.iter().any(|e| e["reg"] == "stack32:0"));

    // After first C_LW a2,0(a0): real32:12 = EntryVar.data (v32:4).
    let step1: serde_json::Value =
        serde_json::from_str(&rv32::expand_snapshot(1, 48)).expect("json");
    assert_eq!(step1["status"], "running");
    let n1 = step1["nodes"].as_array().expect("nodes");
    assert_eq!(n1.len(), 2);
    let exprs1 = n1[1]["exprs"].as_array().expect("exprs");
    assert!(exprs1
        .iter()
        .any(|e| e["reg"] == "real32:12" && e["term"] == "v32:4"));

    // Short budget: after B successful expands fuel is 0 and work remains (running);
    // the next expand observes LimitExceeded. Exit is unreachable on 48 insns.
    let at_limit: serde_json::Value =
        serde_json::from_str(&rv32::expand_snapshot(3, 3)).expect("json");
    assert_eq!(at_limit["status"], "running");
    assert_eq!(at_limit["fuel"], 0);
    assert_eq!(at_limit["nodes"].as_array().expect("nodes").len(), 4);

    let limited: serde_json::Value =
        serde_json::from_str(&rv32::expand_snapshot(4, 3)).expect("json");
    assert_eq!(limited["status"], "fail");
    assert_eq!(limited["reason"], "LimitExceeded");
    assert_eq!(limited["nodes"].as_array().expect("nodes").len(), 4);
}

#[test]
fn rv32_out_of_image_cjal_preserves_partial_graph() {
    let snapshot = |steps| -> serde_json::Value {
        serde_json::from_str(&rv32::expand_snapshot(steps, 512)).expect("json")
    };
    let before = snapshot(39);
    let failed = snapshot(40);
    assert_eq!(before["status"], "running");
    assert_eq!(before["work"], serde_json::json!([41, 42, 43]));
    assert_eq!(before["fuel"], 473);
    assert_eq!(failed["status"], "fail");
    assert_eq!(failed["reason"], "UnboundTarget");
    // Includes every pre-instruction expression and predicate: BLTU forks,
    // successful STORE effects, and the short-side return survive rejection.
    assert_eq!(failed["nodes"], before["nodes"]);
    assert_eq!(failed["edges"], before["edges"]);
    let nodes = failed["nodes"].as_array().expect("nodes");
    let edges = failed["edges"].as_array().expect("edges");
    assert_eq!(nodes.len(), 44);
    assert_eq!(nodes[41]["id"], 41);
    assert_eq!(nodes[41]["loc"], "36");
    assert!(edges.iter().any(|e| e["dst"] == 41));
    assert!(!edges.iter().any(|e| e["src"] == 41));
    assert!(edges.iter().any(|e| e["dir"] == "Taken"));
    assert!(edges.iter().any(|e| e["dir"] == "NotTaken"));
    assert!(nodes.iter().any(|n| n["loc"] == "exit"));
    assert_eq!(failed["work"], serde_json::json!([42, 43]));
    assert_eq!(failed["fuel"], 472);
    assert_eq!(snapshot(512), failed);
}
