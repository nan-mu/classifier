//! Integration tests that call Lean4 modules through the Rust FFI surface.

use lean_binding::{classifier_expr, compare, ebpf, rv32};

#[test]
fn classifier_expr_add_wraps_at_32() {
    assert_eq!(classifier_expr::add32(0xffff_ffff, 2), 1);
}

#[test]
fn classifier_expr_sub_wraps() {
    assert_eq!(classifier_expr::sub32(0, 1), 0xffff_ffff);
}

#[test]
fn classifier_expr_and() {
    assert_eq!(classifier_expr::and32(0b1100, 0b1010), 0b1000);
}

#[test]
fn classifier_expr_divu_by_zero_is_all_ones() {
    assert_eq!(classifier_expr::divu32(42, 0), 0xffff_ffff);
}

#[test]
fn classifier_expr_tq_toward_zero() {
    // TQ(-7, 2) = -3 → bit pattern
    assert_eq!(classifier_expr::tq32((-7i32) as u32, 2), (-3i32) as u32);
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
    assert_eq!(exprs.len(), 14);
    assert!(exprs
        .iter()
        .any(|e| e["reg"] == "real32:0" && e["term"] == "0"));
    assert!(exprs
        .iter()
        .any(|e| e["reg"] == "context32:0" && e["term"] == "v32:4"));

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
fn rv32_symbolic_packet_offset_preserves_partial_graph() {
    let snapshot = |steps| -> serde_json::Value {
        serde_json::from_str(&rv32::expand_snapshot(steps, 512)).expect("json")
    };
    // Matches `esp32c3DeepFrontierCheck`: after 38 expands the queued call is
    // still an unbound external jump; the graph freezes with 41 nodes.
    let before = snapshot(37);
    let failed = snapshot(38);
    assert_eq!(before["status"], "running");
    assert_eq!(before["work"], serde_json::json!([40]));
    assert_eq!(before["fuel"], 475);
    assert_eq!(failed["status"], "fail");
    assert_eq!(failed["reason"], "UnboundTarget");
    assert_eq!(failed["failed"], 40);
    assert_eq!(before["failed"], serde_json::Value::Null);
    // BLTU forks and the short-side return survive; no further nodes are added.
    assert_eq!(failed["nodes"], before["nodes"]);
    assert_eq!(failed["edges"], before["edges"]);
    let nodes = failed["nodes"].as_array().expect("nodes");
    let edges = failed["edges"].as_array().expect("edges");
    assert_eq!(nodes.len(), 41);
    assert_eq!(nodes[40]["id"], 40);
    assert_eq!(nodes[40]["loc"], "36");
    assert!(edges.iter().any(|e| e["dir"] == "Taken"));
    assert!(edges.iter().any(|e| e["dir"] == "NotTaken"));
    assert!(nodes.iter().any(|n| n["loc"] == "exit"));
    assert_eq!(failed["work"], serde_json::json!([]));
    assert_eq!(failed["fuel"], 474);
    assert_eq!(snapshot(512), failed);
}

mod stateless_head_ffi {
    use super::rv32;
    use serde_json::{json, Value};

    fn step(words: &[u32], j: u32, exprs: &str, preds: &str) -> Value {
        serde_json::from_str(&rv32::expand_step(words, 42, j, exprs, preds)).unwrap()
    }

    #[test]
    fn symbolic_branch_returns_states_with_complementary_expr_constraints() {
        let words = [0x00051263, 0x00700513, 0x00008067];
        let root: Value =
            serde_json::from_str(&rv32::expand_create(0x400, 0x100, 0x2000, &[], &[], &[]))
                .unwrap();
        let node = &root["nodes"][0];
        let empty = json!([]);
        let result = step(&words, 0, &node["exprs"].to_string(), &empty.to_string());
        assert_eq!(result["status"], "ok");
        assert_eq!(result["reason"], Value::Null);
        assert!(result.get("fuel").is_none());
        let successors = result["successors"].as_array().unwrap();
        assert_eq!(successors.len(), 2);
        for (successor, dir, rel, branch_dir) in [
            (&successors[0], "Taken", "ne", "taken"),
            (&successors[1], "NotTaken", "eq", "notTaken"),
        ] {
            assert_eq!(successor["dir"], dir);
            assert_eq!(successor["loc"], "1");
            let exprs = successor["exprs"].as_array().unwrap();
            let constraint = exprs.iter().find(|e| e["role"] == "constraint").unwrap();
            assert_eq!(constraint["reg"], "real32:10");
            assert_eq!(constraint["rel"], rel);
            assert_eq!(constraint["term"], "0");
            assert_eq!(
                exprs.iter().filter(|e| e["role"] != "constraint").count(),
                node["exprs"].as_array().unwrap().len()
            );
            let preds = successor["predicates"].as_array().unwrap();
            assert_eq!(preds.len(), 1);
            assert_eq!(preds[0]["kind"], "branch");
            assert_eq!(preds[0]["dir"], branch_dir);
            assert_eq!(preds[0]["position"], 1);
            let saved = successor.clone();
            let assigned = step(
                &words,
                1,
                &successor["exprs"].to_string(),
                &successor["predicates"].to_string(),
            );
            let after = &assigned["successors"][0];
            assert!(after["exprs"]
                .as_array()
                .unwrap()
                .iter()
                .all(|e| e["role"] != "constraint" || e["reg"] != "real32:10"));
            // ADDI keeps prior Branch observation via mergePredicate.
            assert_eq!(after["predicates"], successor["predicates"]);
            assert_eq!(*successor, saved);
        }
        assert_eq!(
            step(&words, 0, &node["exprs"].to_string(), &empty.to_string()),
            result
        );
    }

    #[test]
    fn expand_merge_exact_config_is_arch_neutral() {
        let equal = json!({
            "observationModel": "HelperOnly",
            "requiredObservations": ["Helper"],
            "taken": { "id": 42, "loc": "3", "exprs": [], "predicates": [] },
            "notTaken": [
                { "id": 17, "loc": "3", "exprs": [], "predicates": [] },
                { "id": 18, "loc": "4", "exprs": [], "predicates": [] }
            ]
        });
        let merged: Value = serde_json::from_str(&rv32::expand_merge(&equal.to_string())).unwrap();
        assert_eq!(merged["status"], "merged");
        assert_eq!(merged["scope"], "ExactConfig");
        assert_eq!(merged["reuseFrom"], 17);
        assert_eq!(merged["taken"], 42);

        let unequal = json!({
            "observationModel": "HelperOnly",
            "requiredObservations": ["Helper"],
            "taken": { "id": 1, "loc": "3", "exprs": [], "predicates": [] },
            "notTaken": [{ "id": 2, "loc": "4", "exprs": [], "predicates": [] }]
        });
        let rejected: Value =
            serde_json::from_str(&rv32::expand_merge(&unequal.to_string())).unwrap();
        assert_eq!(rejected["status"], "reject");
        assert_eq!(rejected["reason"], "InsufficientEvidence");
        assert_eq!(rejected["detail"], "NoExactConfigMatch");
    }

    #[test]
    fn failures_have_no_successors_and_no_fuel_field() {
        let words = [0x00700513, 0x00008067];
        for (exprs, preds) in [
            ("{}", "[]"),
            ("[]", "{}"),
            ("[", "[]"),
            (r#"[{"reg":"real32:1","rel":"eq","term":"bad"}]"#, "[]"),
            (r#"[{"reg":"packet64:1","rel":"eq","term":"0"}]"#, "[]"),
            ("[]", r#"[{"kind":"unknown"}]"#),
        ] {
            assert_eq!(
                step(&words, 0, exprs, preds),
                json!({
                    "status":"fail", "reason":"LocalReject", "successors":[],
                })
            );
        }
        // Two equalities on one register are value then comparison, not a reject.
        assert_eq!(
            step(
                &words,
                0,
                r#"[{"reg":"real32:1","rel":"eq","term":"0"},{"reg":"real32:1","rel":"eq","term":"1"}]"#,
                "[]",
            ),
            json!({
                "status":"ok",
                "reason":null,
                "successors":[{
                    "dir":"OK",
                    "loc":"1",
                    "exprs":[
                        {"reg":"real32:1","rel":"eq","term":"0"},
                        {"reg":"real32:10","rel":"eq","term":"7"},
                        {"reg":"real32:1","rel":"eq","role":"constraint","term":"1"}
                    ],
                    "predicates":[]
                }],
            })
        );
        assert_eq!(step(&[], 0, "[]", "[]")["reason"], "InvalidEntry");
        assert_eq!(
            step(&[0x000e0513, 0x00008067], 0, "[]", "[]"),
            json!({
                "status":"fail", "reason":"UndefinedSrc", "successors":[],
            })
        );
    }
}

mod ebpf_expand_ffi {
    use super::{compare, ebpf};
    use serde_json::{json, Value};

    /// BPF_ALU | BPF_MOV | BPF_K: w0 ← 1, then EXIT.
    const MOV_R0_1: u64 = 0x0000_0001_0000_00b4;
    const EXIT: u64 = 0x0000_0000_0000_0095;

    #[test]
    fn create_then_step_one_insn() {
        let words = [MOV_R0_1, EXIT];
        let root: Value = serde_json::from_str(&ebpf::expand_create(&ebpf::Create {
            t_ctx: ebpf::T_CTX,
            t_sp: ebpf::T_SP,
            t_data: ebpf::T_DATA,
            packet_bytes: ebpf::PACKET_BYTES,
            alpha_ctx: 0,
            packet_id: 0,
            stack_id: 0,
            slots: &[34],
            terms: &[0],
            map_ids: &[],
            key_sizes: &[],
            value_sizes: &[],
        }))
        .unwrap();
        assert_eq!(root["status"], "running");
        assert!(root.get("fuel").is_none());
        assert_eq!(root["nodes"][0]["loc"], "0");
        let node = &root["nodes"][0];
        let step: Value = serde_json::from_str(&ebpf::expand_step(
            &words,
            0,
            0,
            &node["exprs"].to_string(),
            &node["predicates"].to_string(),
        ))
        .unwrap();
        assert_eq!(step["status"], "ok");
        assert!(step.get("fuel").is_none());
        let successors = step["successors"].as_array().unwrap();
        assert_eq!(successors.len(), 1);
        // eBPF fallthrough uses Direction.OK → wire tag "OK" (RV32 uses Only).
        assert_eq!(successors[0]["dir"], "OK");
        assert_eq!(successors[0]["loc"], "1");
    }

    #[test]
    fn compare_run_same_diff_identical_minimal() {
        let req = json!({
            "left": {"arch":"ebpf","nodes":[{"id":0,"loc":"0","exprs":[],"predicates":[]}],"edges":[]},
            "right": {"arch":"ebpf","nodes":[{"id":0,"loc":"0","exprs":[],"predicates":[]}],"edges":[]}
        });
        let report: Value =
            serde_json::from_str(&compare::run_same_diff(&req.to_string())).unwrap();
        assert_eq!(report["status"], "compared");
        assert_eq!(report["conclusion"], "sameStructure");
        assert_eq!(report["claim"], "structural");
        assert_eq!(report["behavioralEquivalence"], "notEstablished");
    }
}
