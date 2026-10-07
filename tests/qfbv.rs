use std::path::PathBuf;

use classifier::{
    BoolExpr, Environment, GoalError, QfbvQuery, check_qfbv_file_with, compile_path_asserts,
    discover_path_family_matching_with, inequivalence_query, pathgen_bpf, pathgen_rv32,
    prefixgen_bpf_object, prefixgen_rv32_elf, verify_path_family_matching_with,
    xdp_environment_contract,
};

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn fixture_paths_fail_closed_at_the_first_unmodeled_effect() {
    let root = manifest_dir();

    let bpf_program = prefixgen_bpf_object(&root.join("example/bpf.o")).unwrap();
    let bpf_paths = pathgen_bpf(&bpf_program).unwrap();
    let bpf_error = compile_path_asserts(&bpf_paths[0], "left").unwrap_err();
    assert!(matches!(
        bpf_error,
        GoalError::Unsupported {
            insn_index: 1,
            reason,
            ..
        } if reason.contains("memory load")
    ));

    let environment =
        Environment::from_toml(include_str!("../config/esp32c3.environment.toml")).unwrap();
    let rv_program = prefixgen_rv32_elf(&root.join("example/just_tx.elf"), &environment).unwrap();
    let rv_paths = pathgen_rv32(&rv_program, &environment).unwrap();
    let rv_error = compile_path_asserts(&rv_paths[0], "right").unwrap_err();
    assert!(matches!(
        rv_error,
        GoalError::Unsupported {
            insn_index: 1,
            reason,
            ..
        } if reason.contains("memory store")
    ));
}

#[test]
fn xdp_environment_contract_is_explicit_and_single_map() {
    let mut environment =
        Environment::from_toml(include_str!("../config/esp32c3.environment.toml")).unwrap();
    let contract = xdp_environment_contract(&environment).unwrap();
    let text = QfbvQuery::new(contract).to_smt2().unwrap();
    assert!(text.contains("(bvule input_packet_base input_packet_end)"));
    assert!(text.contains("(bvule input_packet_base (_ bv4294901760 32))"));
    assert!(text.contains("(bvand input_packet_base (_ bv3 32))"));

    let mut second_map = environment.maps[0].clone();
    second_map.id += 1;
    second_map.handle += 4;
    environment.maps.push(second_map);
    assert!(xdp_environment_contract(&environment).is_err());
}

#[test]
fn xdp_fixture_path_family_generates_typed_inequivalence_queries() {
    let root = manifest_dir();
    let environment =
        Environment::from_toml(include_str!("../config/esp32c3.environment.toml")).unwrap();
    let bpf_program = prefixgen_bpf_object(&root.join("example/bpf.o")).unwrap();
    let rv_program = prefixgen_rv32_elf(&root.join("example/just_tx.elf"), &environment).unwrap();
    let bpf_paths = pathgen_bpf(&bpf_program).unwrap();
    let rv_paths = pathgen_rv32(&rv_program, &environment).unwrap();
    assert_eq!(bpf_paths.len(), rv_paths.len());

    let left = bpf_paths
        .iter()
        .map(|path| classifier::compile_xdp_bpf_path_asserts(path, &environment).unwrap())
        .collect::<Vec<_>>();
    let right = rv_paths
        .iter()
        .map(|path| classifier::compile_xdp_rv32_path_asserts(path, &environment).unwrap())
        .collect::<Vec<_>>();
    for formula in left.iter().chain(&right) {
        let self_query = inequivalence_query(formula, formula, BoolExpr::Const(true));
        assert_eq!(
            self_query.to_smt2().unwrap().matches("(check-sat)").count(),
            1
        );
    }

    let z3_available = std::process::Command::new("z3")
        .arg("-version")
        .output()
        .is_ok();
    if !z3_available {
        return;
    }

    let query_path = std::env::temp_dir().join(format!(
        "classifier-xdp-qfbv-family-{}.smt2",
        std::process::id()
    ));
    let contract = xdp_environment_contract(&environment).unwrap();
    let matching = discover_path_family_matching_with(&left, &right, &contract, |query| {
        query.write_smt2(&query_path).unwrap();
        check_qfbv_file_with("z3", &query_path, false)
    })
    .unwrap();
    assert_eq!(matching.checked_pairs, left.len() * right.len());
    let evidence = verify_path_family_matching_with(&left, &right, &contract, matching, |query| {
        query.write_smt2(&query_path).unwrap();
        check_qfbv_file_with("z3", &query_path, false)
    })
    .unwrap();
    assert_eq!(evidence.matching().pairs.len(), left.len());
    let _ = std::fs::remove_file(&query_path);
}
