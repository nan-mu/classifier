use lean_binding::rv32;
use serde_json::Value;

fn addi(rd: u32, rs: u32, imm: u32) -> u32 {
    ((imm & 0xfff) << 20) | (rs << 15) | (rd << 7) | 0x13
}
fn jal(rd: u32, delta: i32) -> u32 {
    let n = delta as u32;
    ((n >> 20 & 1) << 31)
        | ((n >> 1 & 0x3ff) << 21)
        | ((n >> 11 & 1) << 20)
        | (n & 0xff000)
        | (rd << 7)
        | 0x6f
}
fn cj(delta: i32, link: bool) -> u32 {
    let n = delta as u32;
    let bits = ((n >> 11 & 1) << 12)
        | ((n >> 4 & 1) << 11)
        | ((n >> 8 & 3) << 9)
        | ((n >> 10 & 1) << 8)
        | ((n >> 6 & 1) << 7)
        | ((n >> 7 & 1) << 6)
        | ((n >> 1 & 7) << 3)
        | ((n >> 5 & 1) << 2);
    bits | if link { 0x2001 } else { 0xa001 }
}
fn snapshot(words: &[u32], steps: u32) -> Value {
    serde_json::from_str(&rv32::expand_bound_words_snapshot(
        words, 0x400, 0x100, steps, 100,
    ))
    .unwrap()
}
fn term<'a>(node: &'a Value, reg: u32) -> &'a str {
    node["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["reg"] == format!("real32:{reg}") && e["rel"] == "eq")
        .unwrap()["term"]
        .as_str()
        .unwrap()
}
fn call_program(id: u32, form: usize) -> (Vec<u32>, usize, u32) {
    let mut words = vec![addi(8, 1, 0), addi(10, 0, id)];
    for reg in 11..=15 {
        words.push(addi(reg, 0, reg));
    }
    if form >= 2 {
        words.push(addi(1, 0, 0x101));
    }
    let position = words.len();
    let pc = 0x400 + position as u32 * 4;
    let call = match form {
        0 => jal(1, 0x100 - pc as i32),
        1 => cj(0x100 - pc as i32, true),
        2 => 0x000080e7,
        _ => 0x9082,
    };
    let next = pc + if form == 1 || form == 3 { 2 } else { 4 };
    words.extend([call, addi(1, 8, 0), 0x00008067]);
    (words, position, next)
}

#[test]
fn all_link_call_forms_resume_and_preserve_abi() {
    for form in 0..4 {
        let (words, pos, next) = call_program(5, form);
        let s = snapshot(&words, pos as u32 + 1);
        assert_eq!(s["status"], "running", "form {form} reason {}", s["reason"]);
        let before = &s["nodes"][pos];
        let after = &s["nodes"][pos + 1];
        assert_eq!(term(after, 1), next.to_string());
        assert_eq!(term(after, 8), "8192");
        assert_eq!(term(after, 2), term(before, 2));
        assert!(term(after, 10).contains(&format!("externalResult{pos}_0")));
        for r in [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] {
            assert!(term(after, r).contains(&format!("externalResult{pos}_{r}")));
        }
        assert!(after["predicates"].as_array().unwrap().is_empty());
        assert_eq!(snapshot(&words, 100)["status"], "complete");
    }
}

#[test]
fn helper_types_return_opaque_values_and_unknown_returns_minus_one() {
    for id in [1, 2, 3, 5, 6, 28, 65, 999] {
        let (words, pos, _) = call_program(id, 0);
        let s = snapshot(&words, pos as u32 + 1);
        assert_eq!(s["status"], "running", "helper {id}");
        let result = term(&s["nodes"][pos + 1], 10);
        if id == 999 {
            assert_eq!(result, "4294967295");
        } else {
            assert!(result.contains("externalResult"));
        }
        if id == 28 {
            assert!(result.starts_with("low16("), "{result}");
        }
    }
}

#[test]
fn equal_argument_calls_are_fresh_and_replay_is_stable() {
    let mut words = vec![addi(8, 1, 0), addi(10, 0, 5)];
    words.push(jal(1, 0x100 - 0x408));
    words.push(addi(9, 10, 0));
    words.push(addi(10, 0, 5));
    words.push(jal(1, 0x100 - 0x414));
    words.extend([addi(1, 8, 0), 0x00008067]);
    let s = snapshot(&words, 6);
    assert_eq!(s["status"], "running");
    let first = term(&s["nodes"][6], 9);
    let second = term(&s["nodes"][6], 10);
    assert!(first.contains("externalResult2_0"));
    assert!(second.contains("externalResult5_0"));
    assert_ne!(first, second);
    assert_eq!(s, snapshot(&words, 6));
}

#[test]
fn dispatcher_tail_wrong_target_and_missing_continuation_reject() {
    let (mut words, pos, _) = call_program(5, 0);
    for call in [
        jal(0, 0x100 - (0x400 + pos * 4) as i32),
        jal(1, 0x104 - (0x400 + pos * 4) as i32),
    ] {
        words[pos] = call;
        assert_eq!(snapshot(&words, 100)["reason"], "UnboundTarget");
    }
    words[pos] = jal(1, 0x100 - (0x400 + pos * 4) as i32);
    words.truncate(pos + 1);
    assert_eq!(snapshot(&words, 100)["reason"], "UnboundTarget");
    let mut compressed = vec![addi(10, 0, 5), cj(0x100 - 0x404, false), 0x00008067];
    assert_eq!(snapshot(&compressed, 100)["reason"], "UnboundTarget");
    compressed[1] = 0x00008067;
    assert_eq!(snapshot(&compressed, 100)["status"], "complete");
}

#[test]
fn required_arguments_and_symbolic_helper_id_reject() {
    let words = vec![addi(10, 0, 6), jal(1, 0x100 - 0x404), 0x00008067];
    assert_eq!(snapshot(&words, 100)["reason"], "UndefinedSrc");
    let words = vec![jal(1, 0x100 - 0x400), 0x00008067];
    assert_eq!(snapshot(&words, 100)["reason"], "Unsupported");
}

#[test]
fn context_identity_survives_returns_and_adjust_tail_invalidates_end() {
    let mut words = vec![
        addi(9, 10, 0),
        addi(8, 1, 0),
        addi(10, 0, 5),
        jal(1, 0x100 - 0x40c),
    ];
    words.extend([0x0004a603, addi(1, 8, 0), 0x00008067]);
    let s = snapshot(&words, 5);
    assert_eq!(s["status"], "running", "reason {}", s["reason"]);
    assert_eq!(term(&s["nodes"][5], 12), "v32:4");
    words[4] = 0x00052603;
    assert_eq!(snapshot(&words, 100)["reason"], "UndefinedSrc");
    let (words, pos, _) = call_program(65, 0);
    let s = snapshot(&words, pos as u32 + 1);
    let field = s["nodes"][pos + 1]["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["reg"] == "stack32:1")
        .unwrap();
    assert!(field["term"]
        .as_str()
        .unwrap()
        .contains(&format!("externalResult{pos}_33")));
}

#[test]
fn a_loop_revisiting_the_same_helper_gets_new_events() {
    let words = vec![
        addi(10, 0, 5),
        jal(1, 0x100 - 0x404),
        addi(9, 10, 0),
        jal(0, -12),
    ];
    let s = snapshot(&words, 6);
    assert_eq!(s["status"], "running");
    assert!(term(&s["nodes"][6], 9).contains("externalResult1_0"));
    assert!(term(&s["nodes"][6], 10).contains("externalResult5_0"));
    assert_eq!(s, snapshot(&words, 6));
}

#[test]
fn saved_context_is_used_by_compressed_and_narrow_loads() {
    for (load, reg, expected) in [
        (0x408c, 11, "v32:4"),
        (0x0004c603, 12, "extract0,8(v32:4)"),
        (0x0004d603, 12, "extract0,16(v32:4)"),
    ] {
        let words = vec![
            addi(9, 10, 0),
            addi(8, 1, 0),
            addi(10, 0, 5),
            jal(1, 0x100 - 0x40c),
            load,
            addi(1, 8, 0),
            0x00008067,
        ];
        let s = snapshot(&words, 5);
        assert_eq!(s["status"], "running", "load {load:x}, {}", s["reason"]);
        assert_eq!(term(&s["nodes"][5], reg), expected);
    }
}

#[test]
fn bound_ffi_rejects_colliding_or_invalid_metadata() {
    for (base, helper) in [
        (0, 0x100),
        (0x401, 0x100),
        (0x400, 0),
        (0x400, 0x101),
        (0x2000, 0x100),
        (0x400, 0x2000),
        (0x400, 0x400),
    ] {
        let s: Value = serde_json::from_str(&rv32::expand_bound_words_snapshot(
            &[0x00008067],
            base,
            helper,
            0,
            10,
        ))
        .unwrap();
        assert_eq!(s["reason"], "InvalidEntry");
        assert!(s["nodes"].as_array().unwrap().is_empty());
    }
}

#[test]
fn branch_predicates_survive_helper_calls_without_new_contracts() {
    let words = vec![
        addi(8, 1, 0),
        0x00051263,
        addi(10, 0, 5),
        jal(1, 0x100 - 0x40c),
        addi(1, 8, 0),
        0x00008067,
    ];
    let s = snapshot(&words, 6);
    assert_eq!(s["status"], "running");
    for (before, after, rel) in [(4, 6, "ne"), (5, 7, "eq")] {
        let predicate =
            serde_json::json!([{"kind":"cmp","rel":rel,"width":32,"lhs":"v32:1","rhs":"0"}]);
        assert_eq!(s["nodes"][before]["predicates"], predicate);
        assert_eq!(s["nodes"][after]["predicates"], predicate);
        assert!(term(&s["nodes"][after], 10).contains(&format!("externalResult{before}_0")));
    }
}
