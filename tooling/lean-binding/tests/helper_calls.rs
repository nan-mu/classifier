use lean_binding::rv32::{self, MapLayout};
use serde_json::Value;

fn addi(rd: u32, rs: u32, imm: u32) -> u32 {
    ((imm & 0xfff) << 20) | (rs << 15) | (rd << 7) | 0x13
}
fn load(rd: u32, base: u32, offset: u32, width: u32, unsigned: bool) -> u32 {
    let funct3 = match (width, unsigned) {
        (1, false) => 0,
        (2, false) => 1,
        (4, _) => 2,
        (1, true) => 4,
        (2, true) => 5,
        _ => panic!("invalid load width"),
    };
    ((offset & 0xfff) << 20) | (base << 15) | (funct3 << 12) | (rd << 7) | 0x03
}
fn store(base: u32, source: u32, offset: u32, width: u32) -> u32 {
    let funct3 = match width {
        1 => 0,
        2 => 1,
        4 => 2,
        _ => panic!("invalid store width"),
    };
    ((offset & 0xfe0) << 20)
        | (source << 20)
        | (base << 15)
        | (funct3 << 12)
        | ((offset & 0x1f) << 7)
        | 0x23
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
fn snapshot_maps(words: &[u32], steps: u32, maps: &[MapLayout]) -> Value {
    let ids: Vec<u32> = maps.iter().map(|m| m.map_id).collect();
    let keys: Vec<u32> = maps.iter().map(|m| m.key_size).collect();
    let vals: Vec<u32> = maps.iter().map(|m| m.value_size).collect();
    let root: Value = serde_json::from_str(&rv32::expand_create(0x400, 0x100, 0x2000, &ids, &keys, &vals)).unwrap();
    let node = &root["nodes"][0];
    serde_json::from_str(&rv32::expand_bound_words_snapshot(
        words,
        &node["exprs"].to_string(),
        &node["predicates"].to_string(),
        steps,
        100,
    ))
    .unwrap()
}

fn snapshot(words: &[u32], steps: u32) -> Value {
    snapshot_maps(words, steps, &[])
}

/// call_program sets a1=11; the installed layout must match that Map id.
fn lookup_map() -> MapLayout {
    MapLayout {
        map_id: 11,
        key_size: 4,
        value_size: 32,
    }
}

/// Lookup call with a 4-byte key at `[sp]` and `a2 = sp` (jal offset computed after setup).
fn call_program_lookup_keyed(form: usize) -> (Vec<u32>, usize, u32) {
    let mut words = vec![addi(8, 1, 0), addi(10, 0, 1)];
    for reg in 11..=15 {
        words.push(addi(reg, 0, reg));
    }
    words.extend([addi(13, 0, 0x101), store(2, 13, 0, 4), addi(12, 2, 0)]);
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

fn has_map_write(s: &Value) -> bool {
    s["nodes"].as_array().unwrap().iter().any(|n| {
        n["predicates"]
            .as_array()
            .unwrap()
            .iter()
            .any(|p| p["kind"] == "mapWrite")
    })
}
fn term(node: &Value, reg: u32) -> &str {
    node["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["reg"] == format!("real32:{reg}") && e["rel"] == "eq")
        .unwrap()["term"]
        .as_str()
        .unwrap()
}

fn helper_pred(node: &Value) -> &Value {
    node["predicates"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["kind"] == "helper")
        .expect("helper Predicate")
}

fn map_word_alpha(resource: u64, byte_offset: u64) -> u64 {
    (resource + byte_offset) * (resource + byte_offset + 1) / 2 + byte_offset
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
        // Return-only projection: only a0 is overwritten.
        assert!(term(after, 10).contains(&format!("externalResult{pos}_0")));
        for r in [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] {
            let before_t = before["exprs"]
                .as_array()
                .unwrap()
                .iter()
                .find(|e| e["reg"] == format!("real32:{r}") && e["rel"] == "eq");
            let after_t = after["exprs"]
                .as_array()
                .unwrap()
                .iter()
                .find(|e| e["reg"] == format!("real32:{r}") && e["rel"] == "eq");
            match (before_t, after_t) {
                (Some(b), Some(a)) => assert_eq!(a["term"], b["term"], "form {form} r{r}"),
                (None, None) => {}
                (None, Some(a)) => panic!("form {form} invented r{r} binding {}", a["term"]),
                (Some(_), None) => panic!("form {form} dropped r{r} binding"),
            }
        }
        let pred = helper_pred(after);
        assert_eq!(pred["helperId"], 5);
        assert_eq!(pred["event"], pos);
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
fn context_identity_survives_returns_and_adjust_tail_keeps_data_end() {
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
    let before = snapshot(&words, pos as u32);
    let s = snapshot(&words, pos as u32 + 1);
    assert!(term(&s["nodes"][pos + 1], 10).contains(&format!("externalResult{pos}_0")));
    // Return-only projection does not rewrite data_end; stack SW bindings are unchanged.
    // Return-only projection does not rewrite data_end (context32:1).
    let before_end = before["nodes"][pos]["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["reg"] == "context32:1")
        .unwrap()["term"]
        .clone();
    let after_end = s["nodes"][pos + 1]["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["reg"] == "context32:1")
        .unwrap()["term"]
        .clone();
    assert_eq!(after_end, before_end);
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
        (0x0004c603, 12, "zext8/32(extract0,8(v32:4))"),
        (0x0004d603, 12, "zext16/32(extract0,16(v32:4))"),
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
        let s: Value =
            serde_json::from_str(&rv32::expand_create(base, helper, 0x2000, &[], &[], &[])).unwrap();
        assert_eq!(s["reason"], "InvalidEntry");
        assert!(s["nodes"].as_array().unwrap().is_empty());
    }
}

#[test]
fn branch_constraints_are_overwritten_while_old_snapshots_and_helper_observations_survive() {
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
        let branch = if before == 4 { 2 } else { 3 };
        let historical = s["nodes"][branch]["exprs"].as_array().unwrap();
        assert!(historical
            .iter()
            .any(|e| e["role"] == "constraint" && e["reg"] == "real32:10" && e["rel"] == rel));
        for id in [before, after] {
            assert!(s["nodes"][id]["exprs"]
                .as_array()
                .unwrap()
                .iter()
                .all(|e| e["role"] != "constraint" || e["reg"] != "real32:10"));
            assert!(s["nodes"][id]["predicates"]
                .as_array()
                .unwrap()
                .iter()
                .all(|p| p["kind"] != "cmp"));
        }
        let after_preds = s["nodes"][after]["predicates"].as_array().unwrap();
        let helper = after_preds
            .iter()
            .find(|p| p["kind"] == "helper")
            .expect("helper Predicate after call");
        assert_eq!(helper["helperId"], 5);
        assert_eq!(helper["event"], before);
        assert!(term(&s["nodes"][after], 10).contains(&format!("externalResult{before}_0")));
    }
}

#[test]
fn lookup_introduces_helper_predicate_and_map_regvar() {
    let (mut words, pos, _) = call_program(1, 0);
    let s = snapshot(&words, pos as u32 + 1);
    assert_eq!(s["status"], "running", "reason {}", s["reason"]);
    let after = &s["nodes"][pos + 1];
    let pred = helper_pred(after);
    assert_eq!(pred["helperId"], 1);
    assert_eq!(pred["event"], pos);
    let alpha = map_word_alpha(pos as u64, 0);
    let map = after["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["reg"] == format!("map32:{alpha}"))
        .expect("mapWord binding");
    assert!(
        map["term"]
            .as_str()
            .unwrap()
            .starts_with(&format!("regVar{pos}(")),
        "{}",
        map["term"]
    );
    let original = map["term"].as_str().unwrap().to_owned();
    words.splice(
        pos + 1..pos + 1,
        [addi(9, 10, 0), addi(10, 0, 5), load(12, 9, 0, 4, true)],
    );
    let s = snapshot(&words, pos as u32 + 4);
    assert_eq!(s["status"], "running", "{}", s["reason"]);
    let after = &s["nodes"][pos + 4];
    assert_eq!(term(after, 12), original);
    assert_eq!(term(after, 10), "5");
    let map = after["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["reg"] == format!("map32:{alpha}"))
        .unwrap();
    assert_eq!(map["term"], original, "Map LOAD must only write rd");
    assert_eq!(snapshot(&words, 100)["status"], "complete");
}

#[test]
fn lookup_map_stores_and_alias_subword_loads_share_the_first_word() {
    let (mut words, pos, _) = call_program_lookup_keyed(0);
    words.splice(
        pos + 1..pos + 1,
        [
            addi(9, 10, 0),
            addi(10, 0, 5),
            addi(13, 0, 0x123),
            store(9, 13, 0, 4),
            addi(9, 9, 3),
            addi(13, 0, 0x80),
            store(9, 13, 0, 1),
            load(14, 9, 0, 1, false),
            load(15, 9, 0xfff, 2, true),
            load(12, 9, 0xffd, 4, true),
            addi(13, 0, 0x456),
            store(9, 13, 0xfff, 2),
            load(16, 9, 0xffd, 4, true),
        ],
    );
    let s = snapshot_maps(&words, 100, &[lookup_map()]);
    assert_eq!(s["status"], "complete", "{}", s["reason"]);
    assert!(has_map_write(&s), "expected MapWrite observations");
    let exit = s["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["loc"] == "exit")
        .unwrap();
    assert_eq!(term(exit, 10), "5");
    assert_eq!(term(exit, 14), "4294967168");
    assert_eq!(term(exit, 15), "32768");
    assert_eq!(term(exit, 12), "2147483939"); // 0x80000123
    assert_eq!(term(exit, 16), "72745251"); // 0x04560123
    let maps: Vec<_> = exit["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["reg"].as_str().unwrap().starts_with("map32:"))
        .collect();
    assert_eq!(maps.len(), 1);
    assert_eq!(
        maps[0]["reg"],
        format!("map32:{}", map_word_alpha(pos as u64, 0))
    );
    assert_eq!(maps[0]["term"], "72745251");
}

#[test]
fn unresolved_map_accesses_reject_without_growing_the_graph() {
    for (id, offset, width) in [
        (1, 3, 2),
        (1, 7, 2),
        (1, 5, 4),
        (5, 0, 4),
        (5, 4, 4),
        (999, 0, 4),
    ] {
        for writing in [false, true] {
            let (mut words, pos, _) = call_program(id, 0);
            let access = if writing {
                store(10, 11, offset, width)
            } else {
                load(12, 10, offset, width, true)
            };
            words.insert(pos + 1, access);
            let before = snapshot(&words, pos as u32 + 1);
            let failed = snapshot(&words, pos as u32 + 2);
            assert_eq!(
                failed["reason"], "UndefinedSrc",
                "helper {id}, offset {offset}, write {writing}"
            );
            assert_eq!(failed["failed"], pos + 1);
            assert_eq!(failed["nodes"], before["nodes"]);
            assert_eq!(failed["edges"], before["edges"]);
        }
    }
}

#[test]
fn lookup_later_words_materialize_once_and_preserve_writes_through_aliases() {
    let (mut words, pos, _) = call_program_lookup_keyed(0);
    words.splice(
        pos + 1..pos + 1,
        [
            addi(9, 10, 4),
            addi(10, 0, 5),
            load(12, 9, 0, 4, true),
            load(14, 9, 0, 4, true),
            addi(13, 0, 0x80),
            store(9, 13, 3, 1),
            load(15, 9, 3, 1, false),
            addi(9, 9, 4),
            store(9, 13, 1, 1), // Fresh third word needs symbolic old bits.
            load(16, 9, 1, 1, true),
            store(9, 13, 0xffc, 4), // Full overwrite of the second word.
            load(17, 9, 0xffc, 4, true),
            store(9, 13, 4, 4), // Fresh fourth word needs no old content.
            load(18, 9, 4, 4, true),
        ],
    );
    let s = snapshot_maps(&words, 100, &[lookup_map()]);
    assert_eq!(s["status"], "complete", "{}", s["reason"]);
    assert!(has_map_write(&s), "expected MapWrite observations");
    let exit = s["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["loc"] == "exit")
        .unwrap();
    let content = format!("externalResult{pos}_2(1)");
    assert_eq!(term(exit, 12), content);
    assert_eq!(term(exit, 14), content);
    assert_eq!(term(exit, 10), "5");
    assert!(term(exit, 15).contains(&content), "{}", term(exit, 15));
    assert!(term(exit, 16).contains(&format!("externalResult{pos}_3(1)")));
    assert_eq!(term(exit, 17), "128");
    assert_eq!(term(exit, 18), "128");
    let maps: Vec<_> = exit["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["reg"].as_str().unwrap().starts_with("map32:"))
        .collect();
    assert_eq!(maps.len(), 4);
    for (offset, expected) in [
        (0, format!("regVar{pos}(real32:10)")),
        (4, "128".into()),
        (12, "128".into()),
    ] {
        let map = maps
            .iter()
            .find(|e| e["reg"] == format!("map32:{}", map_word_alpha(pos as u64, offset)))
            .unwrap();
        assert_eq!(map["term"], expected);
    }
    let third = maps
        .iter()
        .find(|e| e["reg"] == format!("map32:{}", map_word_alpha(pos as u64, 8)))
        .unwrap();
    assert!(third["term"]
        .as_str()
        .unwrap()
        .contains(&format!("externalResult{pos}_3(1)")));
    assert!(!maps.iter().any(|e| e["term"]
        .as_str()
        .unwrap()
        .contains(&format!("externalResult{pos}_4"))));
}

#[test]
fn compressed_map_accesses_and_distinct_lookup_events_keep_later_words_separate() {
    let (mut words, pos, _) = call_program_lookup_keyed(0);
    words.splice(
        pos + 1..pos + 1,
        [
            addi(9, 10, 0),
            0x40d0, // C.LW a2,4(s1), first materialization.
            addi(13, 0, 0x123),
            0xc0d4, // C.SW a3,4(s1), same word as C.LW.
            0x40d8, // C.LW a4,4(s1), current stored word.
            addi(10, 0, 1),
            // 22 = byte length of the six insns above (4+2+4+2+2+4).
            jal(1, 0x100 - (0x400 + pos as i32 * 4 + 22)),
            load(15, 10, 4, 4, true),
        ],
    );
    let s = snapshot_maps(&words, 100, &[lookup_map()]);
    assert_eq!(s["status"], "complete", "{}", s["reason"]);
    assert!(has_map_write(&s), "expected MapWrite observations");
    let exit = s["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["loc"] == "exit")
        .unwrap();
    assert_eq!(term(exit, 12), format!("externalResult{pos}_2(1)"));
    assert_eq!(term(exit, 14), "291");
    assert!(term(exit, 15).contains("externalResult"));
    assert_ne!(term(exit, 12), term(exit, 15));
    assert_eq!(
        s,
        snapshot_maps(&words, 100, &[lookup_map()]),
        "event content must replay stably"
    );
}
