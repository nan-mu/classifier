//! Concrete checks previously run by the `semanticCheck` executable.
//! Each assertion reads JSON from the existing expand, update, normalize, or unify export.
//! Term values are the compact strings inside that JSON.

use lean_binding::cross_pred::{self, normalize};
use lean_binding::ebpf::{self, Create};
use lean_binding::expand;
use lean_binding::rv32;
use serde_json::{json, Value};

fn parse(label: &str, raw: &str) -> Value {
    serde_json::from_str(raw).unwrap_or_else(|err| panic!("{label}: {err}\n{raw}"))
}

fn raw_insn(opcode: u64, dst: u64, src: u64, off: i64, imm: u64) -> u64 {
    let off = (off as i16 as u16) as u64;
    opcode + 256 * dst + 4096 * src + 65536 * off + (imm << 32)
}

fn regs64(pairs: &[(u64, &str)]) -> String {
    let rows: Vec<String> = pairs
        .iter()
        .map(|(i, term)| format!(r#"{{"reg":"real:{i}:[0,64)","rel":"eq","term":"{term}"}}"#))
        .collect();
    format!("[{}]", rows.join(","))
}

fn with_eq(parent: &str, reg: &str, term: &str) -> String {
    let step = format!(r#"[{{"reg":"{reg}","rel":"eq","term":"{term}"}}]"#);
    let raw = expand::update(parent, "[]", &step, "[]");
    let value = parse("update", &raw);
    assert_eq!(value["status"], "ok", "{raw}");
    value["exprs"].to_string()
}

fn ebpf_step(words: &[u64], j: u32, exprs: &str) -> Value {
    parse(
        "ebpf step",
        &ebpf::expand_step(words, 70, j, exprs, "[]"),
    )
}

fn sole(label: &str, step: &Value) -> Value {
    assert_eq!(step["status"], "ok", "{label}: {step}");
    assert!(step["reason"].is_null(), "{label}: {step}");
    let successors = step["successors"].as_array().expect(label);
    assert_eq!(successors.len(), 1, "{label}: {step}");
    successors[0].clone()
}

fn merged(parent: &str, successor: impl std::borrow::Borrow<Value>) -> Value {
    let successor = successor.borrow();
    let raw = expand::update(
        parent,
        "[]",
        &successor["writes"].to_string(),
        &successor["observations"].to_string(),
    );
    let value = parse("merged", &raw);
    assert_eq!(value["status"], "ok", "{raw}");
    value
}

fn eq_term(state: &Value, reg: &str) -> String {
    state["exprs"]
        .as_array()
        .into_iter()
        .flatten()
        .find(|row| {
            row["reg"] == reg && row["rel"] == "eq" && row.get("role").is_none()
        })
        .map(|row| row["term"].as_str().unwrap().to_string())
        .unwrap_or_else(|| panic!("missing {reg} in {state}"))
}

fn reg_bounds(reg: &str) -> Option<(u32, u32)> {
    let start = reg.find('[')?;
    let body = reg[start + 1..].strip_suffix(')')?;
    let (lo, hi) = body.split_once(',')?;
    Some((lo.parse().ok()?, hi.parse().ok()?))
}

/// Concrete bits covered by one equality. A 64-bit ALU result may be two 32-bit rows.
fn slice_nat(state: &Value, reg_prefix: &str, lo: u32, hi: u32) -> Option<u128> {
    let bits = hi - lo;
    let mut best: Option<(u32, u128)> = None;
    for row in state["exprs"].as_array()? {
        if row["rel"] != "eq" || row.get("role").is_some() {
            continue;
        }
        let reg = row["reg"].as_str()?;
        if !reg.starts_with(reg_prefix) {
            continue;
        }
        let (start, end) = reg_bounds(reg)?;
        if start <= lo && hi <= end {
            let value: u128 = row["term"].as_str()?.parse().ok()?;
            let shift = lo - start;
            let mask = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
            let sliced = (value >> shift) & mask;
            let width = end - start;
            if best.map(|(have, _)| width < have).unwrap_or(true) {
                best = Some((width, sliced));
            }
        }
    }
    best.map(|(_, value)| value)
}

fn real64(state: &Value, index: u64) -> String {
    let prefix = format!("real:{index}:");
    if let Some(value) = slice_nat(state, &prefix, 0, 64) {
        return value.to_string();
    }
    let lo = slice_nat(state, &prefix, 0, 32).unwrap_or_else(|| panic!("missing r{index} in {state}"));
    let hi = slice_nat(state, &prefix, 32, 64).unwrap_or(0);
    ((hi << 32) | lo).to_string()
}

fn assert_r64(label: &str, word: u64, exprs: &str, reg: u64, expected: &str) {
    let step = ebpf_step(&[word, 0x95], 0, exprs);
    let one = sole(label, &step);
    assert_eq!(one["dir"], "OK", "{label}: {step}");
    assert_eq!(one["loc"], "1", "{label}: {step}");
    let state = merged(exprs, one);
    assert_eq!(real64(&state, reg), expected, "{label}\n{state}");
}

fn assert_fail(label: &str, step: &Value, reason: &str) {
    assert_eq!(step["status"], "fail", "{label}: {step}");
    assert_eq!(step["reason"], reason, "{label}: {step}");
    assert_eq!(
        step["successors"].as_array().map(Vec::len),
        Some(0),
        "{label}: {step}"
    );
}

fn entry(packet_bytes: u32, t_data: &str) -> String {
    let raw = ebpf::expand_create(&Create {
        t_ctx: "v64:1",
        t_sp: "v64:0",
        t_data,
        packet_bytes,
        alpha_ctx: 0,
        packet_id: 0,
        stack_id: 0,
        slots: &[],
        terms: &[],
        map_ids: &[],
        key_sizes: &[],
        value_sizes: &[],
    });
    let value = parse("entry", &raw);
    assert_eq!(value["status"], "running", "{raw}");
    value["nodes"][0]["exprs"].to_string()
}

fn stack_reg(unit: u32) -> String {
    let lo = (508 - 4 * unit) * 8;
    format!("stack:[{lo},{})", lo + 32)
}

fn eval_piece(term: &str) -> Option<u128> {
    if let Ok(value) = term.parse::<u128>() {
        return Some(value);
    }
    if let Some(rest) = term.strip_prefix("low") {
        let (bits, payload) = rest.split_once('(')?;
        let bits: u32 = bits.parse().ok()?;
        let inner = payload.strip_suffix(')')?;
        let value = eval_piece(inner)?;
        let mask = (1u128 << bits) - 1;
        return Some(value & mask);
    }
    if let Some(rest) = term.strip_prefix("extract") {
        let (head, payload) = rest.split_once('(')?;
        let (offset, len) = head.split_once(',')?;
        let offset: u32 = offset.parse().ok()?;
        let len: u32 = len.parse().ok()?;
        let inner = payload.strip_suffix(')')?;
        let value = eval_piece(inner)?;
        let mask = (1u128 << len) - 1;
        return Some((value >> offset) & mask);
    }
    None
}

fn stitch(state: &Value, prefix: &str, lo: u32, hi: u32) -> Option<u128> {
    if let Some(value) = slice_nat(state, prefix, lo, hi) {
        return Some(value);
    }
    let mut parts = Vec::new();
    for row in state["exprs"].as_array()? {
        if row["rel"] != "eq" || row.get("role").is_some() {
            continue;
        }
        let reg = row["reg"].as_str()?;
        if !reg.starts_with(prefix) {
            continue;
        }
        let (start, end) = reg_bounds(reg)?;
        if start >= lo && end <= hi {
            parts.push((start, end, eval_piece(row["term"].as_str()?)?));
        }
    }
    parts.sort_by_key(|part| part.0);
    let mut cursor = lo;
    let mut acc = 0u128;
    for (start, end, value) in parts {
        if start != cursor {
            return None;
        }
        let width = end - start;
        let mask = (1u128 << width) - 1;
        acc |= (value & mask) << (start - lo);
        cursor = end;
    }
    if cursor == hi { Some(acc) } else { None }
}

fn stack_at(state: &Value, unit: u32) -> String {
    let lo = (508 - 4 * unit) * 8;
    stitch(state, "stack:", lo, lo + 32)
        .unwrap_or_else(|| panic!("missing stack unit {unit} in {state}"))
        .to_string()
}

fn rel_compl(rel: &str) -> &'static str {
    match rel {
        "eq" => "ne",
        "ne" => "eq",
        "ltu" => "geu",
        "leu" => "gtu",
        "gtu" => "leu",
        "geu" => "ltu",
        "lts" => "ges",
        "les" => "gts",
        "gts" => "les",
        "ges" => "lts",
        "eqN32" => "neN32",
        "neN32" => "eqN32",
        "ltuN32" => "geuN32",
        "leuN32" => "gtuN32",
        "gtuN32" => "leuN32",
        "geuN32" => "ltuN32",
        "ltsN32" => "gesN32",
        "lesN32" => "gtsN32",
        "gtsN32" => "lesN32",
        "gesN32" => "ltsN32",
        "bitsnz64" => "bitsz64",
        "bitsnz32" => "bitsz32",
        "bitsz64" => "bitsnz64",
        "bitsz32" => "bitsnz32",
        other => panic!("unknown rel {other}"),
    }
}

#[test]
fn ebpf_alu_matches_concrete_results() {
    let rows = [
        ("ADD", 0u64, 0i64, 15u64, 3u64, "18"),
        ("SUB", 1, 0, 15, 3, "12"),
        ("MUL", 2, 0, 15, 3, "45"),
        ("UDIV", 3, 0, 15, 3, "5"),
        ("OR", 4, 0, 10, 3, "11"),
        ("AND", 5, 0, 10, 3, "2"),
        ("LSH", 6, 0, 15, 2, "60"),
        ("RSH", 7, 0, 15, 2, "3"),
        ("UREM", 9, 0, 17, 3, "2"),
        ("XOR", 10, 0, 10, 3, "9"),
        ("ARSH-positive", 12, 0, 15, 2, "3"),
        ("SDIV", 3, 1, 17, 3, "5"),
        ("SREM", 9, 1, 17, 3, "2"),
    ];
    for cls in [4u64, 7] {
        for (name, code, off, a, b, expected) in rows {
            let exprs = regs64(&[(0, &a.to_string()), (1, &b.to_string())]);
            assert_r64(
                &format!("ALU{cls}/{name}/reg"),
                raw_insn(16 * code + 8 + cls, 0, 1, off, 0),
                &exprs,
                0,
                expected,
            );
            assert_r64(
                &format!("ALU{cls}/{name}/imm"),
                raw_insn(16 * code + cls, 0, 0, off, b),
                &exprs,
                0,
                expected,
            );
        }
        let max: u64 = if cls == 4 { u32::MAX as u64 } else { u64::MAX };
        let min: u64 = if cls == 4 { 1 << 31 } else { 1 << 63 };
        let neg_three = max - 2;
        let bounds = [
            ("ARSH-negative-one", 12u64, 0i64, max, 1u64, max.to_string()),
            ("ARSH-negative-odd", 12, 0, neg_three, 1, (max - 1).to_string()),
            ("UDIV-zero", 3, 0, 7, 0, "0".into()),
            ("UREM-zero", 9, 0, 7, 0, "7".into()),
            ("SDIV-zero", 3, 1, 7, 0, "0".into()),
            ("SREM-zero", 9, 1, 7, 0, "7".into()),
            ("SDIV-overflow", 3, 1, min, max, min.to_string()),
            ("SREM-overflow", 9, 1, min, max, "0".into()),
            ("SDIV-negative", 3, 1, neg_three, 2, max.to_string()),
            ("SREM-negative", 9, 1, neg_three, 2, max.to_string()),
        ];
        for (name, code, off, a, b, expected) in bounds {
            let exprs = regs64(&[(0, &a.to_string()), (1, &b.to_string())]);
            assert_r64(
                &format!("ALU{cls}/{name}"),
                raw_insn(16 * code + 8 + cls, 0, 1, off, 0),
                &exprs,
                0,
                &expected,
            );
        }
        assert_r64(
            &format!("ALU{cls}/NEG"),
            raw_insn(0x80 + cls, 0, 0, 0, 0),
            &regs64(&[(0, "1")]),
            0,
            &max.to_string(),
        );
        assert_r64(
            &format!("ALU{cls}/MOV-no-old-dst"),
            raw_insn(0xb0 + cls, 0, 0, 0, 7),
            "[]",
            0,
            "7",
        );
    }
    assert_r64(
        "ALU32-clears-high-half",
        raw_insn(0x04, 0, 0, 0, 1),
        &regs64(&[(0, "4294967295")]),
        0,
        "0",
    );
    assert_r64(
        "ALU32-shift-count-masked",
        raw_insn(0x6c, 0, 1, 0, 0),
        &regs64(&[(0, "1"), (1, "33")]),
        0,
        "2",
    );
    assert_r64(
        "ALU64-shift-count-masked",
        raw_insn(0x6f, 0, 1, 0, 0),
        &regs64(&[(0, "1"), (1, "65")]),
        0,
        "2",
    );
    assert_r64(
        "ALU32 projects both operands before division",
        raw_insn(0x3c, 0, 1, 0, 0),
        &regs64(&[(0, "4294967311"), (1, "4294967299")]),
        0,
        "5",
    );
    assert_r64(
        "MOV32 projects source without old destination",
        raw_insn(0xbc, 0, 1, 0, 0),
        &regs64(&[(1, "4294967297")]),
        0,
        "1",
    );
    assert_r64(
        "MOV64 sign extends immediate",
        raw_insn(0xb7, 0, 0, 0, 0xffffffff),
        "[]",
        0,
        "18446744073709551615",
    );
    assert_r64(
        "MOV32 zero extends immediate",
        raw_insn(0xb4, 0, 0, 0, 0xffffffff),
        "[]",
        0,
        "4294967295",
    );
    for (cls, bits, source, expected) in [
        (4u64, 8i64, 128u64, "4294967168"),
        (4, 16, 32769, "4294934529"),
        (7, 8, 128, "18446744073709551488"),
        (7, 16, 32769, "18446744073709518849"),
        (7, 32, 2147483649, "18446744071562067969"),
    ] {
        assert_r64(
            &format!("MOVSX/{cls}/{bits}"),
            raw_insn(0xb8 + cls, 0, 1, bits, 0),
            &regs64(&[(1, &source.to_string())]),
            0,
            expected,
        );
    }
    for (opcode, bits, expected) in [
        (0xd4u64, 16u64, "30600"),
        (0xd4, 32, "1432778632"),
        (0xd4, 64, "1234605616436508552"),
        (0xdc, 16, "34935"),
        (0xdc, 32, "2289526357"),
        (0xdc, 64, "9833440827789222417"),
        (0xd7, 16, "34935"),
        (0xd7, 32, "2289526357"),
        (0xd7, 64, "9833440827789222417"),
    ] {
        assert_r64(
            &format!("END/{opcode}/{bits}"),
            raw_insn(opcode, 0, 0, 0, bits),
            &regs64(&[(0, "1234605616436508552")]),
            0,
            expected,
        );
    }
}

#[test]
fn ebpf_jumps_record_concrete_and_symbolic_arms() {
    let rows = [
        ("JEQ", 1u64, "eq", "eqN32", false, true),
        ("JGT", 2, "gtu", "gtuN32", true, false),
        ("JGE", 3, "geu", "geuN32", true, true),
        ("JSET", 4, "bitsnz64", "bitsnz32", true, false),
        ("JNE", 5, "ne", "neN32", true, false),
        ("JSGT", 6, "gts", "gtsN32", true, false),
        ("JSGE", 7, "ges", "gesN32", true, true),
        ("JLT", 10, "ltu", "ltuN32", false, false),
        ("JLE", 11, "leu", "leuN32", false, true),
        ("JSLT", 12, "lts", "ltsN32", false, false),
        ("JSLE", 13, "les", "lesN32", false, true),
    ];
    for cls in [5u64, 6] {
        for (name, code, r64, r32, unequal, equal) in rows {
            for (a, b, taken_seed) in [
                (5u64, 3u64, unequal),
                (0, 0, equal),
                (3, 5, [4u64, 5, 10, 11, 12, 13].contains(&code)),
            ] {
                for register_source in [false, true] {
                    let opcode = 16 * code + cls + if register_source { 8 } else { 0 };
                    let exprs = regs64(&[(0, &a.to_string()), (1, &b.to_string())]);
                    let word = raw_insn(
                        opcode,
                        0,
                        if register_source { 1 } else { 0 },
                        1,
                        if register_source { 0 } else { b },
                    );
                    let label = format!("JMP{cls}/{name}/{a}/{register_source}");
                    let step = ebpf_step(&[word, 0x95, 0x95], 0, &exprs);
                    let one = sole(&label, &step);
                    let rel = if cls == 5 { r64 } else { r32 };
                    let rel = if taken_seed { rel } else { rel_compl(rel) };
                    let dir = if taken_seed { "taken" } else { "notTaken" };
                    let loc = if taken_seed { "2" } else { "1" };
                    assert_eq!(one["dir"], if taken_seed { "Taken" } else { "NotTaken" }, "{label}");
                    assert_eq!(one["loc"], loc, "{label}");
                    assert_eq!(
                        one["observations"],
                        json!([{
                            "kind": "branch",
                            "position": 1,
                            "dir": dir,
                            "width": 64,
                            "cond": {"lhs": a.to_string(), "rel": rel, "rhs": b.to_string()}
                        }]),
                        "{label}"
                    );
                }
            }
        }
        let exprs = regs64(&[(0, "18446744073709551615")]);
        for (code, taken) in [(6u64, false), (7, false), (12, true), (13, true)] {
            let step = ebpf_step(&[raw_insn(16 * code + cls, 0, 0, 1, 1), 0x95, 0x95], 0, &exprs);
            let one = sole("signed-negative-jump", &step);
            assert_eq!(
                (one["dir"].as_str(), one["loc"].as_str()),
                (
                    Some(if taken { "Taken" } else { "NotTaken" }),
                    Some(if taken { "2" } else { "1" })
                ),
                "signed-negative-jump/{cls}/{code}"
            );
        }
    }
    let wide = regs64(&[(0, "4294967297")]);
    let low = sole("JMP32-low-view", &ebpf_step(&[raw_insn(0x16, 0, 0, 1, 1), 0x95, 0x95], 0, &wide));
    assert_eq!(low["dir"], "Taken");
    let high = sole("JMP64-high-view", &ebpf_step(&[raw_insn(0x15, 0, 0, 1, 1), 0x95, 0x95], 0, &wide));
    assert_eq!(high["dir"], "NotTaken");
    let ones = regs64(&[(0, "18446744073709551615")]);
    let signed = sole(
        "JMP64 sign extends immediate",
        &ebpf_step(&[raw_insn(0x15, 0, 0, 1, 0xffffffff), 0x95, 0x95], 0, &ones),
    );
    assert_eq!((signed["dir"].as_str(), signed["loc"].as_str()), (Some("Taken"), Some("2")));

    let symbolic = regs64(&[(0, "v64:8"), (1, "5")]);
    let step = ebpf_step(&[raw_insn(0x1d, 0, 1, 1, 0), 0x95, 0x95], 0, &symbolic);
    assert_eq!(step["status"], "ok", "{step}");
    let arms = step["successors"].as_array().unwrap();
    assert_eq!(arms.len(), 2, "{step}");
    for (dir_tag, branch_dir, rel, loc) in [
        ("Taken", "taken", "eq", "2"),
        ("NotTaken", "notTaken", "ne", "1"),
    ] {
        let arm = arms.iter().find(|arm| arm["dir"] == dir_tag).unwrap_or_else(|| panic!("{step}"));
        assert_eq!(arm["loc"], loc);
        assert_eq!(
            arm["observations"],
            json!([{"kind":"branch","position":1,"dir":branch_dir,"width":64,
                "cond":{"lhs":"v64:8","rel":rel,"rhs":"5"}}])
        );
        let state = merged(&symbolic, arm);
        assert_eq!(eq_term(&state, "real:0:[0,64)"), "v64:8");
        let constraints: Vec<&Value> = state["exprs"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["role"] == "constraint")
            .collect();
        assert_eq!(constraints.len(), 1, "{state}");
        assert_eq!(constraints[0]["reg"], "real:0:[0,64)");
        assert_eq!(constraints[0]["rel"], rel);
        assert_eq!(constraints[0]["term"], "5");
    }

    let known_false = regs64(&[(0, "1")]);
    let pruned = sole(
        "known false prunes invalid taken target",
        &ebpf_step(&[raw_insn(0x15, 0, 0, 99, 7), 0x95], 0, &known_false),
    );
    assert_eq!((pruned["dir"].as_str(), pruned["loc"].as_str()), (Some("NotTaken"), Some("1")));
    let known_true = regs64(&[(0, "7")]);
    let forced = sole(
        "known true prunes invalid fallthrough",
        &ebpf_step(&[0x95, raw_insn(0x15, 0, 0, -2, 7)], 1, &known_true),
    );
    assert_eq!((forced["dir"].as_str(), forced["loc"].as_str()), (Some("Taken"), Some("0")));
}

#[test]
fn ebpf_memory_and_atomics_match_stack_and_packet_terms() {
    let root = entry(64, "v32:2");
    let with_source = with_eq(&root, "real:0:[0,64)", "2864434397");
    let stored = sole(
        "ST-W",
        &ebpf_step(&[raw_insn(0x62, 10, 0, -4, 0x11223344), 0x95], 0, &with_source),
    );
    assert_eq!(stack_at(&merged(&with_source, stored), 0), "287454020");

    let double = sole(
        "ST-DW",
        &ebpf_step(&[raw_insn(0x7a, 10, 0, -8, 0xffffffff), 0x95], 0, &with_source),
    );
    let double_state = merged(&with_source, double);
    assert_eq!(stack_at(&double_state, 1), "4294967295");
    assert_eq!(stack_at(&double_state, 0), "4294967295");

    let old = with_eq(&with_source, &stack_reg(0), "287454020");
    let byte = sole(
        "ST-partial byte",
        &ebpf_step(&[raw_insn(0x72, 10, 0, -3, 0xaa), 0x95], 0, &old),
    );
    let byte_state = merged(&old, byte);
    assert_eq!(eq_term(&byte_state, "stack:[4072,4080)"), "low8(170)");
    assert_eq!(eq_term(&byte_state, "stack:[4064,4072)"), "extract0,8(287454020)");
    assert_eq!(eq_term(&byte_state, "stack:[4080,4096)"), "extract16,16(287454020)");
    let half = sole(
        "ST-partial half",
        &ebpf_step(&[raw_insn(0x6a, 10, 0, -4, 0xbbcc), 0x95], 0, &old),
    );
    let half_state = merged(&old, half);
    assert_eq!(eq_term(&half_state, "stack:[4064,4080)"), "low16(48076)");
    assert_eq!(eq_term(&half_state, "stack:[4080,4096)"), "extract16,16(287454020)");
    let hole = sole(
        "ST-partial into undefined",
        &ebpf_step(&[raw_insn(0x72, 10, 0, -3, 0xaa), 0x95], 0, &with_source),
    );
    let hole_state = merged(&with_source, hole);
    assert_eq!(eq_term(&hole_state, "stack:[4072,4080)"), "low8(170)");
    assert!(
        hole_state["exprs"].as_array().unwrap().iter().all(|row| row["reg"] != stack_reg(0)),
        "{hole_state}"
    );

    let signed = with_eq(&with_source, &stack_reg(0), "2147582207");
    for (opcode, off, expected) in [
        (0x91u64, -4i64, "18446744073709551615"),
        (0x89, -4, "18446744073709519103"),
        (0x81, -4, "18446744071562166527"),
    ] {
        assert_r64(
            &format!("MEMSX/{opcode}"),
            raw_insn(opcode, 2, 10, off, 0),
            &signed,
            2,
            expected,
        );
    }
    for (opcode, expected) in [(0xc3u64, "2147582207"), (0xcb, "33023"), (0xd3, "255")] {
        assert_r64(
            &format!("LOAD_ACQ/{opcode}"),
            raw_insn(opcode, 2, 10, -4, 0x100),
            &signed,
            2,
            expected,
        );
    }
    let release = sole(
        "STORE_REL",
        &ebpf_step(&[raw_insn(0xc3, 10, 0, -4, 0x110), 0x95], 0, &signed),
    );
    assert_eq!(stack_at(&merged(&signed, release), 0), "2864434397");
    for (opcode, expected) in [(0xcbu64, "2147601629"), (0xd3, "2147582173")] {
        let step = sole(
            "STORE_REL narrow",
            &ebpf_step(&[raw_insn(opcode, 10, 0, -4, 0x110), 0x95], 0, &signed),
        );
        assert_eq!(stack_at(&merged(&signed, step), 0), expected);
    }
    let wide = with_eq(&signed, &stack_reg(1), "287454020");
    assert_r64(
        "LOAD_ACQ DW",
        raw_insn(0xdb, 2, 10, -8, 0x100),
        &wide,
        2,
        "9223795344823956292",
    );
    let wide_store = sole(
        "STORE_REL DW",
        &ebpf_step(&[raw_insn(0xdb, 10, 0, -8, 0x110), 0x95], 0, &wide),
    );
    let wide_state = merged(&wide, wide_store);
    assert_eq!(stack_at(&wide_state, 1), "2864434397");
    assert_eq!(stack_at(&wide_state, 0), "0");

    let loaded = sole("LOAD-context-data", &ebpf_step(&[raw_insn(0x61, 2, 1, 0, 0), 0x95], 0, &root));
    let loaded_state = merged(&root, loaded);
    let packet = sole(
        "ST-packet",
        &ebpf_step(
            &[raw_insn(0x6a, 2, 0, 3, 0x7788), 0x95],
            0,
            &loaded_state["exprs"].to_string(),
        ),
    );
    assert_eq!(
        packet["observations"],
        json!([{"kind":"packetWrite","offset":3,"width":16,"source":"c64:30600"}])
    );
    let packet_state = merged(&loaded_state["exprs"].to_string(), packet);
    assert_eq!(eq_term(&packet_state, "packet:[24,32)"), "low8(136)");
    assert_eq!(eq_term(&packet_state, "packet:[32,40)"), "low8(119)");
    assert_fail(
        "ST packet boundary",
        &ebpf_step(
            &[raw_insn(0x6a, 2, 0, 63, 0x7788), 0x95],
            0,
            &loaded_state["exprs"].to_string(),
        ),
        "UndefinedSrc",
    );

    for (opcode, off, high) in [(0xc3u64, -4i64, false), (0xdb, -8, true)] {
        let mut seeded = if high {
            with_eq(&with_eq(&root, &stack_reg(1), "10"), &stack_reg(0), "0")
        } else {
            with_eq(&root, &stack_reg(0), "10")
        };
        for (imm, expected) in [
            (0x00u64, "13"),
            (0x01, "13"),
            (0x40, "11"),
            (0x41, "11"),
            (0x50, "2"),
            (0x51, "2"),
            (0xa0, "9"),
            (0xa1, "9"),
            (0xe1, "3"),
        ] {
            let parent = with_eq(&seeded, "real:1:[0,64)", "3");
            let step = sole(
                &format!("atomic/{opcode}/{imm}"),
                &ebpf_step(&[raw_insn(opcode, 10, 1, off, imm), 0x95], 0, &parent),
            );
            let state = merged(&parent, step);
            assert_eq!(
                stack_at(&state, if high { 1 } else { 0 }),
                expected,
                "{opcode}/{imm}"
            );
            assert_eq!(
                real64(&state, 1),
                if imm % 2 == 1 { "10" } else { "3" },
                "{opcode}/{imm}"
            );
            if high {
                assert_eq!(stack_at(&state, 0), "0");
            }
        }
        for (expected_old, next) in [("10", "3"), ("9", "10")] {
            let parent = with_eq(
                &with_eq(&seeded, "real:0:[0,64)", expected_old),
                "real:1:[0,64)",
                "3",
            );
            let step = sole(
                "CMPXCHG",
                &ebpf_step(&[raw_insn(opcode, 10, 1, off, 0xf1), 0x95], 0, &parent),
            );
            let state = merged(&parent, step);
            assert_eq!(stack_at(&state, if high { 1 } else { 0 }), next);
            assert_eq!(real64(&state, 0), "10");
        }
        let _ = &mut seeded;
    }
    let carried = with_eq(
        &with_eq(&root, &stack_reg(1), "4294967295"),
        &stack_reg(0),
        "1",
    );
    let carried = with_eq(&carried, "real:1:[0,64)", "1");
    let carry = sole("DW-carry", &ebpf_step(&[raw_insn(0xdb, 10, 1, -8, 1), 0x95], 0, &carried));
    let carry_state = merged(&carried, carry);
    assert_eq!(stack_at(&carry_state, 1), "0");
    assert_eq!(stack_at(&carry_state, 0), "2");
    assert_eq!(real64(&carry_state, 1), "8589934591");

    let same = with_eq(&with_eq(&root, &stack_reg(0), "10"), "real:0:[0,64)", "10");
    let same_step = sole(
        "CMPXCHG same r0 source",
        &ebpf_step(&[raw_insn(0xc3, 10, 0, -4, 0xf1), 0x95], 0, &same),
    );
    let same_state = merged(&same, same_step);
    assert_eq!(stack_at(&same_state, 0), "10");
    assert_eq!(real64(&same_state, 0), "10");

    let alias_root = entry_sp("4096");
    let alias = with_eq(
        &with_eq(&alias_root, "real:2:[0,64)", "4092"),
        &stack_reg(0),
        "10",
    );
    let alias_step = sole(
        "XCHG base/source alias",
        &ebpf_step(&[raw_insn(0xc3, 2, 2, 0, 0xe1), 0x95], 0, &alias),
    );
    let alias_state = merged(&alias, alias_step);
    assert_eq!(stack_at(&alias_state, 0), "4092");
    assert_eq!(real64(&alias_state, 2), "10");

    let pointed = with_eq(&root, "real:2:[0,64)", "1");
    assert_fail(
        "atomic missing old memory",
        &ebpf_step(&[raw_insn(0xc3, 10, 2, -4, 1), 0x95], 0, &pointed),
        "UndefinedSrc",
    );
    let low_only = with_eq(&pointed, &stack_reg(1), "1");
    assert_fail(
        "atomic missing high half",
        &ebpf_step(&[raw_insn(0xdb, 10, 2, -8, 1), 0x95], 0, &low_only),
        "UndefinedSrc",
    );
    let present = with_eq(&pointed, &stack_reg(0), "1");
    assert_fail(
        "CMPXCHG missing r0",
        &ebpf_step(&[raw_insn(0xc3, 10, 2, -4, 0xf1), 0x95], 0, &present),
        "UndefinedSrc",
    );
    assert_fail(
        "atomic context forbidden",
        &ebpf_step(&[raw_insn(0xc3, 1, 2, 0, 1), 0x95], 0, &pointed),
        "Unsupported",
    );
    assert_fail(
        "atomic unaligned forbidden",
        &ebpf_step(&[raw_insn(0xc3, 10, 2, -3, 1), 0x95], 0, &pointed),
        "UndefinedSrc",
    );
    let packet_base = sole(
        "packet-base",
        &ebpf_step(&[raw_insn(0x61, 3, 1, 0, 0), 0x95], 0, &pointed),
    );
    let packet_parent = merged(&pointed, packet_base);
    assert_fail(
        "atomic packet forbidden",
        &ebpf_step(
            &[raw_insn(0xc3, 3, 2, 0, 1), 0x95],
            0,
            &packet_parent["exprs"].to_string(),
        ),
        "Unsupported",
    );
}

fn entry_sp(sp: &str) -> String {
    let raw = ebpf::expand_create(&Create {
        t_ctx: "v64:1",
        t_sp: sp,
        t_data: "v32:2",
        packet_bytes: 64,
        alpha_ctx: 0,
        packet_id: 0,
        stack_id: 0,
        slots: &[],
        terms: &[],
        map_ids: &[],
        key_sizes: &[],
        value_sizes: &[],
    });
    let value = parse("entry sp", &raw);
    assert_eq!(value["status"], "running", "{raw}");
    value["nodes"][0]["exprs"].to_string()
}

fn rv_m_word(funct: u32) -> u32 {
    0x0200_0033 + 9 * (1 << 20) + 8 * (1 << 15) + funct * (1 << 12) + 10 * (1 << 7)
}

fn rv_step(words: &[u32], exprs: &str) -> Value {
    parse("rv step", &rv32::expand_step(words, 70, 0, exprs, "[]"))
}

fn regs32(pairs: &[(u32, &str)]) -> String {
    let rows: Vec<String> = pairs
        .iter()
        .map(|(i, term)| format!(r#"{{"reg":"real:{i}:[0,32)","rel":"eq","term":"{term}"}}"#))
        .collect();
    format!("[{}]", rows.join(","))
}

#[test]
fn rv32_m_closed_and_open_results() {
    let open = [
        (0u32, "4294967293", "mullo32(v32:41,v32:42)"),
        (1, "4294967295", "mulh32(v32:41,v32:42)"),
        (2, "4294967295", "mulhsu32(v32:41,v32:42)"),
        (3, "2", "mulhu32(v32:41,v32:42)"),
        (4, "0", "sdiv32_4294967295(v32:41,v32:42)"),
        (5, "1431655765", "udiv32_4294967295(v32:41,v32:42)"),
        (6, "4294967295", "srem32(v32:41,v32:42)"),
        (7, "0", "urem32(v32:41,v32:42)"),
    ];
    for (funct, closed, symbolic) in open {
        let concrete = regs32(&[(8, "4294967295"), (9, "3")]);
        let step = sole(
            &format!("RV32-M/{funct}"),
            &rv_step(&[rv_m_word(funct), 0x0001], &concrete),
        );
        assert_eq!(
            eq_term(&merged(&concrete, step), "real:10:[0,32)"),
            closed
        );
        let symbolic_parent = regs32(&[(8, "v32:41"), (9, "v32:42")]);
        let step = sole(
            &format!("RV32-open-M/{funct}"),
            &rv_step(&[rv_m_word(funct), 0x0001], &symbolic_parent),
        );
        assert_eq!(
            eq_term(&merged(&symbolic_parent, step), "real:10:[0,32)"),
            symbolic
        );
    }
    for (funct, a, b, expected) in [
        (4u32, 7u32, 0u32, "4294967295"),
        (5, 7, 0, "4294967295"),
        (6, 7, 0, "7"),
        (7, 7, 0, "7"),
        (4, 2147483648, 4294967295, "2147483648"),
        (6, 2147483648, 4294967295, "0"),
        (4, 4294967293, 2, "4294967295"),
        (6, 4294967293, 2, "4294967295"),
    ] {
        let parent = regs32(&[(8, &a.to_string()), (9, &b.to_string())]);
        let step = sole("RV32-M boundary", &rv_step(&[rv_m_word(funct), 0x0001], &parent));
        assert_eq!(
            eq_term(&merged(&parent, step), "real:10:[0,32)"),
            expected,
            "{funct}/{a}/{b}"
        );
    }
    assert_fail(
        "RV32-M missing source",
        &rv_step(&[rv_m_word(0), 0x0001], "[]"),
        "UndefinedSrc",
    );
    assert_fail(
        "RV32 privileged encoding",
        &rv_step(&[0x3020_0073, 0x0001], "[]"),
        "Unsupported",
    );
}

fn helper_observation(id: u64, args: &[&str]) -> Value {
    json!({"kind":"helper","helperId":id,"args":args})
}

#[test]
fn helper_snapshots_are_frozen_bytes_and_incomplete_reads_reject() {
    let root = entry(64, "v32:2");
    let mut parent = with_eq(&root, "context:mapKeyBytes:42:[0,32)", "3");
    parent = with_eq(&parent, "context:mapValueBytes:42:[0,32)", "2");
    parent = with_eq(&parent, "real:1:[0,64)", "42");
    parent = with_eq(&parent, "real:2:[0,64)", "add64(v64:0,18446744073709551608)");
    parent = with_eq(&parent, "real:3:[0,64)", "add64(v64:0,18446744073709551612)");
    parent = with_eq(&parent, "real:4:[0,64)", "0");
    let full = with_eq(
        &with_eq(&parent, &stack_reg(1), "1144201745"),
        &stack_reg(0),
        "48042",
    );
    let changed = with_eq(&full, &stack_reg(1), "197121");
    for (id, args, ret) in [
        (1u64, vec!["c64:42", "c64:17", "c64:34", "c64:51"], "externalResult0(1,42,17,34,51)"),
        (3, vec!["c64:42", "c64:17", "c64:34", "c64:51"], "externalResult0(3,42,17,34,51)"),
        (
            2,
            vec!["c64:42", "c64:17", "c64:34", "c64:51", "c64:170", "c64:187", "c64:0"],
            "externalResult0(2,42,17,34,51,170,187,0)",
        ),
    ] {
        let step = sole(
            &format!("eBPF helper/{id}"),
            &ebpf_step(&[raw_insn(0x85, 0, 0, 0, id), 0x95], 0, &full),
        );
        assert_eq!(step["observations"], json!([helper_observation(id, &args)]));
        assert_eq!(eq_term(&merged(&full, step), "real:0:[0,64)"), ret);
        let again = sole(
            "eBPF helper changed snapshot",
            &ebpf_step(&[raw_insn(0x85, 0, 0, 0, id), 0x95], 0, &changed),
        );
        let changed_args: Vec<&str> = if id == 2 {
            vec!["c64:42", "c64:1", "c64:2", "c64:3", "c64:170", "c64:187", "c64:0"]
        } else {
            vec!["c64:42", "c64:1", "c64:2", "c64:3"]
        };
        assert_eq!(again["observations"], json!([helper_observation(id, &changed_args)]));
    }
    for incomplete in [
        with_eq(&parent, &stack_reg(0), "48042"),
        with_eq(&parent, &stack_reg(1), "1144201745"),
    ] {
        assert_fail(
            "eBPF update incomplete",
            &ebpf_step(&[raw_insn(0x85, 0, 0, 0, 2), 0x95], 0, &incomplete),
            "UndefinedSrc",
        );
    }
    assert_fail(
        "eBPF delete missing key",
        &ebpf_step(
            &[raw_insn(0x85, 0, 0, 0, 3), 0x95],
            0,
            &with_eq(&parent, &stack_reg(0), "48042"),
        ),
        "UndefinedSrc",
    );

    let mut rv_parent = regs32(&[
        (2, "v32:0"),
        (11, "42"),
        (12, "add32(v32:0,3)"),
        (13, "add32(v32:0,4)"),
        (14, "0"),
    ]);
    for (reg, term) in [
        ("context:imageBase:[0,32)", "4096"),
        ("context:helper:[0,32)", "4352"),
        ("context:wrapperReturn:[0,32)", "8192"),
        ("context:mapKeyBytes:42:[0,32)", "3"),
        ("context:mapValueBytes:42:[0,32)", "2"),
        ("stack:[0,32)", "67305985"),
        ("stack:[32,64)", "134678021"),
    ] {
        rv_parent = with_eq(&rv_parent, reg, term);
    }
    let mut missing = regs32(&[
        (2, "v32:0"),
        (11, "42"),
        (12, "add32(v32:0,3)"),
        (13, "add32(v32:0,4)"),
        (14, "0"),
    ]);
    for (reg, term) in [
        ("context:imageBase:[0,32)", "4096"),
        ("context:helper:[0,32)", "4352"),
        ("context:wrapperReturn:[0,32)", "8192"),
        ("context:mapKeyBytes:42:[0,32)", "3"),
        ("context:mapValueBytes:42:[0,32)", "2"),
        ("stack:[0,32)", "67305985"),
    ] {
        missing = with_eq(&missing, reg, term);
    }
    for (id, args, ret) in [
        (1u64, vec!["42", "4", "5", "6"], "externalResult0(1,42,4,5,6)"),
        (3, vec!["42", "4", "5", "6"], "externalResult0(3,42,4,5,6)"),
        (
            2,
            vec!["42", "4", "5", "6", "5", "6", "0"],
            "externalResult0(2,42,4,5,6,5,6,0)",
        ),
    ] {
        let parent = with_eq(&rv_parent, "real:10:[0,32)", &id.to_string());
        let step = sole(&format!("RV helper/{id}"), &rv_step(&[0x1000_00ef, 0x0001], &parent));
        assert_eq!(step["observations"], json!([helper_observation(id, &args)]));
        assert_eq!(eq_term(&merged(&parent, step), "real:10:[0,32)"), ret);
        let incomplete = with_eq(&missing, "real:10:[0,32)", &id.to_string());
        assert_fail(
            "RV helper incomplete",
            &rv_step(&[0x1000_00ef, 0x0001], &incomplete),
            "UndefinedSrc",
        );
    }
    let missing_value = with_eq(
        &with_eq(&rv_parent, "real:10:[0,32)", "2"),
        "real:13:[0,32)",
        "add32(v32:0,7)",
    );
    assert_fail(
        "RV update missing final byte",
        &rv_step(&[0x1000_00ef, 0x0001], &missing_value),
        "UndefinedSrc",
    );
}

fn solved32(term: &str) -> Result<String, Value> {
    let parent = regs32(&[(8, term)]);
    let step = rv_step(&[0x0004_0513, 0x0001], &parent);
    if step["status"] != "ok" {
        return Err(step);
    }
    let one = sole(term, &step);
    Ok(eq_term(&merged(&parent, one), "real:10:[0,32)"))
}

#[test]
fn solver_rewrites_are_the_term_strings_a_step_writes() {
    let rows = [
        ("R1-whole-closed", "mullo32(add32(2,3),4)", "20", "20"),
        ("R2-spine", "add32(add32(v32:1,16),4)", "add32(v32:1,20)", "29"),
        ("R3-sub", "sub32(v32:1,4)", "add32(v32:1,4294967292)", "5"),
        ("R5-sub", "sub32(v32:1,v32:1)", "0", "0"),
        ("R5-xor", "xor32(v32:1,v32:1)", "0", "0"),
        ("R6-add", "add32(v32:1,0)", "v32:1", "9"),
        ("R6-or", "or32(v32:1,0)", "v32:1", "9"),
        ("R6-xor", "xor32(v32:1,0)", "v32:1", "9"),
        ("R6-and", "and32(v32:1,4294967295)", "v32:1", "9"),
        ("R6-mul", "mullo32(v32:1,1)", "v32:1", "9"),
        ("R6-shl", "shl32(v32:1,0)", "v32:1", "9"),
        ("R6-lshr", "lshr32(v32:1,0)", "v32:1", "9"),
        ("R6-ashr", "ashr32(v32:1,0)", "v32:1", "9"),
        ("R8-shl", "shl32(v32:1,2)", "mullo32(v32:1,4)", "36"),
        ("R8-lshr", "lshr32(v32:1,1)", "udiv32_0(v32:1,2)", "4"),
        ("R8-shl-width", "shl32(v32:1,32)", "v32:1", "9"),
        (
            "R9-disjoint-or",
            "or32(and32(v32:1,255),shl32(and32(v32:2,255),8))",
            "add32(mullo32(and32(v32:2,255),256),and32(v32:1,255))",
            "3337",
        ),
    ];
    let mut failures = Vec::new();
    for (name, input, expected, value) in rows {
        match solved32(input) {
            Ok(actual) if actual == expected => {}
            Ok(actual) => failures.push(format!("{name}: {actual} != {expected}")),
            Err(err) => failures.push(format!("{name} rejected {input}: {err}")),
        }
        match solved32(expected) {
            Ok(actual) if actual == expected => {}
            Ok(actual) => failures.push(format!("{name}/idempotent: {actual} != {expected}")),
            Err(err) => failures.push(format!("{name}/idempotent rejected {expected}: {err}")),
        }
        let concrete = input.replace("v32:2", "13").replace("v32:1", "9");
        let solved = expected.replace("v32:2", "13").replace("v32:1", "9");
        for (label, term) in [("input meaning", concrete), ("solved meaning", solved)] {
            match solved32(&term) {
                Ok(actual) if actual == value => {}
                Ok(actual) => failures.push(format!("{name}/{label}: {actual} != {value}")),
                Err(err) => failures.push(format!("{name}/{label} rejected {term}: {err}")),
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    let unordered = "add32(v32:2,add32(4,v32:1))";
    let reordered = "add32(v32:1,add32(v32:2,4))";
    assert_eq!(solved32(unordered).unwrap(), solved32(reordered).unwrap());
    assert_eq!(
        solved32(&unordered.replace("v32:2", "13").replace("v32:1", "9")).unwrap(),
        "26"
    );
    for (name, input) in [
        ("no-open-subtree-fold", "mullo32(v32:1,add32(2,3))"),
        ("no-symbolic-shl", "shl32(v32:1,v32:2)"),
        ("no-overlapping-or", "or32(and32(v32:1,255),and32(v32:2,255))"),
        ("no-distributivity", "mullo32(v32:1,add32(v32:2,1))"),
    ] {
        assert_eq!(solved32(input).unwrap(), input, "{name}");
    }
    for (name, input) in [("no-partial-or-unit", "or8(v32:1,0)"), ("no-partial-and-unit", "and8(v32:1,255)")] {
        assert!(solved32(input).is_err(), "{name}");
    }
    assert!(solved32("add32(v32:1)").is_err(), "invalid-arity");
    assert!(solved32("sub64(v32:1,v32:1)").is_err(), "invalid-width");
    assert_eq!(solved32("externalResult2(5)").unwrap(), "externalResult2(5)");
    assert!(solved32("inputByte3(4096,4108)").is_err(), "inputByte is 8 bits");
    assert_eq!(
        solved32("sub32(externalResult2(5),externalResult2(5))").unwrap(),
        "0"
    );
    assert_eq!(
        solved32("add32(externalResult2(5),inputByte3(4096,4108))").unwrap(),
        "add32(externalResult2(5),inputByte3(4096,4108))"
    );
}

fn canonical(op: &str, params: Value, arity: usize) -> Value {
    let args: Vec<Value> = (1..=arity)
        .map(|name| json!({"kind":"var","name":name}))
        .collect();
    json!({"kind":"ret","payload":{"kind":"app","op":op,"params":params,"args":args}})
}

#[test]
fn operator_terms_normalize_to_canonical_json() {
    for (bits, max) in [(32u64, 4294967295u64), (64, 18446744073709551615)] {
        let rows = [
            ("udiv", json!([bits, 0]), format!("udiv{bits}_0")),
            ("udiv", json!([bits, max]), format!("udiv{bits}_{max}")),
            ("sdiv", json!([bits, 0]), format!("sdiv{bits}_0")),
            ("sdiv", json!([bits, max]), format!("sdiv{bits}_{max}")),
            ("urem", json!([bits]), format!("urem{bits}")),
            ("srem", json!([bits]), format!("srem{bits}")),
            ("mulh", json!([bits]), format!("mulh{bits}")),
            ("mulhu", json!([bits]), format!("mulhu{bits}")),
            ("mulhsu", json!([bits]), format!("mulhsu{bits}")),
        ];
        for (op, params, raw_stem) in rows {
            let term = format!("{raw_stem}(v{bits}:1,v{bits}:2)");
            let pred = format!(r#"{{"kind":"ret","width":{bits},"term":"{term}"}}"#);
            let rendered = normalize("{}", &pred).unwrap_or_else(|| panic!("normalize {term}"));
            assert_eq!(parse(&raw_stem, &rendered), canonical(op, params, 2), "{raw_stem}");
        }
        let select = format!("selectEq{bits}(v{bits}:1,v{bits}:2,v{bits}:3,v{bits}:4)");
        let pred = format!(r#"{{"kind":"ret","width":{bits},"term":"{select}"}}"#);
        let rendered = normalize("{}", &pred).unwrap();
        assert_eq!(parse("selectEq", &rendered), canonical("selectEq", json!([bits]), 4));
    }
    assert!(normalize("{}", r#"{"kind":"ret","width":32,"term":"udiv32_0(v32:1)"}"#).is_none());
    assert!(normalize("{}", r#"{"kind":"ret","width":32,"term":"sdiv32_0(v64:1,v32:2)"}"#).is_none());
}

fn ret_var(name: u64) -> Value {
    json!({"kind":"ret","payload":{"kind":"var","name":name}})
}
fn ret_const(value: &str) -> Value {
    json!({"kind":"ret","payload":{"kind":"c","value":value}})
}

#[test]
fn alignment_json_reports_ambiguity_complements_and_rename() {
    let cases = [
        (json!([ret_var(0), ret_var(1)]), json!([ret_var(1), ret_var(1)]), json!({"ok":false})),
        (json!([ret_const("1"), ret_const("1")]), json!([ret_const("1")]), json!({"ok":false})),
        (
            json!([ret_const("1"), ret_const("2")]),
            json!([ret_const("1"), ret_const("3")]),
            json!({"ok":true,"pass":false,"pairs":[{"left":0,"right":0}],"onlyLeft":[1],"onlyRight":[1],"subst":{"vars":[],"regs":[]}}),
        ),
        (
            json!([ret_const("1"), ret_const("3")]),
            json!([ret_const("1"), ret_const("2")]),
            json!({"ok":true,"pass":false,"pairs":[{"left":0,"right":0}],"onlyLeft":[1],"onlyRight":[1],"subst":{"vars":[],"regs":[]}}),
        ),
        (
            json!([ret_var(9)]),
            json!([ret_var(4)]),
            json!({"ok":true,"pass":true,"pairs":[{"left":0,"right":0}],"onlyLeft":[],"onlyRight":[],"subst":{"vars":[[9,4]],"regs":[]}}),
        ),
        (
            json!([ret_var(4)]),
            json!([ret_var(9)]),
            json!({"ok":true,"pass":true,"pairs":[{"left":0,"right":0}],"onlyLeft":[],"onlyRight":[],"subst":{"vars":[[4,9]],"regs":[]}}),
        ),
        (json!([ret_const("1"), ret_const("2")]), json!([ret_const("2"), ret_const("1")]), json!({"ok":false})),
    ];
    for (left, right, expected) in cases {
        let request = json!({"left": left, "right": right}).to_string();
        let actual = cross_pred::unify_json(&request).unwrap_or_else(|| panic!("{request}"));
        assert_eq!(actual, expected, "{request}");
    }
    let args = r#"[{"kind":"c","value":"7"},{"kind":"c","value":"0"}]"#;
    let left = format!(
        r#"{{"kind":"ret","payload":{{"kind":"app","op":"udiv","params":[32,0],"args":{args}}}}}"#
    );
    let right = format!(
        r#"{{"kind":"ret","payload":{{"kind":"app","op":"udiv","params":[32,4294967295],"args":{args}}}}}"#
    );
    let request = format!(r#"{{"left":[{left}],"right":[{right}]}}"#);
    let actual = cross_pred::unify_json(&request).unwrap();
    assert_eq!(actual["ok"], true);
    assert_eq!(actual["pass"], false);
    assert_eq!(actual["pairs"], json!([]));
    assert_eq!(actual["onlyLeft"], json!([0]));
    assert_eq!(actual["onlyRight"], json!([0]));
}

#[test]
fn string_ffi_steps_are_all_or_nothing() {
    let mov = sole(
        "String FFI MOV",
        &ebpf_step(&[raw_insn(0xb7, 0, 0, 0, 7), 0x95], 0, "[]"),
    );
    assert_eq!(mov["loc"], "1");
    assert_eq!(eq_term(&merged("[]", &mov), "real:0:[0,64)"), "7");
    assert!(mov["observations"].as_array().unwrap().is_empty());

    let lddw = sole(
        "String FFI LDDW",
        &ebpf_step(
            &[raw_insn(0x18, 0, 0, 0, 0x55667788), raw_insn(0, 0, 0, 0, 0x11223344), 0x95],
            0,
            "[]",
        ),
    );
    assert_eq!(lddw["loc"], "2");
    assert_eq!(eq_term(&merged("[]", lddw), "real:0:[0,64)"), "1234605616436508552");

    let failures = [
        ("illegal opcode", vec![0u64, 0x95], 0u32, "[]", "LocalReject"),
        ("r10 destination", vec![raw_insn(0xb7, 10, 0, 0, 7), 0x95], 0, "[]", "LocalReject"),
        ("immediate shift range", vec![raw_insn(0x64, 0, 0, 0, 32), 0x95], 0, "[]", "LocalReject"),
        ("reserved source field", vec![raw_insn(0xb7, 0, 1, 0, 7), 0x95], 0, "[]", "LocalReject"),
        ("invalid atomic selector", vec![raw_insn(0xc3, 10, 1, -4, 2), 0x95], 0, "[]", "LocalReject"),
        ("FETCH r10", vec![raw_insn(0xc3, 10, 10, -4, 1), 0x95], 0, "[]", "LocalReject"),
        ("missing ALU old", vec![raw_insn(0x04, 0, 0, 0, 1), 0x95], 0, "[]", "UndefinedSrc"),
        ("missing helper ABI", vec![raw_insn(0x85, 0, 0, 0, 2), 0x95], 0, "[]", "UndefinedSrc"),
        ("LDDW continuation", vec![raw_insn(0x18, 0, 0, 0, 7), 0, 0x95], 1, "[]", "LocalReject"),
        ("LDDW missing upper", vec![raw_insn(0x18, 0, 0, 0, 7)], 0, "[]", "LocalReject"),
        ("LDDW malformed upper", vec![raw_insn(0x18, 0, 0, 0, 7), raw_insn(0, 1, 0, 0, 0), 0x95], 0, "[]", "LocalReject"),
        (
            "branch all-or-nothing",
            vec![raw_insn(0x15, 0, 0, 99, 7), 0x95],
            0,
            r#"[{"reg":"real:0:[0,64)","rel":"eq","term":"v64:8"}]"#,
            "UnboundTarget",
        ),
        (
            "branch continuation all-or-nothing",
            vec![raw_insn(0x15, 0, 0, 1, 7), raw_insn(0x18, 1, 0, 0, 0), 0, 0x95],
            0,
            r#"[{"reg":"real:0:[0,64)","rel":"eq","term":"v64:8"}]"#,
            "UnboundTarget",
        ),
    ];
    for (name, words, j, exprs, reason) in failures {
        assert_fail(name, &parse(name, &ebpf::expand_step(&words, 70, j, exprs, "[]")), reason);
    }

    let dual = r#"[{"reg":"real:0:[0,64)","rel":"eq","term":"1"},{"reg":"real:0:[0,64)","rel":"eq","term":"2"}]"#;
    let kept = sole(
        "dual eq",
        &ebpf_step(&[raw_insn(0xb7, 1, 0, 0, 0), 0x95], 0, dual),
    );
    let kept_state = merged(dual, kept);
    assert_eq!(eq_term(&kept_state, "real:0:[0,64)"), "1");
    let constraints: Vec<&Value> = kept_state["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row["role"] == "constraint")
        .collect();
    assert_eq!(constraints.len(), 1);
    assert_eq!(constraints[0]["term"], "2");
    let overwritten = sole(
        "MOV after dual eq",
        &ebpf_step(&[raw_insn(0xb7, 0, 0, 0, 7), 0x95], 0, dual),
    );
    let overwritten_state = merged(dual, overwritten);
    assert_eq!(eq_term(&overwritten_state, "real:0:[0,64)"), "7");
    assert!(overwritten_state["exprs"]
        .as_array()
        .unwrap()
        .iter()
        .all(|row| row["role"] != "constraint"));

    let exit_parent = regs64(&[(0, "7")]);
    let exit = sole("EXIT", &ebpf_step(&[0x95], 0, &exit_parent));
    assert_eq!(exit["loc"], "exit");
    assert_eq!(
        exit["observations"],
        json!([{"kind":"ret","width":64,"term":"7"}])
    );
    assert_eq!(eq_term(&merged(&exit_parent, exit), "real:0:[0,64)"), "7");

    let rv_parent = regs32(&[(8, "v32:41"), (9, "v32:42")]);
    let open = sole("RV open M", &rv_step(&[rv_m_word(5), 0x0001], &rv_parent));
    assert_eq!(open["loc"], "1");
    let open_state = merged(&rv_parent, open);
    assert_eq!(eq_term(&open_state, "real:8:[0,32)"), "v32:41");
    assert_eq!(eq_term(&open_state, "real:9:[0,32)"), "v32:42");
    assert_eq!(
        eq_term(&open_state, "real:10:[0,32)"),
        "udiv32_4294967295(v32:41,v32:42)"
    );
    assert_fail(
        "RV illegal",
        &rv_step(&[0xffff_ffff, 0x0001], "[]"),
        "LocalReject",
    );
}

fn root_state(raw: &str) -> (String, String) {
    let value = parse("create", raw);
    let node = &value["nodes"][0];
    (node["exprs"].to_string(), node["predicates"].to_string())
}

#[test]
fn mov_exit_snapshot_runs_then_completes() {
    let (exprs, preds) = root_state(&ebpf::expand_create(&Create {
        t_ctx: "v64:1",
        t_sp: "v64:0",
        t_data: "v32:2",
        packet_bytes: 64,
        alpha_ctx: 0,
        packet_id: 0,
        stack_id: 0,
        slots: &[],
        terms: &[],
        map_ids: &[],
        key_sizes: &[],
        value_sizes: &[],
    }));
    let program = [raw_insn(0xb7, 0, 0, 0, 7), 0x95];
    for (steps, status, location, observations, pending) in [
        (1u32, "running", "1", json!([]), vec!["1"]),
        (2, "complete", "exit", json!([{"kind":"ret","width":64,"term":"7"}]), vec![]),
    ] {
        let snap = parse(
            status,
            &ebpf::expand_bound_words_snapshot(&program, &exprs, &preds, steps, 4),
        );
        assert_eq!(snap["status"], status);
        assert!(snap["reason"].is_null());
        assert!(snap["failed"].is_null());
        let nodes = snap["nodes"].as_array().unwrap();
        let work_locs: Vec<String> = snap["work"]
            .as_array()
            .unwrap()
            .iter()
            .map(|id| {
                let id = id.as_u64().unwrap();
                nodes
                    .iter()
                    .find(|node| node["id"] == id)
                    .unwrap()["loc"]
                    .as_str()
                    .unwrap()
                    .to_string()
            })
            .collect();
        assert_eq!(work_locs, pending);
        let node = nodes.iter().find(|node| node["loc"] == location).unwrap();
        assert_eq!(eq_term(node, "real:0:[0,64)"), "7");
        assert_eq!(node["predicates"], observations);
    }
}

const JUST_TX: [u64; 58] = [
    0x00000001000000b4, 0x0000000000041261, 0x0000000000001661, 0x00000000000061bf,
    0x0000000e00000107, 0x000000000033212d, 0x00000000000c6469, 0x0000008100020416,
    0x0000000e000003b7, 0x0000a88800050456, 0x00000000000063bf, 0x0000001200000307,
    0x00000000002c232d, 0x00000012000003b7, 0x0000000000021469, 0x00000000000001b4,
    0x0000dd8600080416, 0x00000008000d0456, 0x00000000000064bf, 0x000000000000340f,
    0x00000000000043bf, 0x0000001400000307, 0x000000000008232d, 0x0000000000094171,
    0x0000000000060005, 0x00000000000064bf, 0x000000000000340f, 0x00000000000043bf,
    0x0000002800000307, 0x000000000001232d, 0x0000000000064171, 0x00000000fffc1a63,
    0x000000000000a2bf, 0xfffffffc00000207, 0x0000000000000118, 0x0000000000000000,
    0x0000000100000085, 0x0000000000030015, 0x0000000000000179, 0x0000000100000107,
    0x000000000000107b, 0x00000000fffca161, 0x00000001000000b4, 0x00000011000d0156,
    0x0000000000006169, 0x0000000000066269, 0x000000000000266b, 0x0000000000086269,
    0x0000000000026369, 0x000000000008366b, 0x000000000002266b, 0x00000000000a6269,
    0x0000000000046369, 0x00000000000a366b, 0x000000000006166b, 0x000000000004266b,
    0x00000003000000b4, 0x0000000000000095,
];

const RV_FIXTURE: [u32; 76] = [
    4417, 50694, 50210, 49702, 2048, 16644, 16716, 14976531, 17669, 180744035, 12899843, 26285,
    2290517651, 14026339, 135267987, 14031459, 19170835, 180740195, 17094147, 17737, 40977, 17721,
    26297, 3630597779, 14028131, 18081, 14032739, 38182, 21300755, 12970595, 9782531, 41017, 38182,
    42272275, 113638243, 17665, 49194, 1077413303, 780502419, 17669, 34314, 18049, 18177, 18305,
    13121, 34218, 17669, 51593, 16784, 16852, 1541, 1455891, 38586, 49552, 49620, 17794, 17989,
    46504803, 6591747, 8689027, 10786307, 300675, 2397955, 4495235, 10784803, 11833635, 12882467,
    13931299, 14980131, 16028963, 17677, 16562, 17442, 17554, 321, 32898,
];

#[test]
fn just_tx_finite_product_regressions() {
    let (exprs, preds) = root_state(&ebpf::expand_create(&Create {
        t_ctx: "v64:1",
        t_sp: "v64:0",
        t_data: "v32:4",
        packet_bytes: 128,
        alpha_ctx: 0,
        packet_id: 0,
        stack_id: 0,
        slots: &[34],
        terms: &[1077412584],
        map_ids: &[1077412584],
        key_sizes: &[4],
        value_sizes: &[8],
    }));
    let snap = parse(
        "just_tx eBPF",
        &ebpf::expand_bound_words_snapshot(&JUST_TX, &exprs, &preds, 2000, 1024),
    );
    assert_eq!(
        snap["status"], "complete",
        "reason={} failed={}",
        snap["reason"], snap["failed"]
    );
    let returns_three = snap["nodes"].as_array().unwrap().iter().any(|node| {
        node["loc"] == "exit"
            && node["predicates"].as_array().is_some_and(|preds| {
                preds.iter().any(|pred| pred["kind"] == "ret" && pred["term"] == "3")
            })
    });
    assert!(returns_three, "{}", snap["nodes"]);

    let rv_root = parse(
        "rv create",
        &rv32::expand_create(1077412352, 1077411840, 8192, &[1077412584], &[4], &[8]),
    );
    let rv_node = &rv_root["nodes"][0];
    let rv_snap = parse(
        "just_tx RV",
        &rv32::expand_bound_words_snapshot(
            &RV_FIXTURE,
            &rv_node["exprs"].to_string(),
            &rv_node["predicates"].to_string(),
            400,
            400,
        ),
    );
    let nodes = rv_snap["nodes"].as_array().unwrap();
    let failed = nodes.iter().find(|node| node["id"] == rv_snap["failed"]);
    let reached34 = nodes.iter().any(|node| node["loc"] == "34");
    assert_eq!(
        rv_snap["status"], "complete",
        "stepping loc {} returned {}: nodes={} reached34={reached34}",
        failed.and_then(|node| node["loc"].as_str()).unwrap_or("?"),
        rv_snap["reason"],
        nodes.len()
    );
    assert!(rv_snap["reason"].is_null());
    assert_eq!(nodes.len(), 146);
    assert!(!reached34);
}
