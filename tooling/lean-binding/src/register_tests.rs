use super::{ffi, init};
use serde_json::Value;
use std::ffi::CStr;

unsafe fn json_result(obj: *mut std::os::raw::c_void) -> Value {
    let text = unsafe { CStr::from_ptr(ffi::lean_binding_string_cstr(obj)) }
        .to_string_lossy()
        .into_owned();
    unsafe { ffi::lean_binding_dec(obj) };
    serde_json::from_str(&text).expect("Lean register-effect JSON")
}

#[allow(clippy::too_many_arguments)]
fn cell(
    kind: u32,
    width: u32,
    old: Option<u64>,
    offset: u32,
    bits: u32,
    source_width: u32,
    unsigned: bool,
    source: Option<u64>,
) -> Value {
    init();
    unsafe {
        json_result(ffi::lean_virtual_cell_access(
            kind,
            width,
            u32::from(old.is_some()),
            offset,
            bits,
            source_width,
            u32::from(unsigned),
            u32::from(source.is_some()),
            old.unwrap_or(0),
            source.unwrap_or(0),
        ))
    }
}

#[allow(clippy::too_many_arguments)]
fn packet(
    values: &[u32],
    resource: u32,
    offset: u32,
    bytes: u32,
    width: u32,
    big_endian: bool,
    unsigned: bool,
    input: bool,
    source: Option<u64>,
) -> Value {
    init();
    unsafe {
        let values = ffi::lean_binding_mk_uint32_array(values.as_ptr(), values.len());
        json_result(ffi::lean_virtual_packet_access(
            values,
            resource,
            offset,
            bytes,
            width,
            u32::from(big_endian),
            u32::from(unsigned),
            u32::from(input),
            u32::from(source.is_some()),
            source.unwrap_or(0),
        ))
    }
}

fn rv32_case(case_id: u32, value: u32) -> Value {
    init();
    unsafe { json_result(ffi::lean_rv32_register_effects(case_id, value)) }
}

fn term<'a>(exprs: &'a Value, reg: &str) -> &'a str {
    exprs
        .as_array()
        .expect("expressions")
        .iter()
        .find(|e| e["reg"] == reg)
        .expect("register")["term"]
        .as_str()
        .expect("term")
}

#[test]
fn stack_and_map_fields_preserve_other_bits_and_require_old_values() {
    for kind in [0, 1] {
        let r = if kind == 0 { "stack64:7" } else { "map64:7" };
        let result = cell(
            kind,
            64,
            Some(0x8877_6655_4433_2211),
            16,
            16,
            32,
            true,
            Some(0xeeff),
        );
        assert_eq!(
            term(&result["updates"], r),
            0x8877_6655_eeff_2211u64.to_string()
        );
        assert_eq!(
            cell(
                kind,
                64,
                Some(0x8877_6655_4433_2211),
                16,
                16,
                32,
                true,
                None
            )["value"],
            "17459"
        ); // 0x4433
        assert_eq!(
            cell(kind, 32, Some(0x80), 0, 8, 64, false, None)["value"],
            (u64::MAX - 127).to_string()
        );
        assert!(cell(kind, 64, None, 8, 8, 32, true, Some(1)).is_null());
        let full = cell(kind, 64, None, 0, 64, 64, true, Some(u64::MAX));
        assert_eq!(term(&full["updates"], r), u64::MAX.to_string());
        assert!(cell(kind, 64, Some(0), 56, 16, 32, true, Some(1)).is_null());
    }
}

#[test]
fn packet_bytes_pack_and_split_in_both_orders_without_packet64() {
    let bytes = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88];
    let little = packet(&bytes, 7, 0, 8, 64, false, true, false, None);
    let big = packet(&bytes, 7, 0, 8, 64, true, true, false, None);
    assert_eq!(little["value"], 0x8877_6655_4433_2211u64.to_string());
    assert_eq!(big["value"], 0x1122_3344_5566_7788u64.to_string());
    assert!(little["inputs"].as_array().unwrap().is_empty());
    assert!(packet(&bytes, 7, 0, 8, 32, false, true, false, None).is_null());
    assert_eq!(
        packet(&[0, 0x80], 7, 1, 1, 64, false, false, false, None)["value"],
        (u64::MAX - 127).to_string()
    );
    for big_endian in [false, true] {
        let write = packet(
            &[],
            7,
            3,
            8,
            64,
            big_endian,
            true,
            false,
            Some(0x8877_6655_4433_2211),
        );
        let updates = write["updates"].as_array().unwrap();
        assert_eq!(updates.len(), 8);
        assert!(
            updates
                .iter()
                .all(|e| e["reg"].as_str().unwrap().starts_with("packet32:"))
        );
        assert_eq!(
            term(&write["updates"], "packet32:58"),
            if big_endian { "136" } else { "17" }
        );
        assert_eq!(
            term(&write["updates"], "packet32:97"),
            if big_endian { "85" } else { "68" }
        );
    }
    let a = packet(&[], 7, 3, 1, 32, false, true, true, None);
    let b = packet(&[], 8, 3, 1, 32, false, true, true, None);
    assert_eq!(a["inputs"][0]["reg"], "packet32:58");
    assert_ne!(a["inputs"][0]["reg"], b["inputs"][0]["reg"]);
    assert!(a["value"].as_str().unwrap().contains("inputByte"));
}

#[test]
fn rv32_unaligned_packet_overlap_uses_current_bytes_and_preserves_old_load() {
    let result = rv32_case(0, 0x80ff);
    assert!(!result.is_null());
    assert_eq!(result["first"]["inputs"].as_array().unwrap().len(), 4);
    assert_eq!(result["first"]["updates"].as_array().unwrap().len(), 1);
    assert_eq!(result["first"]["updates"][0]["reg"], "real32:14");
    assert!(result["store"]["inputs"].as_array().unwrap().is_empty());
    assert_eq!(result["store"]["updates"].as_array().unwrap().len(), 2);
    assert_eq!(term(&result["state"], "packet32:20"), "255"); // byte 5, resource 0
    assert_eq!(term(&result["state"], "packet32:27"), "128"); // byte 6
    assert!(result["reload"]["inputs"].as_array().unwrap().is_empty());
    let old = term(&result["state"], "real32:14");
    let new = term(&result["state"], "real32:15");
    assert_eq!(old, term(&result["first"]["updates"], "real32:14"));
    assert_ne!(old, new);
    assert!(old.contains("add32(v32:4,5)"));
    assert!(!new.contains("add32(v32:4,5)"));
    assert!(!new.contains("add32(v32:4,6)"));
    assert_eq!(term(&result["state"], "real32:17"), "4294967295");
    assert_eq!(term(&result["state"], "real32:13"), "33023");
    assert_eq!(
        result["compressedStore"]["updates"]
            .as_array()
            .unwrap()
            .len(),
        4
    );
    assert!(
        result["compressedRead"]["inputs"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        term(&result["compressedRead"]["updates"], "real32:9"),
        "33023"
    );
}

#[test]
fn rv32_stack_alias_subword_store_preserves_the_rest_of_the_word() {
    let result = rv32_case(1, 0xdd);
    assert_eq!(
        term(&result["byte"]["updates"], "stack32:8589934592"),
        0x1122_dd44u32.to_string()
    );
    assert_eq!(term(&result["read"]["updates"], "real32:14"), "8925"); // 0x22dd
    assert_eq!(result["crossesRejected"], true);
}

#[test]
fn resource_classification_rejects_missing_or_ambiguous_bindings() {
    let result = rv32_case(2, 0);
    let checks = result.as_object().expect("rejection checks");
    assert_eq!(checks.len(), 12);
    for (name, passed) in checks {
        assert_eq!(passed, &Value::Bool(true), "{name}");
    }
}
