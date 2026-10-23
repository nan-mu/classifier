//! Thin Rust interface over Lean `@[export]` symbols from `Core`,
//! `Node`, `RV32`, and `EBPF`.
//!
//! FFI runs on a fixed pool of [`LEAN_WORKERS`] Lean-initialized OS threads
//! (`lean_initialize_thread`). The process runtime is initialized once; there is
//! no global Lean mutex.

use std::sync::Once;

static INIT: Once = Once::new();

mod pool;

pub use pool::{lean_call, LEAN_WORKERS};

pub(crate) mod ffi {
    use std::os::raw::{c_char, c_uchar, c_void};

    pub type LeanObj = *mut c_void;

    unsafe extern "C" {
        pub fn lean_initialize_runtime_module();
        pub fn lean_initialize();
        pub fn lean_io_mark_end_initialization();
        pub fn lean_initialize_thread();
        pub fn lean_finalize_thread();

        pub fn initialize_Init(builtin: c_uchar, world: LeanObj) -> LeanObj;
        pub fn initialize_classifier_Core(builtin: c_uchar, world: LeanObj) -> LeanObj;
        pub fn initialize_classifier_Node(builtin: c_uchar, world: LeanObj) -> LeanObj;
        pub fn initialize_classifier_RV32(builtin: c_uchar, world: LeanObj) -> LeanObj;
        pub fn initialize_classifier_EBPF(builtin: c_uchar, world: LeanObj) -> LeanObj;

        // Inlines from lean.h, exported by shim.c
        pub fn lean_binding_string_cstr(o: LeanObj) -> *const c_char;
        pub fn lean_binding_mk_string(utf8: *const c_char) -> LeanObj;
        pub fn lean_binding_dec(o: LeanObj);
        pub fn lean_binding_mk_uint32_array(data: *const u32, len: usize) -> LeanObj;
        pub fn lean_binding_mk_uint64_array(data: *const u64, len: usize) -> LeanObj;

        pub fn classifier_expr_add32(a: u32, b: u32) -> u32;
        pub fn classifier_expr_sub32(a: u32, b: u32) -> u32;
        pub fn classifier_expr_and32(a: u32, b: u32) -> u32;
        pub fn classifier_expr_tq32(a: u32, b: u32) -> u32;
        pub fn classifier_expr_divu32(a: u32, b: u32) -> u32;
        pub fn lean_rv32_expr_override_keeps(unused: u32) -> u32;

        pub fn lean_rv32_decode32(w: u32) -> u32;
        pub fn lean_rv32_decode16(h: u32) -> u32;
        pub fn lean_rv32_value_addi(rs1_val: u32, imm: u32, rs1: u32, rd: u32) -> u32;
        pub fn lean_rv32_value_add(rs1_val: u32, rs2_val: u32, rs1: u32, rs2: u32, rd: u32) -> u32;
        pub fn lean_rv32_value_auipc(pc: u32, uimm20: u32, rd: u32) -> u32;
        pub fn lean_rv32_value_lui(uimm20: u32, rd: u32) -> u32;
        pub fn lean_rv32_value_div(rs1_val: u32, rs2_val: u32) -> u32;
        pub fn lean_rv32_value_ecall_rejects(unused: u32) -> u32;
        #[link_name = "lean_rv32_expand_builtin_snapshot"]
        pub fn lean_rv32_expand_builtin_snapshot(steps: u32, budget: u32) -> LeanObj;
        pub fn lean_rv32_expand_bound_words_snapshot(
            insns: LeanObj,
            exprs_json: LeanObj,
            preds_json: LeanObj,
            steps: u32,
            budget: u32,
        ) -> LeanObj;
        pub fn lean_rv32_expand_words_snapshot(insns: LeanObj, steps: u32, budget: u32) -> LeanObj;
        pub fn lean_rv32_expand_create(
            base: u32,
            helper: u32,
            wrapper_return: u32,
            map_ids: LeanObj,
            key_sizes: LeanObj,
            value_sizes: LeanObj,
        ) -> LeanObj;
        pub fn lean_rv32_expand_step(
            insns: LeanObj,
            event: u32,
            j: u32,
            exprs_json: LeanObj,
            preds_json: LeanObj,
        ) -> LeanObj;
        /// HelperOnly ExactConfig merge (`Node/Merge.lean`).
        pub fn lean_expand_merge(request_json: LeanObj) -> LeanObj;
        pub fn lean_expand_update(
            local_exprs: LeanObj,
            local_preds: LeanObj,
            step_exprs: LeanObj,
            step_preds: LeanObj,
        ) -> LeanObj;

        pub fn lean_ebpf_expand_create(
            t_ctx: LeanObj,
            t_sp: LeanObj,
            t_data: LeanObj,
            packet_bytes: u32,
            alpha_ctx: u32,
            packet_id: u32,
            stack_id: u32,
            slots: LeanObj,
            terms: LeanObj,
            map_ids: LeanObj,
            key_sizes: LeanObj,
            value_sizes: LeanObj,
        ) -> LeanObj;
        pub fn lean_ebpf_expand_step(
            insns: LeanObj,
            event: u32,
            j: u32,
            exprs_json: LeanObj,
            preds_json: LeanObj,
        ) -> LeanObj;
        pub fn lean_ebpf_expand_bound_words_snapshot(
            insns: LeanObj,
            exprs_json: LeanObj,
            preds_json: LeanObj,
            steps: u32,
            budget: u32,
        ) -> LeanObj;

        /// Structural same/diff of two run snapshots (`Node/Compare.lean`).
        pub fn lean_compare_run_same_diff(request_json: LeanObj) -> LeanObj;

        /// CrossPred normalize (`Core.exportCrossPredNormalize`).
        /// Success is CrossPred JSON. Failure is the four characters `null`.
        pub fn lean_cross_pred_normalize(env_json: LeanObj, pred_json: LeanObj) -> LeanObj;

        /// CrossPred unify (`Core.exportCrossPredUnify`).
        /// Success is unify JSON. Failure is the four characters `null`.
        pub fn lean_cross_pred_unify(request_json: LeanObj) -> LeanObj;
    }

    #[cfg(test)]
    unsafe extern "C" {
        pub fn lean_virtual_cell_access(
            kind: u32,
            width: u32,
            has_old: u32,
            bit_offset: u32,
            bits: u32,
            source_width: u32,
            is_unsigned: u32,
            write: u32,
            old: u64,
            source: u64,
        ) -> LeanObj;
        pub fn lean_virtual_packet_access(
            values: LeanObj,
            resource: u32,
            offset: u32,
            bytes: u32,
            width: u32,
            big_endian: u32,
            is_unsigned: u32,
            allow_input: u32,
            write: u32,
            source: u64,
        ) -> LeanObj;
        pub fn lean_rv32_register_effects(case_id: u32, value: u32) -> LeanObj;
    }
}

#[cfg(test)]
mod register_tests;

/// Initialize the Lean runtime and classifier modules once per process.
pub fn init() {
    INIT.call_once(|| unsafe {
        ffi::lean_initialize_runtime_module();
        ffi::lean_initialize();
        let world = std::ptr::null_mut();
        let _ = ffi::initialize_Init(1, world);
        let _ = ffi::initialize_classifier_Core(1, world);
        let _ = ffi::initialize_classifier_Node(1, world);
        let _ = ffi::initialize_classifier_RV32(1, world);
        let _ = ffi::initialize_classifier_EBPF(1, world);
        ffi::lean_io_mark_end_initialization();
    });
}

pub mod expand {
    use super::{ffi, lean_call, rv32};
    use std::ffi::{CStr, CString};

    /// HelperOnly ExactConfig merge (request JSON only).
    pub fn merge(request_json: &str) -> String {
        rv32::expand_merge(request_json)
    }

    /// Compose one step increment onto a stored node. The two JSON shapes differ.
    pub fn update(
        local_exprs: &str,
        local_preds: &str,
        step_writes: &str,
        step_observations: &str,
    ) -> String {
        let local_exprs = local_exprs.to_owned();
        let local_preds = local_preds.to_owned();
        let step_writes = step_writes.to_owned();
        let step_observations = step_observations.to_owned();
        lean_call(move || unsafe {
            let local_exprs = lean_string(&local_exprs);
            let local_preds = lean_string(&local_preds);
            let step_writes = lean_string(&step_writes);
            let step_observations = lean_string(&step_observations);
            take_string(ffi::lean_expand_update(
                local_exprs,
                local_preds,
                step_writes,
                step_observations,
            ))
        })
    }

    unsafe fn take_string(obj: ffi::LeanObj) -> String {
        let s = CStr::from_ptr(ffi::lean_binding_string_cstr(obj))
            .to_string_lossy()
            .into_owned();
        ffi::lean_binding_dec(obj);
        s
    }

    unsafe fn lean_string(s: &str) -> ffi::LeanObj {
        let c = CString::new(s).expect("JSON contains NUL");
        ffi::lean_binding_mk_string(c.as_ptr())
    }
}

pub mod classifier_expr {
    use super::{ffi, lean_call};

    pub fn add32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::classifier_expr_add32(a, b) })
    }

    pub fn sub32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::classifier_expr_sub32(a, b) })
    }

    pub fn and32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::classifier_expr_and32(a, b) })
    }

    pub fn tq32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::classifier_expr_tq32(a, b) })
    }

    pub fn divu32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::classifier_expr_divu32(a, b) })
    }
}

pub mod rv32 {
    use super::{ffi, lean_call};
    use std::ffi::CStr;

    /// Instruction tags matching `RV32.insnTag`.
    pub mod tag {
        pub const ILLEGAL: u32 = 0;
        pub const LUI: u32 = 2;
        pub const AUIPC: u32 = 3;
        pub const ADDI: u32 = 7;
        pub const ADD: u32 = 16;
        pub const MUL: u32 = 36;
        pub const DIV: u32 = 40;
        pub const ECALL: u32 = 30;
        pub const C_NOP: u32 = 44;
    }

    pub fn decode32(word: u32) -> u32 {
        lean_call(move || unsafe { ffi::lean_rv32_decode32(word) })
    }

    pub fn decode16(half: u32) -> u32 {
        lean_call(move || unsafe { ffi::lean_rv32_decode16(half) })
    }

    pub fn value_addi(rs1_val: u32, imm: u32, rs1: u32, rd: u32) -> u32 {
        lean_call(move || unsafe { ffi::lean_rv32_value_addi(rs1_val, imm, rs1, rd) })
    }

    pub fn value_add(rs1_val: u32, rs2_val: u32, rs1: u32, rs2: u32, rd: u32) -> u32 {
        lean_call(move || unsafe { ffi::lean_rv32_value_add(rs1_val, rs2_val, rs1, rs2, rd) })
    }

    pub fn value_auipc(pc: u32, uimm20: u32, rd: u32) -> u32 {
        lean_call(move || unsafe { ffi::lean_rv32_value_auipc(pc, uimm20, rd) })
    }

    pub fn value_lui(uimm20: u32, rd: u32) -> u32 {
        lean_call(move || unsafe { ffi::lean_rv32_value_lui(uimm20, rd) })
    }

    pub fn value_div(rs1_val: u32, rs2_val: u32) -> u32 {
        lean_call(move || unsafe { ffi::lean_rv32_value_div(rs1_val, rs2_val) })
    }

    pub fn ecall_rejects() -> bool {
        lean_call(|| unsafe { ffi::lean_rv32_value_ecall_rejects(0) == 1 })
    }

    pub fn expr_override_keeps() -> bool {
        lean_call(|| unsafe { ffi::lean_rv32_expr_override_keeps(0) == 1 })
    }

    /// JSON after `steps` expandOne calls on the Lean smoke program (`rv32Snapshot`).
    pub fn expand_snapshot(steps: u32, budget: u32) -> String {
        lean_call(move || unsafe {
            let obj = ffi::lean_rv32_expand_builtin_snapshot(steps, budget);
            take_string(obj)
        })
    }

    /// JSON after `steps` expandOne calls on a caller-supplied instruction word list.
    pub fn expand_words_snapshot(insns: &[u32], steps: u32, budget: u32) -> String {
        let insns = insns.to_vec();
        lean_call(move || unsafe {
            let arr = ffi::lean_binding_mk_uint32_array(insns.as_ptr(), insns.len());
            let obj = ffi::lean_rv32_expand_words_snapshot(arr, steps, budget);
            take_string(obj)
        })
    }

    unsafe fn take_string(obj: ffi::LeanObj) -> String {
        let s = CStr::from_ptr(ffi::lean_binding_string_cstr(obj))
            .to_string_lossy()
            .into_owned();
        ffi::lean_binding_dec(obj);
        s
    }

    /// Static Map layout for lookup key freeze / MapWrite bounds (Lean `MapLayout`).
    #[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct MapLayout {
        pub map_id: u32,
        pub key_size: u32,
        pub value_size: u32,
    }

    unsafe fn lean_string(s: &str) -> ffi::LeanObj {
        use std::ffi::CString;
        let c = CString::new(s).expect("JSON contains NUL");
        ffi::lean_binding_mk_string(c.as_ptr())
    }

    pub fn expand_bound_words_snapshot(
        insns: &[u32],
        exprs_json: &str,
        preds_json: &str,
        steps: u32,
        budget: u32,
    ) -> String {
        let insns = insns.to_vec();
        let exprs_json = exprs_json.to_owned();
        let preds_json = preds_json.to_owned();
        lean_call(move || unsafe {
            let arr = ffi::lean_binding_mk_uint32_array(insns.as_ptr(), insns.len());
            let exprs = lean_string(&exprs_json);
            let preds = lean_string(&preds_json);
            let obj = ffi::lean_rv32_expand_bound_words_snapshot(arr, exprs, preds, steps, budget);
            take_string(obj)
        })
    }

    /// Entry state plus anchors. Program image and fuel stay in the server engine.
    pub fn expand_create(
        base: u32,
        helper: u32,
        wrapper_return: u32,
        map_ids: &[u32],
        key_sizes: &[u32],
        value_sizes: &[u32],
    ) -> String {
        let map_ids = map_ids.to_vec();
        let key_sizes = key_sizes.to_vec();
        let value_sizes = value_sizes.to_vec();
        lean_call(move || unsafe {
            let map_ids = ffi::lean_binding_mk_uint32_array(map_ids.as_ptr(), map_ids.len());
            let key_sizes = ffi::lean_binding_mk_uint32_array(key_sizes.as_ptr(), key_sizes.len());
            let value_sizes =
                ffi::lean_binding_mk_uint32_array(value_sizes.as_ptr(), value_sizes.len());
            take_string(ffi::lean_rv32_expand_create(
                base,
                helper,
                wrapper_return,
                map_ids,
                key_sizes,
                value_sizes,
            ))
        })
    }

    /// Stateless head inference. Anchors travel in `exprs_json`.
    /// Graph / fuel / work-queue ownership lives in the server expand engine.
    pub fn expand_step(
        insns: &[u32],
        event: u32,
        j: u32,
        exprs_json: &str,
        preds_json: &str,
    ) -> String {
        let insns = insns.to_vec();
        let exprs_json = exprs_json.to_owned();
        let preds_json = preds_json.to_owned();
        lean_call(move || unsafe {
            let arr = ffi::lean_binding_mk_uint32_array(insns.as_ptr(), insns.len());
            let exprs = lean_string(&exprs_json);
            let preds = lean_string(&preds_json);
            take_string(ffi::lean_rv32_expand_step(arr, event, j, exprs, preds))
        })
    }

    /// HelperOnly ExactConfig merge. Request JSON only.
    /// See `doc/NodeInference/路径合并FFI.md`.
    pub fn expand_merge(request_json: &str) -> String {
        let request_json = request_json.to_owned();
        lean_call(move || unsafe {
            let req = lean_string(&request_json);
            take_string(ffi::lean_expand_merge(req))
        })
    }
}

/// eBPF budget expand FFI (`lean_ebpf_expand_*`). Insn slots are `Array UInt64`.
pub mod ebpf {
    use super::{ffi, lean_call};
    use std::ffi::CStr;

    /// Same wire record as `rv32::MapLayout`. Fields are mapId, keySize, and valueSize.
    pub type MapLayout = super::rv32::MapLayout;

    /// Symbolic entry passed at the HTTP/kernel create boundary.
    pub const T_CTX: &str = "v64:1";
    pub const T_SP: &str = "v64:0";
    pub const T_DATA: &str = "v32:4";
    pub const PACKET_BYTES: u32 = 128;

    /// One create request: symbolic entry, LDDW slot terms, and map layouts.
    /// Written into the root snapshot as anchors. Not a session store.
    pub struct Create<'a> {
        pub t_ctx: &'a str,
        pub t_sp: &'a str,
        pub t_data: &'a str,
        pub packet_bytes: u32,
        pub alpha_ctx: u32,
        pub packet_id: u32,
        pub stack_id: u32,
        pub slots: &'a [u32],
        pub terms: &'a [u64],
        pub map_ids: &'a [u32],
        pub key_sizes: &'a [u32],
        pub value_sizes: &'a [u32],
    }

    unsafe fn take_string(obj: ffi::LeanObj) -> String {
        let s = CStr::from_ptr(ffi::lean_binding_string_cstr(obj))
            .to_string_lossy()
            .into_owned();
        ffi::lean_binding_dec(obj);
        s
    }

    unsafe fn lean_string(s: &str) -> ffi::LeanObj {
        use std::ffi::CString;
        let c = CString::new(s).expect("JSON contains NUL");
        ffi::lean_binding_mk_string(c.as_ptr())
    }

    pub fn expand_create(args: &Create<'_>) -> String {
        let t_ctx = args.t_ctx.to_owned();
        let t_sp = args.t_sp.to_owned();
        let t_data = args.t_data.to_owned();
        let packet_bytes = args.packet_bytes;
        let alpha_ctx = args.alpha_ctx;
        let packet_id = args.packet_id;
        let stack_id = args.stack_id;
        let slots = args.slots.to_vec();
        let terms = args.terms.to_vec();
        let map_ids = args.map_ids.to_vec();
        let key_sizes = args.key_sizes.to_vec();
        let value_sizes = args.value_sizes.to_vec();
        lean_call(move || unsafe {
            let t_ctx = lean_string(&t_ctx);
            let t_sp = lean_string(&t_sp);
            let t_data = lean_string(&t_data);
            let slots = ffi::lean_binding_mk_uint32_array(slots.as_ptr(), slots.len());
            let terms = ffi::lean_binding_mk_uint64_array(terms.as_ptr(), terms.len());
            let map_ids = ffi::lean_binding_mk_uint32_array(map_ids.as_ptr(), map_ids.len());
            let key_sizes = ffi::lean_binding_mk_uint32_array(key_sizes.as_ptr(), key_sizes.len());
            let value_sizes =
                ffi::lean_binding_mk_uint32_array(value_sizes.as_ptr(), value_sizes.len());
            take_string(ffi::lean_ebpf_expand_create(
                t_ctx,
                t_sp,
                t_data,
                packet_bytes,
                alpha_ctx,
                packet_id,
                stack_id,
                slots,
                terms,
                map_ids,
                key_sizes,
                value_sizes,
            ))
        })
    }

    pub fn expand_step(
        insns: &[u64],
        event: u32,
        j: u32,
        exprs_json: &str,
        preds_json: &str,
    ) -> String {
        let insns = insns.to_vec();
        let exprs_json = exprs_json.to_owned();
        let preds_json = preds_json.to_owned();
        lean_call(move || unsafe {
            let arr = ffi::lean_binding_mk_uint64_array(insns.as_ptr(), insns.len());
            let exprs = lean_string(&exprs_json);
            let preds = lean_string(&preds_json);
            take_string(ffi::lean_ebpf_expand_step(arr, event, j, exprs, preds))
        })
    }

    pub fn expand_bound_words_snapshot(
        insns: &[u64],
        exprs_json: &str,
        preds_json: &str,
        steps: u32,
        budget: u32,
    ) -> String {
        let insns = insns.to_vec();
        let exprs_json = exprs_json.to_owned();
        let preds_json = preds_json.to_owned();
        lean_call(move || unsafe {
            let arr = ffi::lean_binding_mk_uint64_array(insns.as_ptr(), insns.len());
            let exprs = lean_string(&exprs_json);
            let preds = lean_string(&preds_json);
            take_string(ffi::lean_ebpf_expand_bound_words_snapshot(
                arr, exprs, preds, steps, budget,
            ))
        })
    }
}

/// Structural cross-arch compare (`lean_compare_run_same_diff`).
pub mod compare {
    use super::{ffi, lean_call};
    use std::ffi::CStr;

    unsafe fn take_string(obj: ffi::LeanObj) -> String {
        let s = CStr::from_ptr(ffi::lean_binding_string_cstr(obj))
            .to_string_lossy()
            .into_owned();
        ffi::lean_binding_dec(obj);
        s
    }

    unsafe fn lean_string(s: &str) -> ffi::LeanObj {
        use std::ffi::CString;
        let c = CString::new(s).expect("JSON contains NUL");
        ffi::lean_binding_mk_string(c.as_ptr())
    }

    /// Request JSON: `{ "left": { arch, nodes, edges }, "right": { ... } }`.
    pub fn run_same_diff(request_json: &str) -> String {
        let request_json = request_json.to_owned();
        lean_call(move || unsafe {
            let req = lean_string(&request_json);
            take_string(ffi::lean_compare_run_same_diff(req))
        })
    }
}

/// CrossPred normalize (`lean_cross_pred_normalize`).
pub mod cross_pred {
    use super::{ffi, lean_call};
    use std::ffi::CStr;

    unsafe fn take_string(obj: ffi::LeanObj) -> String {
        let s = CStr::from_ptr(ffi::lean_binding_string_cstr(obj))
            .to_string_lossy()
            .into_owned();
        ffi::lean_binding_dec(obj);
        s
    }

    unsafe fn lean_string(s: &str) -> ffi::LeanObj {
        use std::ffi::CString;
        let c = CString::new(s).expect("JSON contains NUL");
        ffi::lean_binding_mk_string(c.as_ptr())
    }

    /// `None` when Lean returns the ABI failure marker `null`.
    pub fn normalize(env_json: &str, pred_json: &str) -> Option<String> {
        let env_json = env_json.to_owned();
        let pred_json = pred_json.to_owned();
        let raw = lean_call(move || unsafe {
            let env = lean_string(&env_json);
            let pred = lean_string(&pred_json);
            take_string(ffi::lean_cross_pred_normalize(env, pred))
        });
        if raw == "null" {
            None
        } else {
            Some(raw)
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct UnifyResult {
        pub ok: bool,
        pub pass: bool,
    }

    /// `None` when Lean returns the ABI failure marker `null`.
    pub fn unify(request_json: &str) -> Option<UnifyResult> {
        let request_json = request_json.to_owned();
        let raw = lean_call(move || unsafe {
            let req = lean_string(&request_json);
            take_string(ffi::lean_cross_pred_unify(req))
        });
        parse_unify(&raw)
    }

    fn parse_unify(raw: &str) -> Option<UnifyResult> {
        if raw == "null" {
            return None;
        }
        let value: serde_json::Value = serde_json::from_str(raw).ok()?;
        let ok = value.get("ok")?.as_bool()?;
        let pass = match value.get("pass") {
            Some(bit) => bit.as_bool()?,
            None if !ok => false,
            None => return None,
        };
        Some(UnifyResult { ok, pass })
    }

    #[cfg(test)]
    mod tests {
        use super::{normalize, unify, UnifyResult};

        const ENV_R: &str = r#"{"packetBase":"v32:4","packetEnd":"add32(v32:4,v32:5)"}"#;
        const ENV_E: &str = r#"{"packetBase":"v32:4","packetEnd":"add32(v32:4,128)"}"#;
        const BOUND_RT: &str = r#"{"kind":"branch","position":10,"dir":"taken","width":32,"cond":{"lhs":"add32(v32:4,v32:5)","rel":"ltu","rhs":"add32(v32:4,14)"}}"#;
        const BOUND_ET: &str = r#"{"kind":"branch","position":6,"dir":"taken","width":64,"cond":{"lhs":"id64(add64(id64(zext32/64/32(extract0,32(v32:4))),14))","rel":"gtu","rhs":"zext32/64/32(extract0,32(add32(v32:4,128)))"}}"#;
        const CROSS: &str = r#"{"kind":"branch","dir":"taken","cond":{"kind":"packetBound","base":{"kind":"var","name":4},"rel":{"kind":"ltu","q":32},"offset":{"kind":"app","op":"add","params":[],"args":[{"kind":"var","name":4},{"kind":"c","value":"14"}]}}}"#;

        #[test]
        fn cross_pred_bound_taken_pair_matches() {
            assert_eq!(normalize(ENV_R, BOUND_RT).as_deref(), Some(CROSS));
            assert_eq!(normalize(ENV_E, BOUND_ET).as_deref(), Some(CROSS));
        }

        #[test]
        fn cross_pred_bad_json_is_none() {
            assert_eq!(normalize("{", BOUND_RT), None);
            assert_eq!(normalize(ENV_R, "{"), None);
        }

        #[test]
        fn cross_pred_unify_var_rename_passes() {
            let request = r#"{"left":[{"kind":"ret","payload":{"kind":"var","name":4}},{"kind":"ret","payload":{"kind":"reg","reg":"real:2:[0,32)"}}],"right":[{"kind":"ret","payload":{"kind":"var","name":9}},{"kind":"ret","payload":{"kind":"reg","reg":"real:5:[0,32)"}}]}"#;
            assert_eq!(
                unify(request),
                Some(UnifyResult {
                    ok: true,
                    pass: true
                })
            );
        }

        #[test]
        fn cross_pred_unify_bad_json_is_none() {
            assert_eq!(unify("{"), None);
        }
    }
}
