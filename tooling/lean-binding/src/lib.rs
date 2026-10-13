//! Thin Rust interface over Lean `@[export]` symbols from `CommonMath` and `RV32IMC`.
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
        pub fn initialize_classifier_CommonMath(builtin: c_uchar, world: LeanObj) -> LeanObj;
        pub fn initialize_classifier_RV32IMC(builtin: c_uchar, world: LeanObj) -> LeanObj;

        // Inlines from lean.h, exported by shim.c
        pub fn lean_binding_string_cstr(o: LeanObj) -> *const c_char;
        pub fn lean_binding_mk_string(utf8: *const c_char) -> LeanObj;
        pub fn lean_binding_dec(o: LeanObj);
        pub fn lean_binding_mk_uint32_array(data: *const u32, len: usize) -> LeanObj;

        pub fn common_math_add32(a: u32, b: u32) -> u32;
        pub fn common_math_sub32(a: u32, b: u32) -> u32;
        pub fn common_math_and32(a: u32, b: u32) -> u32;
        pub fn common_math_tq32(a: u32, b: u32) -> u32;
        pub fn common_math_divu32(a: u32, b: u32) -> u32;
        pub fn lean_path_demo_check(unused: u32) -> u32;
        pub fn lean_path_demo_nodes(budget: u32) -> u32;
        pub fn lean_path_demo_snapshot(steps: u32, budget: u32) -> LeanObj;
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
            meta_json: LeanObj,
            steps: u32,
            budget: u32,
        ) -> LeanObj;
        pub fn lean_rv32_expand_words_snapshot(insns: LeanObj, steps: u32, budget: u32) -> LeanObj;
        pub fn lean_rv32_expand_create(meta_json: LeanObj) -> LeanObj;
        pub fn lean_rv32_expand_step(
            insns: LeanObj,
            meta_json: LeanObj,
            event: u32,
            j: u32,
            exprs_json: LeanObj,
            preds_json: LeanObj,
        ) -> LeanObj;
        /// Arch-neutral exact-config merge (`CommonMath/Merge.lean`).
        pub fn lean_expand_merge(request_json: LeanObj) -> LeanObj;
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
        let _ = ffi::initialize_classifier_CommonMath(1, world);
        let _ = ffi::initialize_classifier_RV32IMC(1, world);
        ffi::lean_io_mark_end_initialization();
    });
}

pub mod expand {
    use super::rv32;

    /// Arch-neutral exact-config merge (request JSON only).
    pub fn merge(request_json: &str) -> String {
        rv32::expand_merge(request_json)
    }
}

pub mod common_math {
    use super::{ffi, lean_call};

    pub fn add32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::common_math_add32(a, b) })
    }

    pub fn sub32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::common_math_sub32(a, b) })
    }

    pub fn and32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::common_math_and32(a, b) })
    }

    pub fn tq32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::common_math_tq32(a, b) })
    }

    pub fn divu32(a: u32, b: u32) -> u32 {
        lean_call(move || unsafe { ffi::common_math_divu32(a, b) })
    }

    /// §18 demo: `B=11` Complete with Exit and `B=10` LimitExceeded.
    pub fn path_demo_check() -> bool {
        lean_call(|| unsafe { ffi::lean_path_demo_check(0) == 1 })
    }

    /// Node count on Complete for budget `B`, else 0.
    pub fn path_demo_nodes(budget: u32) -> u32 {
        lean_call(move || unsafe { ffi::lean_path_demo_nodes(budget) })
    }

    /// JSON snapshot after `steps` expandOne calls (Lean `demoSnapshot`).
    pub fn path_demo_snapshot(steps: u32, budget: u32) -> String {
        lean_call(move || unsafe {
            let obj = ffi::lean_path_demo_snapshot(steps, budget);
            let cstr = std::ffi::CStr::from_ptr(ffi::lean_binding_string_cstr(obj))
                .to_string_lossy()
                .into_owned();
            ffi::lean_binding_dec(obj);
            cstr
        })
    }
}

pub mod rv32 {
    use super::{ffi, lean_call};
    use std::ffi::CStr;

    /// Instruction tags matching `RV32IMC.insnTag`.
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

    /// Static program bindings outside SemState / Predicate.
    /// Extend fields here; create/step FFI takes one Meta JSON blob.
    #[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct Meta {
        pub base: u32,
        /// ELF dispatcher binding — not a Predicate.
        pub helper_address: u32,
        /// Synthetic wrapper return; default `0x2000`.
        #[serde(default = "Meta::default_return_address")]
        pub return_address: u32,
        /// Forward-compatible bag for future bindings.
        #[serde(flatten)]
        pub extra: serde_json::Map<String, serde_json::Value>,
    }

    impl Meta {
        const fn default_return_address() -> u32 {
            0x2000
        }

        pub fn new(base: u32, helper_address: u32) -> Self {
            Self {
                base,
                helper_address,
                return_address: Self::default_return_address(),
                extra: serde_json::Map::new(),
            }
        }

        pub fn to_json(&self) -> String {
            serde_json::to_string(self).expect("Meta JSON")
        }
    }

    unsafe fn lean_string(s: &str) -> ffi::LeanObj {
        use std::ffi::CString;
        let c = CString::new(s).expect("JSON contains NUL");
        ffi::lean_binding_mk_string(c.as_ptr())
    }

    pub fn expand_bound_words_snapshot(
        insns: &[u32],
        meta: &Meta,
        steps: u32,
        budget: u32,
    ) -> String {
        let insns = insns.to_vec();
        let meta_json = meta.to_json();
        lean_call(move || unsafe {
            let arr = ffi::lean_binding_mk_uint32_array(insns.as_ptr(), insns.len());
            let meta = lean_string(&meta_json);
            let obj = ffi::lean_rv32_expand_bound_words_snapshot(arr, meta, steps, budget);
            take_string(obj)
        })
    }

    /// Entry SemState + root node. Program image and fuel stay in the server engine.
    pub fn expand_create(meta: &Meta) -> String {
        let meta_json = meta.to_json();
        lean_call(move || unsafe {
            let meta = lean_string(&meta_json);
            take_string(ffi::lean_rv32_expand_create(meta))
        })
    }

    /// Stateless head inference. Lean returns successors or reject; no fuel field.
    /// Graph / fuel / work-queue ownership lives in the server expand engine.
    pub fn expand_step(
        insns: &[u32],
        meta: &Meta,
        event: u32,
        j: u32,
        exprs_json: &str,
        preds_json: &str,
    ) -> String {
        let insns = insns.to_vec();
        let meta_json = meta.to_json();
        let exprs_json = exprs_json.to_owned();
        let preds_json = preds_json.to_owned();
        lean_call(move || unsafe {
            let arr = ffi::lean_binding_mk_uint32_array(insns.as_ptr(), insns.len());
            let meta = lean_string(&meta_json);
            let exprs = lean_string(&exprs_json);
            let preds = lean_string(&preds_json);
            take_string(ffi::lean_rv32_expand_step(
                arr, meta, event, j, exprs, preds,
            ))
        })
    }

    /// Arch-neutral exact-config merge. Request JSON only (no program / Meta).
    /// See `doc/NodeInference/路径合并FFI.md`.
    pub fn expand_merge(request_json: &str) -> String {
        let request_json = request_json.to_owned();
        lean_call(move || unsafe {
            let req = lean_string(&request_json);
            take_string(ffi::lean_expand_merge(req))
        })
    }
}
