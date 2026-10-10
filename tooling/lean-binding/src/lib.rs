//! Thin Rust interface over Lean `@[export]` symbols from `CommonMath` and `RV32IMC`.

use std::sync::Once;

static INIT: Once = Once::new();

mod ffi {
    use std::os::raw::{c_char, c_uchar, c_void};

    type LeanObj = *mut c_void;

    unsafe extern "C" {
        pub fn lean_initialize_runtime_module();
        pub fn lean_initialize();
        pub fn lean_io_mark_end_initialization();

        pub fn initialize_Init(builtin: c_uchar, world: LeanObj) -> LeanObj;
        pub fn initialize_classifier_CommonMath(builtin: c_uchar, world: LeanObj) -> LeanObj;
        pub fn initialize_classifier_RV32IMC(builtin: c_uchar, world: LeanObj) -> LeanObj;

        // Inlines from lean.h, exported by shim.c
        pub fn lean_binding_string_cstr(o: LeanObj) -> *const c_char;
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
        pub fn lean_rv32_expand_snapshot(steps: u32, budget: u32) -> LeanObj;
        pub fn lean_rv32_expand_bound_words_snapshot(
            words: LeanObj,
            base: u32,
            helper: u32,
            steps: u32,
            budget: u32,
        ) -> LeanObj;
        pub fn lean_rv32_expand_words_snapshot(words: LeanObj, steps: u32, budget: u32) -> LeanObj;
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

pub mod common_math {
    use super::{ffi, init};

    pub fn add32(a: u32, b: u32) -> u32 {
        init();
        unsafe { ffi::common_math_add32(a, b) }
    }

    pub fn sub32(a: u32, b: u32) -> u32 {
        init();
        unsafe { ffi::common_math_sub32(a, b) }
    }

    pub fn and32(a: u32, b: u32) -> u32 {
        init();
        unsafe { ffi::common_math_and32(a, b) }
    }

    pub fn tq32(a: u32, b: u32) -> u32 {
        init();
        unsafe { ffi::common_math_tq32(a, b) }
    }

    pub fn divu32(a: u32, b: u32) -> u32 {
        init();
        unsafe { ffi::common_math_divu32(a, b) }
    }

    /// §18 demo: `B=11` Complete with Exit and `B=10` LimitExceeded.
    pub fn path_demo_check() -> bool {
        init();
        unsafe { ffi::lean_path_demo_check(0) == 1 }
    }

    /// Node count on Complete for budget `B`, else 0.
    pub fn path_demo_nodes(budget: u32) -> u32 {
        init();
        unsafe { ffi::lean_path_demo_nodes(budget) }
    }

    /// JSON snapshot after `steps` expandOne calls (Lean `demoSnapshot`).
    pub fn path_demo_snapshot(steps: u32, budget: u32) -> String {
        init();
        unsafe {
            let obj = ffi::lean_path_demo_snapshot(steps, budget);
            let cstr = ffi::lean_binding_string_cstr(obj);
            let s = std::ffi::CStr::from_ptr(cstr)
                .to_string_lossy()
                .into_owned();
            ffi::lean_binding_dec(obj);
            s
        }
    }
}

pub mod rv32 {
    use super::{ffi, init};

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
        init();
        unsafe { ffi::lean_rv32_decode32(word) }
    }

    pub fn decode16(half: u32) -> u32 {
        init();
        unsafe { ffi::lean_rv32_decode16(half) }
    }

    pub fn value_addi(rs1_val: u32, imm: u32, rs1: u32, rd: u32) -> u32 {
        init();
        unsafe { ffi::lean_rv32_value_addi(rs1_val, imm, rs1, rd) }
    }

    pub fn value_add(rs1_val: u32, rs2_val: u32, rs1: u32, rs2: u32, rd: u32) -> u32 {
        init();
        unsafe { ffi::lean_rv32_value_add(rs1_val, rs2_val, rs1, rs2, rd) }
    }

    pub fn value_auipc(pc: u32, uimm20: u32, rd: u32) -> u32 {
        init();
        unsafe { ffi::lean_rv32_value_auipc(pc, uimm20, rd) }
    }

    pub fn value_lui(uimm20: u32, rd: u32) -> u32 {
        init();
        unsafe { ffi::lean_rv32_value_lui(uimm20, rd) }
    }

    pub fn value_div(rs1_val: u32, rs2_val: u32) -> u32 {
        init();
        unsafe { ffi::lean_rv32_value_div(rs1_val, rs2_val) }
    }

    pub fn ecall_rejects() -> bool {
        init();
        unsafe { ffi::lean_rv32_value_ecall_rejects(0) == 1 }
    }

    pub fn expr_override_keeps() -> bool {
        init();
        unsafe { ffi::lean_rv32_expr_override_keeps(0) == 1 }
    }

    /// JSON after `steps` expandOne calls on the Lean smoke program (`rv32Snapshot`).
    pub fn expand_snapshot(steps: u32, budget: u32) -> String {
        init();
        unsafe {
            let obj = ffi::lean_rv32_expand_snapshot(steps, budget);
            let cstr = ffi::lean_binding_string_cstr(obj);
            let s = std::ffi::CStr::from_ptr(cstr)
                .to_string_lossy()
                .into_owned();
            ffi::lean_binding_dec(obj);
            s
        }
    }

    pub fn expand_bound_words_snapshot(
        words: &[u32],
        base: u32,
        helper: u32,
        steps: u32,
        budget: u32,
    ) -> String {
        init();
        unsafe {
            let arr = ffi::lean_binding_mk_uint32_array(words.as_ptr(), words.len());
            let obj = ffi::lean_rv32_expand_bound_words_snapshot(arr, base, helper, steps, budget);
            let result = std::ffi::CStr::from_ptr(ffi::lean_binding_string_cstr(obj))
                .to_string_lossy()
                .into_owned();
            ffi::lean_binding_dec(obj);
            result
        }
    }

    /// JSON after `steps` expandOne calls on a caller-supplied instruction word list.
    pub fn expand_words_snapshot(words: &[u32], steps: u32, budget: u32) -> String {
        init();
        unsafe {
            let arr = ffi::lean_binding_mk_uint32_array(words.as_ptr(), words.len());
            let obj = ffi::lean_rv32_expand_words_snapshot(arr, steps, budget);
            let cstr = ffi::lean_binding_string_cstr(obj);
            let s = std::ffi::CStr::from_ptr(cstr)
                .to_string_lossy()
                .into_owned();
            ffi::lean_binding_dec(obj);
            s
        }
    }
}
