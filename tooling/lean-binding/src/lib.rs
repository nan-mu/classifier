//! Thin Rust interface over Lean `@[export]` symbols from `CommonMath` and `RV32IMC`.

use std::sync::{Mutex, Once};

static INIT: Once = Once::new();
/// Lean runtime is process-global and not reentrant across threads.
static LEAN_LOCK: Mutex<()> = Mutex::new(());

mod ffi {
    use std::os::raw::{c_char, c_uchar, c_void};

    pub type LeanObj = *mut c_void;

    unsafe extern "C" {
        pub fn lean_initialize_runtime_module();
        pub fn lean_initialize();
        pub fn lean_io_mark_end_initialization();

        pub fn initialize_Init(builtin: c_uchar, world: LeanObj) -> LeanObj;
        pub fn initialize_classifier_CommonMath(builtin: c_uchar, world: LeanObj) -> LeanObj;
        pub fn initialize_classifier_RV32IMC(builtin: c_uchar, world: LeanObj) -> LeanObj;

        // Inlines from lean.h, exported by shim.c
        pub fn lean_binding_string_cstr(o: LeanObj) -> *const c_char;
        pub fn lean_binding_inc(o: LeanObj);
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
            words: LeanObj,
            base: u32,
            helper: u32,
            steps: u32,
            budget: u32,
        ) -> LeanObj;
        pub fn lean_rv32_expand_words_snapshot(words: LeanObj, steps: u32, budget: u32) -> LeanObj;
        pub fn lean_rv32_expand_create(
            words: LeanObj,
            base: u32,
            helper: u32,
            budget: u32,
        ) -> LeanObj;
        pub fn lean_rv32_expand_step(session: LeanObj) -> LeanObj;
        pub fn lean_rv32_expand_snapshot(session: LeanObj) -> LeanObj;
        pub fn lean_rv32_expand_is_running(session: LeanObj) -> u32;
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
    use super::{LEAN_LOCK, ffi, init};

    pub fn add32(a: u32, b: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::common_math_add32(a, b) }
    }

    pub fn sub32(a: u32, b: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::common_math_sub32(a, b) }
    }

    pub fn and32(a: u32, b: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::common_math_and32(a, b) }
    }

    pub fn tq32(a: u32, b: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::common_math_tq32(a, b) }
    }

    pub fn divu32(a: u32, b: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::common_math_divu32(a, b) }
    }

    /// §18 demo: `B=11` Complete with Exit and `B=10` LimitExceeded.
    pub fn path_demo_check() -> bool {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_path_demo_check(0) == 1 }
    }

    /// Node count on Complete for budget `B`, else 0.
    pub fn path_demo_nodes(budget: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_path_demo_nodes(budget) }
    }

    /// JSON snapshot after `steps` expandOne calls (Lean `demoSnapshot`).
    pub fn path_demo_snapshot(steps: u32, budget: u32) -> String {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe {
            let obj = ffi::lean_path_demo_snapshot(steps, budget);
            let cstr = std::ffi::CStr::from_ptr(ffi::lean_binding_string_cstr(obj))
                .to_string_lossy()
                .into_owned();
            ffi::lean_binding_dec(obj);
            cstr
        }
    }
}

pub mod rv32 {
    use super::{LEAN_LOCK, ffi, init};
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
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_rv32_decode32(word) }
    }

    pub fn decode16(half: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_rv32_decode16(half) }
    }

    pub fn value_addi(rs1_val: u32, imm: u32, rs1: u32, rd: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_rv32_value_addi(rs1_val, imm, rs1, rd) }
    }

    pub fn value_add(rs1_val: u32, rs2_val: u32, rs1: u32, rs2: u32, rd: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_rv32_value_add(rs1_val, rs2_val, rs1, rs2, rd) }
    }

    pub fn value_auipc(pc: u32, uimm20: u32, rd: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_rv32_value_auipc(pc, uimm20, rd) }
    }

    pub fn value_lui(uimm20: u32, rd: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_rv32_value_lui(uimm20, rd) }
    }

    pub fn value_div(rs1_val: u32, rs2_val: u32) -> u32 {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_rv32_value_div(rs1_val, rs2_val) }
    }

    pub fn ecall_rejects() -> bool {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_rv32_value_ecall_rejects(0) == 1 }
    }

    pub fn expr_override_keeps() -> bool {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe { ffi::lean_rv32_expr_override_keeps(0) == 1 }
    }

    /// JSON after `steps` expandOne calls on the Lean smoke program (`rv32Snapshot`).
    pub fn expand_snapshot(steps: u32, budget: u32) -> String {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe {
            let obj = ffi::lean_rv32_expand_builtin_snapshot(steps, budget);
            take_string(obj)
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
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe {
            let arr = ffi::lean_binding_mk_uint32_array(words.as_ptr(), words.len());
            let obj = ffi::lean_rv32_expand_bound_words_snapshot(arr, base, helper, steps, budget);
            take_string(obj)
        }
    }

    /// JSON after `steps` expandOne calls on a caller-supplied instruction word list.
    pub fn expand_words_snapshot(words: &[u32], steps: u32, budget: u32) -> String {
        init();
        let _g = LEAN_LOCK.lock().expect("lean lock");
        unsafe {
            let arr = ffi::lean_binding_mk_uint32_array(words.as_ptr(), words.len());
            let obj = ffi::lean_rv32_expand_words_snapshot(arr, steps, budget);
            take_string(obj)
        }
    }

    unsafe fn take_string(obj: ffi::LeanObj) -> String {
        let s = CStr::from_ptr(ffi::lean_binding_string_cstr(obj))
            .to_string_lossy()
            .into_owned();
        ffi::lean_binding_dec(obj);
        s
    }

    /// Persistent Lean expand session. Rust owns the handle and drives true single-step
    /// `expandOne` calls; graph/`WorkState` live in the Lean heap behind this pointer.
    /// All methods take the process-wide Lean lock (runtime is not reentrant).
    pub struct ExpandSession {
        handle: ffi::LeanObj,
    }

    // Safe to move across threads only because every Lean touch goes through `LEAN_LOCK`.
    unsafe impl Send for ExpandSession {}

    impl ExpandSession {
        pub fn create(words: &[u32], base: u32, helper: u32, budget: u32) -> Self {
            init();
            let _g = LEAN_LOCK.lock().expect("lean lock");
            unsafe {
                let arr = ffi::lean_binding_mk_uint32_array(words.as_ptr(), words.len());
                Self {
                    handle: ffi::lean_rv32_expand_create(arr, base, helper, budget),
                }
            }
        }

        pub fn step(&mut self) {
            let _g = LEAN_LOCK.lock().expect("lean lock");
            self.handle = unsafe { ffi::lean_rv32_expand_step(self.handle) };
        }

        pub fn is_running(&self) -> bool {
            let _g = LEAN_LOCK.lock().expect("lean lock");
            unsafe {
                ffi::lean_binding_inc(self.handle);
                ffi::lean_rv32_expand_is_running(self.handle) == 1
            }
        }

        pub fn snapshot_json(&self) -> String {
            let _g = LEAN_LOCK.lock().expect("lean lock");
            unsafe {
                ffi::lean_binding_inc(self.handle);
                take_string(ffi::lean_rv32_expand_snapshot(self.handle))
            }
        }

        /// Step until terminal or `budget + 1` steps (safety cap matching prior server loop).
        pub fn run_to_completion(&mut self, budget: u32) {
            let cap = budget.saturating_add(1);
            for _ in 0..cap {
                if !self.is_running() {
                    break;
                }
                self.step();
            }
        }
    }

    impl Drop for ExpandSession {
        fn drop(&mut self) {
            let _g = LEAN_LOCK.lock().expect("lean lock");
            unsafe { ffi::lean_binding_dec(self.handle) };
        }
    }

    /// Run several independent expands to completion, overlapping work across threads.
    /// Lean calls still serialize on `LEAN_LOCK`; this overlaps Rust-side session chrome.
    pub fn run_many_to_completion(
        jobs: Vec<(Vec<u32>, u32, u32, u32)>,
    ) -> Vec<String> {
        use std::thread;

        let mut handles = Vec::with_capacity(jobs.len());
        for (words, base, helper, budget) in jobs {
            handles.push(thread::spawn(move || {
                let mut session = ExpandSession::create(&words, base, helper, budget);
                session.run_to_completion(budget);
                session.snapshot_json()
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().expect("expand worker"))
            .collect()
    }
}
