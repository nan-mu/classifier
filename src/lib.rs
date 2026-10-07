//! BPF and RV32IMC classifier — prefixgen + pathgen pipeline (SMT predicate IR).

pub mod bpf;
pub mod emit;
pub mod load;
pub mod pathgen;
pub mod predicate;
pub mod prefixgen;
pub mod qfbv;
pub mod rv32;

pub use emit::{write_pathgen, write_prefixgen};
pub use load::load_asm_from_toml;
pub use pathgen::{Path, TASK_PATHGEN, pathgen_bpf, pathgen_rv32};
pub use prefixgen::{
    Arch, TASK_PREFIXGEN, prefixgen_bpf_asm, prefixgen_bpf_object, prefixgen_bpf_words,
    prefixgen_rv32, prefixgen_rv32_elf,
};
pub use qfbv::{
    AstError, BoolExpr, BvBinaryOp, BvCmpOp, BvExpr, BvUnaryOp, DEFAULT_COQQFBV, GoalError,
    PathFamilyEvidence, PathFamilyMatching, PathFormula, PathPair, QfbvQuery, QfbvStatus,
    check_qfbv_file, check_qfbv_file_with, compile_path_asserts, compile_xdp_assert_pair,
    compile_xdp_bpf_path_asserts, compile_xdp_rv32_path_asserts,
    discover_path_family_matching_with, inequivalence_query, verify_path_family_matching_with,
    write_path_family_evidence, xdp_environment_contract,
};
pub use rv32::Environment;
