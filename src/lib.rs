//! BPF and RV32IMC classifier — prefixgen + pathgen pipeline (SMT predicate IR).

pub mod bpf;
pub mod emit;
pub mod load;
pub mod pathgen;
pub mod predicate;
pub mod prefixgen;
pub mod rv32;

pub use emit::{write_pathgen, write_prefixgen};
pub use load::load_asm_from_toml;
pub use pathgen::{pathgen_bpf, pathgen_rv32, Path, TASK_PATHGEN};
pub use prefixgen::{
    Arch, TASK_PREFIXGEN, prefixgen_bpf_asm, prefixgen_bpf_object, prefixgen_bpf_words,
    prefixgen_rv32, prefixgen_rv32_elf,
};
pub use rv32::Environment;
