//! Domain library: expand sessions, compare tree, Kernel command API, CaseSpec harness.

pub mod api;
pub mod bpf_image;
pub mod driver;
pub mod ebpf_disasm;
pub mod engine;
pub mod expand;
pub mod harness;
pub mod pred_match;
pub mod pred_tree;
pub mod profile;
pub mod rv32_image;

pub use api::{Command, Envelope, ImageSource, Kernel, KernelError};
pub use expand::{Arch, BatchTick, Session, Snapshot, WaveBatchPolicy};
pub use harness::{run_suite, CaseOutcome, CaseSpec, SuiteReport};
