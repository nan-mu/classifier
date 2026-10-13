//! Expand-driver domain types: Agenda schedule, History shells, merge port, loc boundary.
//! SemState bytes stay in the applied graph snapshot; merge calls Lean exact-config FFI.

pub mod history;
pub mod loc;
pub mod merge;
pub mod pred_kinds;
pub mod schedule;

pub use history::RecordStore;
pub use merge::{ConfigSnapshot, MergeEffect, MergePort};
pub use schedule::{Agenda, Dir};
