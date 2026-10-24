//! Expand-driver domain types: Agenda schedule, History shells, loc boundary.
//! State bytes stay in the applied graph snapshot. Exact-config merge is not
//! called from the schedule.

pub mod history;
pub mod loc;
pub mod merge;
pub mod pred_kinds;
pub mod schedule;

pub use history::RecordStore;
pub use merge::{ConfigSnapshot, MergeEffect, MergePort};
pub use schedule::{Agenda, Dir};
