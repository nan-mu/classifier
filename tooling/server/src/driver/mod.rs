//! Expand-driver domain types: Agenda schedule, History shells, merge stub, loc boundary.
//! Lean remains create/step only; SemState bytes stay in the applied graph snapshot.

pub mod history;
pub mod loc;
pub mod merge;
pub mod pred_kinds;
pub mod schedule;

pub use history::RecordStore;
pub use merge::MergePort;
pub use schedule::{Agenda, Dir};
