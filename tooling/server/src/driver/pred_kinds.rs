//! Five-class Predicate kind labels as strings. Not a field enum.

#![allow(dead_code)]

pub const HELPER: &str = "helper";
pub const BRANCH: &str = "branch";
pub const RET: &str = "ret";
pub const MAP_WRITE: &str = "mapWrite";
pub const PACKET_WRITE: &str = "packetWrite";

/// Documentation constants for the opaque Predicate wire (`kind` + fields).
pub const FIVE_PRED_KINDS: &[&str] = &[HELPER, BRANCH, RET, MAP_WRITE, PACKET_WRITE];
