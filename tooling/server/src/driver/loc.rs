//! Loc conversion at the Lean FFI / driver boundary only.
//! Wire loc strings stay Lean's current form (0-based index or `"exit"`).
//! Doc ordinals are 1-based Pos when the protocol speaks BranchFrame `jb`.

#![allow(dead_code)]

/// Parsed wire location.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WireLoc {
    /// 0-based instruction index as Lean emits it.
    Pos(u32),
    Exit,
}

pub fn parse_wire_loc(wire: &str) -> WireLoc {
    if wire == "exit" {
        WireLoc::Exit
    } else {
        match wire.parse::<u32>() {
            Ok(j) => WireLoc::Pos(j),
            Err(_) => WireLoc::Exit,
        }
    }
}

/// 0-based wire index → 1-based doc ordinal. `exit` / bad → `None`.
pub fn wire_loc_to_doc(wire: &str) -> Option<u32> {
    match parse_wire_loc(wire) {
        WireLoc::Pos(j) => Some(j.saturating_add(1)),
        WireLoc::Exit => None,
    }
}

/// 1-based doc ordinal → 0-based wire index for `expand_step` `j`.
pub fn doc_loc_to_wire(doc: u32) -> u32 {
    doc.saturating_sub(1)
}
