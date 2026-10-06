//! Isla symbolic execution state carried between instructions.

use std::collections::HashMap;

use isla_lib::bitvector::b129::B129;
use isla_lib::ir::{Name, Val};
use isla_lib::memory::{Memory, Region};
use isla_lib::smt::Checkpoint;

/// Thin ownership wrapper over Isla frame registers, memory, and SMT checkpoint.
///
/// Symbolic values live in `regs` / `memory` as [`Val::Symbolic`]; their definitions
/// and path constraints live in `checkpoint`. Do not serialize this to text and
/// re-parse — that drops SMT state.
#[derive(Clone)]
pub struct PhysicalState {
    pub checkpoint: Checkpoint<B129>,
    pub regs: HashMap<Name, Val<B129>>,
    pub memory: Memory<B129>,
}

impl PhysicalState {
    pub fn new(
        checkpoint: Checkpoint<B129>,
        regs: HashMap<Name, Val<B129>>,
        memory: Memory<B129>,
    ) -> Self {
        Self {
            checkpoint,
            regs,
            memory,
        }
    }

    /// Architectural equality for loop fixed-point detection.
    ///
    /// Compares register file (`Val` syntactic equality, including symbolic ids)
    /// and memory region layout/contents. Path-condition identity inside the
    /// SMT checkpoint is not compared (checkpoint fields are private); matching
    /// symbolic ids already imply a shared solver lineage for our step model.
    pub fn arch_eq(&self, other: &Self) -> bool {
        self.regs == other.regs && memory_arch_eq(&self.memory, &other.memory)
    }
}

fn memory_arch_eq(a: &Memory<B129>, b: &Memory<B129>) -> bool {
    let ra = a.regions();
    let rb = b.regions();
    if ra.len() != rb.len() {
        return false;
    }
    for (x, y) in ra.iter().zip(rb.iter()) {
        match (x, y) {
            (Region::Concrete(r1, m1), Region::Concrete(r2, m2)) => {
                if r1 != r2 || m1 != m2 {
                    return false;
                }
            }
            (Region::Symbolic(r1), Region::Symbolic(r2))
            | (Region::SymbolicCode(r1), Region::SymbolicCode(r2)) => {
                if r1 != r2 {
                    return false;
                }
            }
            (Region::Constrained(r1, _), Region::Constrained(r2, _)) => {
                // Closures are not comparable; range match is a conservative stand-in.
                if r1 != r2 {
                    return false;
                }
            }
            (Region::Custom(r1, _), Region::Custom(r2, _)) => {
                if r1 != r2 {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}
