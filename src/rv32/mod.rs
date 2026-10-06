//! RV32IMC frontend used by prefixgen: decode → lower → Op table.
//!
//! Legacy string T0–T5, Isla execution tree, and footprint tooling are not on
//! the compile graph (session restore left those sources incomplete).

pub(crate) mod decode;
pub(crate) mod environment;
pub(crate) mod lower;
pub(crate) mod op;

pub use decode::{decode_rv32imc, DecodedInsn, DecodedInstruction, InstructionTable};
pub use environment::{
    CallContract, Environment, Helper, MapContract, PacketContract, Selector, StackContract,
};
pub(crate) use lower::{lower_bin, lower_decoded};
