mod error;
pub use error::{CompileError, Status};
mod decode;
mod elf;
mod lift;
mod program;

pub use decode::decode;
pub use elf::{parse, ElfError, Object, Section};
pub use lift::{lift, Compiled};
pub use program::{load_function, Func};
