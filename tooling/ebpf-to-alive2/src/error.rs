use serde::Serialize;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Status {
    Converted,
    Unsupported,
    InvalidElf,
    InvalidInstruction,
    InternalError,
}

#[derive(Clone, Debug, Serialize)]
pub struct CompileError {
    pub status: Status,
    pub stage: &'static str,
    pub slot: Option<u32>,
    pub register: Option<u8>,
    pub message: String,
}

impl CompileError {
    pub fn new(
        status: Status,
        stage: &'static str,
        slot: Option<u32>,
        register: Option<u8>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            status,
            stage,
            slot,
            register,
            message: message.into(),
        }
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} at {}", self.status, self.stage)?;
        if let Some(slot) = self.slot {
            write!(f, " slot {slot}")?;
        }
        if let Some(register) = self.register {
            write!(f, " r{register}")?;
        }
        write!(f, ": {}", self.message)
    }
}
impl std::error::Error for CompileError {}
impl From<String> for CompileError {
    fn from(message: String) -> Self {
        Self::new(Status::InternalError, "internal", None, None, message)
    }
}
impl From<&str> for CompileError {
    fn from(message: &str) -> Self {
        message.to_owned().into()
    }
}
