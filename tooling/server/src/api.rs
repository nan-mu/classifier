//! Sole product entry: `Kernel::execute(Command) -> Envelope`.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use lean_binding::compare;
use lean_binding::ebpf;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use crate::bpf_image;
use crate::expand::{Arch, Session, Snapshot};
use crate::pred_match;
use crate::pred_tree;
use crate::rv32_image;

#[derive(Debug, Clone)]
pub enum ImageSource {
    Default,
    Bytes(Vec<u8>),
    Path(PathBuf),
}

#[derive(Debug, Clone)]
pub enum Command {
    Create {
        arch: Arch,
        budget: u32,
        name: Option<String>,
        image: ImageSource,
        /// Companion Compact ELF for eBPF map rows. Omitted → just_tx product maps.
        map_elf: Option<ImageSource>,
    },
    Step {
        session_id: String,
    },
    Run {
        session_id: String,
    },
    Get {
        session_id: String,
    },
    CompareRuns {
        left: Value,
        right: Value,
    },
    ComparePredicates {
        left: Value,
        right: Value,
    },
    CompareTree {
        left: Value,
        right: Value,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KernelError {
    pub code: String,
    pub message: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct Envelope {
    pub v: u32,
    pub ok: bool,
    pub command: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub payload: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<KernelError>,
}

impl Envelope {
    fn ok(command: &str, session_id: Option<String>, payload: Value) -> Self {
        Self {
            v: 1,
            ok: true,
            command: command.into(),
            session_id,
            payload: Some(payload),
            error: None,
        }
    }

    fn err(command: &str, code: &str, message: impl Into<String>) -> Self {
        Self {
            v: 1,
            ok: false,
            command: command.into(),
            session_id: None,
            payload: None,
            error: Some(KernelError {
                code: code.into(),
                message: message.into(),
            }),
        }
    }

    pub fn fail(command: &str, code: &str, message: impl Into<String>) -> Self {
        Self::err(command, code, message)
    }
}

pub struct Kernel {
    sessions: Mutex<HashMap<String, Arc<Mutex<Session>>>>,
    next_id: AtomicU64,
}

impl Default for Kernel {
    fn default() -> Self {
        Self::new()
    }
}

impl Kernel {
    pub fn new() -> Self {
        Self {
            sessions: Mutex::new(HashMap::new()),
            next_id: AtomicU64::new(1),
        }
    }

    pub fn execute(&self, cmd: Command) -> Envelope {
        match cmd {
            Command::Create {
                arch,
                budget,
                name,
                image,
                map_elf,
            } => self.create(arch, budget, name, image, map_elf),
            Command::Step { session_id } => self.with_session("step", &session_id, |s| {
                s.step_once();
                snap_value(s.snapshot())
            }),
            Command::Run { session_id } => self.with_session("run", &session_id, |s| {
                s.run_all();
                snap_value(s.snapshot())
            }),
            Command::Get { session_id } => {
                self.with_session("get", &session_id, |s| snap_value(s.snapshot()))
            }
            Command::CompareRuns { left, right } => {
                let request = json!({ "left": left, "right": right }).to_string();
                match serde_json::from_str::<Value>(&compare::run_same_diff(&request)) {
                    Ok(v) => Envelope::ok("compare_runs", None, v),
                    Err(e) => Envelope::err("compare_runs", "bad_response", e.to_string()),
                }
            }
            Command::ComparePredicates { left, right } => {
                let left: pred_match::PredRun = match serde_json::from_value(left) {
                    Ok(v) => v,
                    Err(e) => {
                        return Envelope::err("compare_predicates", "bad_request", e.to_string())
                    }
                };
                let right: pred_match::PredRun = match serde_json::from_value(right) {
                    Ok(v) => v,
                    Err(e) => {
                        return Envelope::err("compare_predicates", "bad_request", e.to_string())
                    }
                };
                let report = pred_match::match_predicate_runs(&left, &right);
                Envelope::ok(
                    "compare_predicates",
                    None,
                    serde_json::to_value(report).unwrap_or(Value::Null),
                )
            }
            Command::CompareTree { left, right } => {
                let left: pred_tree::SnapRun = match serde_json::from_value(left) {
                    Ok(v) => v,
                    Err(e) => return Envelope::err("compare_tree", "bad_request", e.to_string()),
                };
                let right: pred_tree::SnapRun = match serde_json::from_value(right) {
                    Ok(v) => v,
                    Err(e) => return Envelope::err("compare_tree", "bad_request", e.to_string()),
                };
                let report = pred_tree::build_compare_tree(&left, &right);
                Envelope::ok(
                    "compare_tree",
                    None,
                    serde_json::to_value(report).unwrap_or(Value::Null),
                )
            }
        }
    }

    pub fn snapshot_value(&self, session_id: &str) -> Option<Value> {
        let sessions = self.sessions.lock().expect("sessions");
        let session = sessions.get(session_id)?;
        let snap = session.lock().expect("session").snapshot();
        Some(snap_value(snap))
    }

    fn create(
        &self,
        arch: Arch,
        budget: u32,
        name: Option<String>,
        image: ImageSource,
        map_elf: Option<ImageSource>,
    ) -> Envelope {
        let name = name
            .filter(|s| !s.trim().is_empty())
            .unwrap_or_else(|| default_name(arch).to_string());
        let bin = match load_image(&image, arch) {
            Ok(b) => b,
            Err(e) => return Envelope::err("create", &e.code, e.message),
        };
        if bin.is_empty() || bin.len() > 256 * 1024 {
            return Envelope::err("create", "bad_image", "image empty or larger than 256 KiB");
        }
        let id = format!("{}", self.next_id.fetch_add(1, Ordering::Relaxed));
        let session = match arch {
            Arch::Rv32imc => match rv32_image::parse_xdp_elf(&bin) {
                Ok(program) => Session::new(id.clone(), budget, arch, name, program),
                Err(_) => {
                    return Envelope::err("create", "bad_image", "invalid Compact XDP ELF");
                }
            },
            Arch::Ebpf => {
                let program = match bpf_image::extract_insn_words(&bin) {
                    Ok(p) => p,
                    Err(_) => {
                        return Envelope::err("create", "bad_image", "invalid eBPF object");
                    }
                };
                let meta = match ebpf_meta(map_elf.as_ref()) {
                    Ok(m) => m,
                    Err(e) => return Envelope::err("create", &e.code, e.message),
                };
                Session::new_ebpf(id.clone(), budget, name, program, meta)
            }
        };
        let snap = snap_value(session.snapshot());
        self.sessions
            .lock()
            .expect("sessions")
            .insert(id.clone(), Arc::new(Mutex::new(session)));
        Envelope::ok("create", Some(id), snap)
    }

    fn with_session(
        &self,
        command: &str,
        session_id: &str,
        f: impl FnOnce(&mut Session) -> Value,
    ) -> Envelope {
        let sessions = self.sessions.lock().expect("sessions");
        let Some(handle) = sessions.get(session_id).cloned() else {
            return Envelope::err(command, "not_found", format!("unknown session {session_id}"));
        };
        drop(sessions);
        let mut session = handle.lock().expect("session");
        let payload = f(&mut session);
        Envelope::ok(command, Some(session_id.into()), payload)
    }
}

fn default_name(arch: Arch) -> &'static str {
    match arch {
        Arch::Rv32imc => rv32_image::DEFAULT_NAME,
        Arch::Ebpf => bpf_image::DEFAULT_BPF_NAME,
    }
}

fn default_bytes(arch: Arch) -> &'static [u8] {
    match arch {
        Arch::Rv32imc => rv32_image::DEFAULT_ELF,
        Arch::Ebpf => bpf_image::DEFAULT_BPF,
    }
}

fn load_image(src: &ImageSource, arch: Arch) -> Result<Vec<u8>, KernelError> {
    match src {
        ImageSource::Default => Ok(default_bytes(arch).to_vec()),
        ImageSource::Bytes(b) => Ok(b.clone()),
        ImageSource::Path(p) => std::fs::read(p).map_err(|e| KernelError {
            code: "bad_image".into(),
            message: format!("read {}: {e}", p.display()),
        }),
    }
}

fn ebpf_meta(map_elf: Option<&ImageSource>) -> Result<ebpf::Meta, KernelError> {
    let elf_bytes = match map_elf {
        None => rv32_image::DEFAULT_ELF.to_vec(),
        Some(src) => load_image(src, Arch::Rv32imc)?,
    };
    let maps = rv32_image::parse_xdp_elf(&elf_bytes)
        .map_err(|_| KernelError {
            code: "bad_image".into(),
            message: "map_elf is not a valid Compact XDP ELF".into(),
        })?
        .maps;
    let mut meta = ebpf::Meta::just_tx_product();
    meta.maps = maps;
    Ok(meta)
}

fn snap_value(snap: Snapshot) -> Value {
    serde_json::to_value(snap).unwrap_or(Value::Null)
}

pub fn snap_run_from_snapshot(snap: &Value) -> Value {
    json!({
        "arch": snap.get("arch").cloned().unwrap_or(json!("")),
        "nodes": snap.get("nodes").cloned().unwrap_or(json!([])),
        "edges": snap.get("edges").cloned().unwrap_or(json!([])),
    })
}

pub fn resolve_path(base: &Path, rel: &str) -> PathBuf {
    if Path::new(rel).is_absolute() {
        PathBuf::from(rel)
    } else {
        base.join(rel)
    }
}
