//! CaseSpec interpreter over `Kernel::execute`.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use serde::Deserialize;
use serde_json::Value;

use crate::api::{snap_run_from_snapshot, Command, Envelope, ImageSource, Kernel};
use crate::expand::Arch;

#[derive(Debug, Clone, Deserialize)]
pub struct CaseSpec {
    pub id: String,
    pub suite: String,
    #[serde(default)]
    pub budget: Option<u32>,
    #[serde(default)]
    pub artifacts: HashMap<String, String>,
    pub steps: Vec<Step>,
    pub expect: Expect,
    #[serde(default)]
    pub assert: Vec<Assert>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Step {
    pub op: String,
    #[serde(default)]
    pub bind: Option<String>,
    #[serde(default)]
    pub arch: Option<String>,
    #[serde(default)]
    pub artifact: Option<String>,
    #[serde(default)]
    pub map_elf: Option<String>,
    #[serde(default)]
    pub budget: Option<u32>,
    #[serde(default)]
    pub left: Option<String>,
    #[serde(default)]
    pub right: Option<String>,
    /// Inline compare-tree bodies (fail suite mismatch).
    #[serde(default)]
    pub left_inline: Option<Value>,
    #[serde(default)]
    pub right_inline: Option<Value>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Expect {
    pub kind: String,
    #[serde(default)]
    pub status: Option<String>,
    #[serde(default)]
    pub compare_tree: Option<CompareExpect>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CompareExpect {
    #[serde(default)]
    pub fail: Option<u64>,
    #[serde(default)]
    pub fail_at_least: Option<u64>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Assert {
    #[serde(default)]
    pub path: Option<String>,
    #[serde(default)]
    pub eq: Option<Value>,
    #[serde(default)]
    pub exists: Option<bool>,
    #[serde(default)]
    pub contains_kind: Option<String>,
}

#[derive(Debug, Clone)]
pub struct CaseOutcome {
    pub id: String,
    pub suite: String,
    pub ok: bool,
    pub detail: String,
}

#[derive(Debug, Clone)]
pub struct SuiteReport {
    pub cases: Vec<CaseOutcome>,
}

impl SuiteReport {
    pub fn all_ok(&self) -> bool {
        self.cases.iter().all(|c| c.ok)
    }

    pub fn to_json(&self) -> Value {
        serde_json::json!({
            "ok": self.all_ok(),
            "passed": self.cases.iter().filter(|c| c.ok).count(),
            "failed": self.cases.iter().filter(|c| !c.ok).count(),
            "cases": self.cases.iter().map(|c| serde_json::json!({
                "id": c.id,
                "suite": c.suite,
                "ok": c.ok,
                "detail": c.detail,
            })).collect::<Vec<_>>(),
        })
    }
}

/// Dual-arch cases for every program in `profile.toml`. Budget 1024, compare fail 0.
pub fn run_profile(programs: &[crate::profile::Program]) -> SuiteReport {
    let mut outcomes = Vec::new();
    for program in programs {
        eprintln!("profile {}", program.name);
        let spec = profile_case(program);
        let outcome = match run_case(&spec, Path::new(".")) {
            Ok(()) => CaseOutcome {
                id: spec.id,
                suite: "profile".into(),
                ok: true,
                detail: "pass".into(),
            },
            Err(detail) => CaseOutcome {
                id: spec.id.clone(),
                suite: "profile".into(),
                ok: false,
                detail,
            },
        };
        eprintln!(
            "profile {} {}",
            program.name,
            if outcome.ok { "ok" } else { "FAIL" }
        );
        outcomes.push(outcome);
    }
    SuiteReport { cases: outcomes }
}

fn profile_case(program: &crate::profile::Program) -> CaseSpec {
    let raw = serde_json::json!({
        "id": format!("profile.{}", program.name),
        "suite": "profile",
        "budget": 1024,
        "artifacts": {
            "rv32": program.elf.display().to_string(),
            "ebpf": program.bpf.display().to_string(),
        },
        "steps": [
            { "op": "create", "bind": "rv", "arch": "rv32imc", "artifact": "rv32" },
            { "op": "create", "bind": "bpf", "arch": "ebpf", "artifact": "ebpf", "map_elf": "rv32" },
            { "op": "run", "bind": "rv" },
            { "op": "run", "bind": "bpf" },
            { "op": "compare_tree", "left": "rv", "right": "bpf" }
        ],
        "expect": { "kind": "pass", "status": "complete", "compare_tree": { "fail": 0 } },
    });
    serde_json::from_value(raw).expect("profile case")
}

pub fn run_suite(root: &Path) -> SuiteReport {
    let mut cases = Vec::new();
    for suite in ["base", "xdp", "fail"] {
        let dir = root.join(suite);
        if !dir.is_dir() {
            continue;
        }
        collect_cases(&dir, suite, &mut cases);
    }
    cases.sort_by(|a, b| a.0.cmp(&b.0));
    let mut outcomes = Vec::new();
    for (case_path, suite) in cases {
        eprintln!("case {suite} {}", case_path.display());
        let outcome = run_case_file(&case_path, &suite);
        eprintln!("case {suite} {} {}", case_path.display(), if outcome.ok { "ok" } else { "FAIL" });
        outcomes.push(outcome);
    }
    SuiteReport { cases: outcomes }
}

fn collect_cases(dir: &Path, suite: &str, out: &mut Vec<(PathBuf, String)>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cases(&path, suite, out);
        } else if path.file_name().and_then(|n| n.to_str()) == Some("case.json") {
            out.push((path, suite.to_string()));
        }
    }
}

fn run_case_file(case_path: &Path, suite: &str) -> CaseOutcome {
    let case_dir = case_path.parent().unwrap_or(Path::new("."));
    let raw = match fs::read_to_string(case_path) {
        Ok(s) => s,
        Err(e) => {
            return CaseOutcome {
                id: case_path.display().to_string(),
                suite: suite.into(),
                ok: false,
                detail: format!("read case: {e}"),
            };
        }
    };
    let spec: CaseSpec = match serde_json::from_str(&raw) {
        Ok(s) => s,
        Err(e) => {
            return CaseOutcome {
                id: case_path.display().to_string(),
                suite: suite.into(),
                ok: false,
                detail: format!("parse case: {e}"),
            };
        }
    };
    match run_case(&spec, case_dir) {
        Ok(()) => CaseOutcome {
            id: spec.id,
            suite: suite.into(),
            ok: true,
            detail: "pass".into(),
        },
        Err(detail) => CaseOutcome {
            id: spec.id,
            suite: suite.into(),
            ok: false,
            detail,
        },
    }
}

pub fn run_case(spec: &CaseSpec, case_dir: &Path) -> Result<(), String> {
    let kernel = Kernel::new();
    let mut binds: HashMap<String, String> = HashMap::new();
    let mut last = Envelope {
        v: 1,
        ok: true,
        command: "nop".into(),
        session_id: None,
        payload: None,
        error: None,
    };
    let default_budget = spec.budget.unwrap_or(1024);

    for step in &spec.steps {
        last = exec_step(&kernel, spec, case_dir, &mut binds, step, default_budget)?;
        if !last.ok {
            if spec.expect.kind == "error" {
                return Ok(());
            }
            return Err(format!(
                "step {} failed: {:?}",
                last.command,
                last.error
            ));
        }
    }

    check_expect(spec, &last, &kernel, &binds)?;
    for a in &spec.assert {
        check_assert(&last, a)?;
    }
    Ok(())
}

fn exec_step(
    kernel: &Kernel,
    spec: &CaseSpec,
    case_dir: &Path,
    binds: &mut HashMap<String, String>,
    step: &Step,
    default_budget: u32,
) -> Result<Envelope, String> {
    match step.op.as_str() {
        "create" => {
            let arch = Arch::parse(step.arch.as_deref().unwrap_or("rv32imc"))
                .ok_or_else(|| format!("bad arch {:?}", step.arch))?;
            let budget = step.budget.unwrap_or(default_budget);
            let image = match step.artifact.as_deref() {
                None | Some("") | Some("default") => ImageSource::Default,
                Some(key) => {
                    let rel = spec
                        .artifacts
                        .get(key)
                        .ok_or_else(|| format!("missing artifact {key}"))?;
                    ImageSource::Path(case_dir.join(rel))
                }
            };
            let map_elf = match step.map_elf.as_deref() {
                None => None,
                Some(key) => {
                    let rel = spec
                        .artifacts
                        .get(key)
                        .ok_or_else(|| format!("missing map_elf artifact {key}"))?;
                    Some(ImageSource::Path(case_dir.join(rel)))
                }
            };
            let env = kernel.execute(Command::Create {
                arch,
                budget,
                name: None,
                image,
                map_elf,
            });
            if let (Some(bind), Some(id)) = (step.bind.as_ref(), env.session_id.as_ref()) {
                binds.insert(bind.clone(), id.clone());
            }
            Ok(env)
        }
        "run" => {
            let bind = step.bind.as_deref().ok_or("run needs bind")?;
            let id = binds
                .get(bind)
                .ok_or_else(|| format!("unbound {bind}"))?
                .clone();
            Ok(kernel.execute(Command::Run { session_id: id }))
        }
        "compare_tree" => {
            let (left, right) = if step.left_inline.is_some() || step.right_inline.is_some() {
                (
                    step.left_inline.clone().unwrap_or(Value::Null),
                    step.right_inline.clone().unwrap_or(Value::Null),
                )
            } else {
                let lb = step.left.as_deref().ok_or("compare_tree needs left")?;
                let rb = step.right.as_deref().ok_or("compare_tree needs right")?;
                let lid = binds
                    .get(lb)
                    .ok_or_else(|| format!("unbound {lb}"))?;
                let rid = binds
                    .get(rb)
                    .ok_or_else(|| format!("unbound {rb}"))?;
                let ls = kernel
                    .snapshot_value(lid)
                    .ok_or_else(|| format!("missing snapshot {lid}"))?;
                let rs = kernel
                    .snapshot_value(rid)
                    .ok_or_else(|| format!("missing snapshot {rid}"))?;
                (snap_run_from_snapshot(&ls), snap_run_from_snapshot(&rs))
            };
            Ok(kernel.execute(Command::CompareTree { left, right }))
        }
        other => Err(format!("unknown op {other}")),
    }
}

fn check_expect(
    spec: &CaseSpec,
    last: &Envelope,
    kernel: &Kernel,
    binds: &HashMap<String, String>,
) -> Result<(), String> {
    match spec.expect.kind.as_str() {
        "error" => {
            if last.ok {
                return Err("expected error envelope, got ok".into());
            }
            Ok(())
        }
        "fail" | "pass" => {
            if !last.ok {
                return Err(format!(
                    "expected ok envelope, got error {:?}",
                    last.error
                ));
            }
            if spec.expect.kind == "fail"
                && spec.expect.status.is_none()
                && spec.expect.compare_tree.is_none()
            {
                return Err("expect.kind fail needs status or compare_tree".into());
            }
            if let Some(status) = &spec.expect.status {
                if binds.is_empty() {
                    let got = pointer(last, "/payload/status")
                        .and_then(|v| v.as_str())
                        .unwrap_or("");
                    if got != status {
                        return Err(format!("status want {status} got {got}"));
                    }
                } else {
                    let mut bad = Vec::new();
                    for (bind, id) in binds {
                        let snap = kernel
                            .snapshot_value(id)
                            .ok_or_else(|| format!("missing snapshot {bind}"))?;
                        let got = snap
                            .get("status")
                            .and_then(|v| v.as_str())
                            .unwrap_or("");
                        if got != status {
                            let reason = snap.get("reason").cloned().unwrap_or(Value::Null);
                            let nodes = snap
                                .get("nodes")
                                .and_then(|n| n.as_array())
                                .map(|n| n.len())
                                .unwrap_or(0);
                            let fuel = snap.get("fuel").cloned().unwrap_or(Value::Null);
                            bad.push(format!(
                                "bind {bind} status want {status} got {got} reason {reason} fuel {fuel} nodes {nodes}"
                            ));
                        }
                    }
                    if !bad.is_empty() {
                        return Err(bad.join("; "));
                    }
                }
            }
            if let Some(ct) = &spec.expect.compare_tree {
                let fails = count_match_fails(last);
                if let Some(exact) = ct.fail {
                    if fails != exact {
                        return Err(format!(
                            "compare fail want {exact} got {fails}{}",
                            fail_sample(last)
                        ));
                    }
                }
                if let Some(min) = ct.fail_at_least {
                    if fails < min {
                        return Err(format!("compare fail_at_least {min} got {fails}"));
                    }
                }
            }
            Ok(())
        }
        other => Err(format!("unknown expect.kind {other}")),
    }
}

fn fail_sample(env: &Envelope) -> String {
    let Some(nodes) = pointer(env, "/payload/nodes").and_then(|v| v.as_array()) else {
        return String::new();
    };
    if std::env::var("CLASSIFIER_DUMP_FAILS").is_ok() {
        let fails: Vec<_> = nodes.iter().filter(|n| n.get("matchStatus").and_then(|m| m.as_str()) == Some("fail")).cloned().collect();
        let _ = std::fs::write("/tmp/compare-fails.json", serde_json::to_string(&fails).unwrap_or_default());
    }
    let mut out = String::new();
    for node in nodes.iter().filter(|n| n.get("matchStatus").and_then(|m| m.as_str()) == Some("fail")).take(4) {
        let brief = |side: &str| -> String {
            node.get(side)
                .and_then(|v| v.as_array())
                .map(|items| {
                    items.iter().take(8).map(|item| {
                        item.get("atom").and_then(|a| a.get("kind")).and_then(|k| k.as_str()).unwrap_or("exit").to_string()
                    }).collect::<Vec<_>>().join(",")
                })
                .unwrap_or_default()
        };
        out.push_str(&format!(" [{} L={} R={}]", node.get("id").and_then(|v| v.as_u64()).unwrap_or(0), brief("left"), brief("right")));
    }
    out
}

fn count_match_fails(env: &Envelope) -> u64 {
    let Some(nodes) = pointer(env, "/payload/nodes").and_then(|v| v.as_array()) else {
        return 0;
    };
    nodes
        .iter()
        .filter(|n| n.get("matchStatus").and_then(|m| m.as_str()) == Some("fail"))
        .count() as u64
}

fn check_assert(last: &Envelope, a: &Assert) -> Result<(), String> {
    if let Some(kind) = &a.contains_kind {
        let nodes = pointer(last, "/payload/nodes")
            .and_then(|v| v.as_array())
            .ok_or("no nodes for contains_kind")?;
        let found = nodes.iter().any(|n| {
            n.get("predicates")
                .and_then(|p| p.as_array())
                .is_some_and(|preds| {
                    preds
                        .iter()
                        .any(|p| p.get("kind").and_then(|k| k.as_str()) == Some(kind.as_str()))
                })
        });
        if !found {
            return Err(format!("no predicate kind {kind}"));
        }
        return Ok(());
    }
    let path = a.path.as_deref().ok_or("assert needs path or contains_kind")?;
    let val = pointer(last, path);
    if a.exists == Some(true) {
        if val.is_none() {
            return Err(format!("missing {path}"));
        }
        return Ok(());
    }
    if let Some(want) = &a.eq {
        let got = val.ok_or_else(|| format!("missing {path}"))?;
        if got != want {
            return Err(format!("{path} want {want} got {got}"));
        }
    }
    Ok(())
}

fn pointer<'a>(env: &'a Envelope, path: &str) -> Option<&'a Value> {
    let path = path.trim_start_matches('$');
    if path.is_empty() || path == "/" {
        return None;
    }
    if let Some(rest) = path.strip_prefix("/payload") {
        return walk_value(env.payload.as_ref()?, rest);
    }
    None
}

fn walk_value<'a>(v: &'a Value, path: &str) -> Option<&'a Value> {
    if path.is_empty() || path == "/" {
        return Some(v);
    }
    let mut cur = v;
    for seg in path.trim_start_matches('/').split('/').filter(|s| !s.is_empty()) {
        cur = match cur {
            Value::Object(map) => map.get(seg)?,
            Value::Array(arr) => {
                let i: usize = seg.parse().ok()?;
                arr.get(i)?
            }
            _ => return None,
        };
    }
    Some(cur)
}
