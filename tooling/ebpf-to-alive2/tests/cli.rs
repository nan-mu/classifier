use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

struct Run(PathBuf);

impl Run {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ebpf-alive-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }

    fn output(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }

    fn compile(&self, input: &Path) -> Output {
        Command::new(env!("CARGO_BIN_EXE_ebpf-to-alive2"))
            .arg("compile")
            .arg(input)
            .arg("--out")
            .arg(self.output("program.alive"))
            .arg("--origin")
            .arg(self.output("origin.json"))
            .arg("--report")
            .arg(self.output("report.toml"))
            .output()
            .unwrap()
    }

    fn corpus(&self, manifest: &str) -> Output {
        let index = self.output("index.toml");
        fs::write(&index, manifest).unwrap();
        Command::new(env!("CARGO_BIN_EXE_ebpf-to-alive2"))
            .arg("compile-corpus")
            .arg("--index")
            .arg(index)
            .arg("--out-dir")
            .arg(self.output("corpus"))
            .output()
            .unwrap()
    }
}

impl Drop for Run {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn corpus(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../alive2/corpus/bpf/{name}/bpf.o"))
}

#[test]
fn published_hashes_and_origin_slots_match_the_artifacts() {
    let run = Run::new();
    let result = run.compile(&corpus("just_drop"));
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let alive = fs::read(run.output("program.alive")).unwrap();
    let origin: serde_json::Value =
        serde_json::from_slice(&fs::read(run.output("origin.json")).unwrap()).unwrap();
    let report: toml::Value =
        toml::from_str(&fs::read_to_string(run.output("report.toml")).unwrap()).unwrap();
    assert_eq!(report["status"].as_str(), Some("converted"));
    assert_eq!(report["implementation_proof"].as_str(), Some("not_proven"));
    assert_eq!(
        origin["alive_sha256"].as_str().unwrap(),
        format!("{:x}", Sha256::digest(alive))
    );
    let bytes = fs::read(corpus("just_drop")).unwrap();
    assert_eq!(
        origin["elf_sha256"].as_str().unwrap(),
        format!("{:x}", Sha256::digest(&bytes))
    );
    let func = ebpf_to_alive2::load_function(&bytes, None).unwrap();
    let insns = origin["instructions"].as_array().unwrap();
    assert_eq!(insns.len(), func.insns.len());
    assert!(insns
        .iter()
        .any(|insn| insn["bytes"].as_str().unwrap().len() == 32));
}

#[test]
fn failed_recompile_removes_all_old_success_artifacts() {
    let run = Run::new();
    assert!(run.compile(&corpus("div2")).status.success());
    let broken = run.output("bad.o");
    fs::write(&broken, b"not an ELF").unwrap();
    assert!(!run.compile(&broken).status.success());
    for name in ["program.alive", "origin.json", "report.toml"] {
        assert!(!run.output(name).exists(), "stale {name}");
    }
}

#[test]
fn output_alias_cannot_delete_the_input() {
    let run = Run::new();
    let input = run.output("program.alive");
    let bytes = fs::read(corpus("div2")).unwrap();
    fs::write(&input, &bytes).unwrap();
    assert!(!run.compile(&input).status.success());
    assert_eq!(fs::read(input).unwrap(), bytes);
}

#[test]
fn invalid_empty_and_traversing_manifests_fail() {
    let run = Run::new();
    for text in [
        "",
        "program = []",
        "[[program]]\nname = '../escape'\n",
        "not toml",
    ] {
        assert!(!run.corpus(text).status.success(), "accepted {text:?}");
    }
}

#[test]
fn manifest_hash_mismatch_cannot_leave_a_success_report() {
    let run = Run::new();
    let object = corpus("div2").canonicalize().unwrap();
    let bytes = fs::read(&object).unwrap();
    let make = |sha: &str| {
        format!("[[program]]\nname = 'div2'\nobject = '{}'\nsha256 = '{sha}'\nsize = {}\nformat = 'elf-bpf-relocatable'\nrole = 'bpf_object'\nmode = 'bpf'\n", object.display(), bytes.len())
    };
    let good = make(&format!("{:x}", Sha256::digest(&bytes)));
    assert!(run.corpus(&good).status.success());
    let bad = make(&"0".repeat(64));
    let result = run.corpus(&bad);
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("SHA-256 mismatch"));
    assert!(!run.output("corpus/div2/compile-report.toml").exists());
}

fn manifest_for(names: &[&str]) -> String {
    names.iter().map(|name| {
        let object = corpus(name).canonicalize().unwrap();
        let bytes = fs::read(&object).unwrap();
        format!("[[program]]\nname = '{name}'\nobject = '{}'\nsha256 = '{:x}'\nsize = {}\nformat = 'elf-bpf-relocatable'\nrole = 'bpf_object'\nmode = 'bpf'\n", object.display(), Sha256::digest(&bytes), bytes.len())
    }).collect()
}

#[test]
fn manifest_failure_invalidates_all_previously_owned_reports() {
    let run = Run::new();
    assert!(run
        .corpus(&manifest_for(&["div2", "just_drop"]))
        .status
        .success());
    assert!(!run.corpus("program = []").status.success());
    for name in ["div2", "just_drop"] {
        assert!(!run
            .output(&format!("corpus/{name}/compile-report.toml"))
            .exists());
    }
}

#[test]
fn programs_removed_from_manifest_lose_their_owned_artifacts() {
    let run = Run::new();
    assert!(run
        .corpus(&manifest_for(&["div2", "just_drop"]))
        .status
        .success());
    fs::write(run.output("corpus/keep.txt"), "unrelated").unwrap();
    assert!(run.corpus(&manifest_for(&["just_drop"])).status.success());
    for file in ["div2.alive", "div2.origin.json", "compile-report.toml"] {
        assert!(!run.output(&format!("corpus/div2/{file}")).exists());
    }
    assert_eq!(
        fs::read_to_string(run.output("corpus/keep.txt")).unwrap(),
        "unrelated"
    );
    assert!(run.output("corpus/just_drop/compile-report.toml").exists());
}
