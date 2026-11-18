use ebpf_to_alive2::{lift, load_function, CompileError, Status};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::env;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::exit;

fn main() {
    let mut args = env::args().skip(1);
    let command = args.next().unwrap_or_default();
    let args: Vec<_> = args.collect();
    let result = match command.as_str() {
        "compile" => compile(&args),
        "compile-corpus" => compile_corpus(&args),
        _ => Err("usage: ebpf-to-alive2 compile <bpf.o> --out <file.alive> --origin <file.json> --report <file.toml> [--entry name]\n       ebpf-to-alive2 compile-corpus --index <snapshot.toml> --out-dir <dir>".into()),
    };
    if let Err(err) = result {
        eprintln!("{err}");
        exit(1);
    }
}

fn flags<'a>(
    args: &'a [String],
    allowed: &[&str],
) -> Result<std::collections::BTreeMap<&'a str, &'a str>, String> {
    let mut out = std::collections::BTreeMap::new();
    if args.len() % 2 != 0 {
        return Err("every option needs a value".into());
    }
    for pair in args.as_chunks::<2>().0 {
        if !allowed.contains(&pair[0].as_str()) {
            return Err(format!("unknown option {}", pair[0]));
        }
        if out.insert(pair[0].as_str(), pair[1].as_str()).is_some() {
            return Err(format!("duplicate option {}", pair[0]));
        }
    }
    Ok(out)
}

fn required<'a>(
    flags: &std::collections::BTreeMap<&str, &'a str>,
    key: &str,
) -> Result<&'a str, String> {
    flags
        .get(key)
        .copied()
        .ok_or_else(|| format!("missing {key}"))
}

fn compile(args: &[String]) -> Result<(), String> {
    let input = args.first().ok_or("compile needs a BPF object path")?;
    let opts = flags(
        &args[1..],
        &["--out", "--origin", "--report", "--entry", "--source-root"],
    )?;
    let outputs = [
        required(&opts, "--out")?,
        required(&opts, "--origin")?,
        required(&opts, "--report")?,
    ]
    .map(Path::new);
    compile_to(
        Path::new(input),
        outputs,
        opts.get("--entry").copied(),
        None,
        source_root(opts.get("--source-root").copied(), Path::new(input))?.as_deref(),
    )
}

fn resolved(path: &Path) -> Result<PathBuf, String> {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        env::current_dir().map_err(|e| e.to_string())?.join(path)
    };
    let mut result = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::ParentDir => {
                result.pop();
            }
            Component::CurDir => {}
            other => {
                result.push(other);
                if result.is_symlink() && !result.exists() {
                    return Err(format!("dangling symlink in path: {}", result.display()));
                }
                if result.exists() {
                    result = result.canonicalize().map_err(|e| e.to_string())?;
                }
            }
        }
    }
    Ok(result)
}

fn source_root(explicit: Option<&str>, anchor: &Path) -> Result<Option<Vec<PathBuf>>, String> {
    let explicit = explicit.map(|root| resolved(Path::new(root))).transpose()?;
    let mut discovered = Vec::new();
    for start in [
        resolved(anchor)?,
        resolved(&env::current_dir().map_err(|e| e.to_string())?)?,
    ] {
        for ancestor in start.ancestors() {
            if ancestor.join(".git").exists()
                && ancestor.join("alive2").is_dir()
                && ancestor.join("tooling").is_dir()
            {
                discovered.push(ancestor.to_path_buf());
                break;
            }
        }
    }
    if let Some(root) = explicit {
        discovered.push(root);
    }
    if discovered.is_empty() {
        return Err("cannot discover source root; pass --source-root".into());
    }
    Ok(Some(discovered))
}

fn reject_source_output(path: &Path, root: Option<&[PathBuf]>) -> Result<(), String> {
    if root.is_some_and(|roots| roots.iter().any(|root| path.starts_with(root))) {
        return Err(format!("output inside source root: {}", path.display()));
    }
    Ok(())
}

#[derive(Serialize)]
struct CompileReport<'a> {
    status: Status,
    entry: &'a str,
    section: &'a str,
    instructions: usize,
    #[serde(rename = "loop")]
    has_loop: bool,
    elf_sha256: &'a str,
    alive_sha256: &'a str,
    origin_sha256: &'a str,
    schema: &'static str,
    compiler_version: &'static str,
    origin_revision: u32,
    alive2_pin: &'static str,
    rocq_pin: &'static str,
    model_proof: &'static str,
    artifact_proof: &'static str,
    source_view: &'static str,
    implementation_proof: &'static str,
}

fn compile_to(
    input: &Path,
    outputs: [&Path; 3],
    entry: Option<&str>,
    expected: Option<(&str, u64)>,
    source_root: Option<&[PathBuf]>,
) -> Result<(), String> {
    let input_path = resolved(input)?;
    let paths = outputs
        .iter()
        .map(|p| resolved(p))
        .collect::<Result<Vec<_>, _>>()?;
    let failure_path = outputs[2].with_extension("failure.json");
    let failure_resolved = resolved(&failure_path)?;
    reject_source_output(&failure_resolved, source_root)?;
    if failure_resolved == input_path || paths.contains(&failure_resolved) || failure_path.is_dir()
    {
        return Err("failure report must be distinct from input and products".into());
    }
    for (i, path) in paths.iter().enumerate() {
        reject_source_output(path, source_root)?;
        if *path == input_path || paths[..i].contains(path) {
            return Err("input and all output paths must be distinct".into());
        }
        if path.is_dir() {
            return Err(format!("output is a directory: {}", path.display()));
        }
    }
    for path in outputs.iter().rev() {
        remove_if_present(path)?;
    }
    remove_if_present(&failure_path)?;
    let mut input_sha = None;
    let result = (|| -> Result<(), CompileError> {
        let bytes = fs::read(input).map_err(|e| {
            CompileError::new(
                Status::InternalError,
                "read_input",
                None,
                None,
                format!("read {}: {e}", input.display()),
            )
        })?;
        let elf_sha = sha256(&bytes);
        input_sha = Some(elf_sha.clone());
        if let Some((expected_sha, expected_size)) = expected {
            if expected_sha != elf_sha {
                return Err(format!("{}: ELF SHA-256 mismatch", input.display()).into());
            }
            if expected_size != bytes.len() as u64 {
                return Err(format!("{}: ELF size mismatch", input.display()).into());
            }
        }
        let func = load_function(&bytes, entry)?;
        let compiled = lift(&func)?;
        let alive_sha = sha256(compiled.alive.as_bytes());
        let instructions: Vec<_> = compiled
        .origin_insns
        .iter()
        .map(|(slot, ir)| {
            let at = *slot as usize * 8;
            let slots = func
                .insns
                .iter()
                .find(|insn| insn.index() == *slot)
                .map_or(1, |insn| insn.slots());
            let raw = &func.bytes[at..at + slots as usize * 8];
            serde_json::json!({"slot": slot, "offset": slot * 8, "bytes": hex(raw), "ir": ir,
                "checkpoint": compiled.checkpoints.get(slot),
                "decoded": func.insns.iter().find(|insn| insn.index() == *slot),
                "generated_instruction_ids": compiled.generated.iter().filter(|inst| inst.slot == Some(*slot)).map(|inst| &inst.id).collect::<Vec<_>>()})
        })
        .collect();
        let origin = serde_json::to_vec_pretty(&serde_json::json!({
        "schema": "classifier-alive-origin-v1", "entry": func.name, "section": func.section,
        "elf_sha256": elf_sha, "alive_sha256": alive_sha, "instructions": instructions,
        "state_mapping": "incomplete", "prologue_ir": compiled.prologue_ir,
        "checkpoint_schema": "register-bindings-v1",
        "unmapped_state": ["RAX", "PC embedding", "cstk", "code_id", "tail_call_count", "memory embedding", "events"],
        "origin_revision": 2, "generated_instructions": compiled.generated,
        "generated_cfg_edges": compiled.generated.iter().flat_map(|inst| inst.targets.iter().map(|target| serde_json::json!({"from": inst.block, "to": target, "instruction": inst.id}))).collect::<Vec<_>>(),
        "source_cfg_blocks": compiled.source_blocks, "source_cfg_edges": compiled.source_edges
    }))
    .map_err(|e| e.to_string())?;
        let report = toml::to_string(&CompileReport {
            status: Status::Converted,
            entry: &func.name,
            section: &func.section,
            instructions: func.insns.len(),
            has_loop: compiled.loop_header,
            elf_sha256: &elf_sha,
            alive_sha256: &alive_sha,
            origin_sha256: &sha256(&origin),
            schema: "classifier-alive-origin-v1",
            compiler_version: env!("CARGO_PKG_VERSION"),
            origin_revision: 2,
            alive2_pin: "adacbd5180ccf95075e9867c4f0c259f59c9fef2",
            rocq_pin: "78d65a77592aae84b31f86385f8be4ab83b45ccb",
            model_proof: "not_proven",
            artifact_proof: "not_proven",
            source_view: "incomplete",
            implementation_proof: "not_proven",
        })
        .map_err(|e| e.to_string())?;
        publish(
            outputs,
            [compiled.alive.as_bytes(), &origin, report.as_bytes()],
        )
        .map_err(|message| {
            CompileError::new(Status::InternalError, "publication", None, None, message)
        })
    })();
    if let Err(error) = &result {
        for path in outputs.iter().rev() {
            remove_if_present(path)?;
        }
        let body = serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "classifier-alive-failure-v1", "compiler_version": env!("CARGO_PKG_VERSION"),
            "alive2_pin": "adacbd5180ccf95075e9867c4f0c259f59c9fef2",
            "rocq_pin": "78d65a77592aae84b31f86385f8be4ab83b45ccb",
            "elf_sha256": input_sha,
            "status": error.status, "stage": error.stage, "slot": error.slot,
            "register": error.register, "message": error.message,
            "model_proof": "not_proven", "implementation_proof": "not_proven", "artifact_proof": "not_proven"
        }))
        .map_err(|e| e.to_string())?;
        let temporary = failure_path.with_extension(format!("{}.partial", std::process::id()));
        let mut created = false;
        let publication = (|| -> Result<(), String> {
            if let Some(parent) = temporary.parent() {
                fs::create_dir_all(parent).map_err(|e| e.to_string())?;
            }
            use std::io::Write;
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temporary)
                .map_err(|e| e.to_string())?;
            created = true;
            file.write_all(&body).map_err(|e| e.to_string())?;
            fs::rename(&temporary, &failure_path).map_err(|e| e.to_string())
        })();
        if publication.is_err() && created {
            let _ = fs::remove_file(temporary);
        }
        publication?;
    }
    result.map_err(|error| error.to_string())
}

#[derive(Deserialize)]
struct Snapshot {
    program: Vec<Program>,
}

#[derive(Deserialize)]
struct Program {
    name: String,
    object: PathBuf,
    sha256: String,
    size: u64,
    format: String,
    role: String,
    mode: String,
    entry: Option<String>,
}

fn compile_corpus(args: &[String]) -> Result<(), String> {
    let opts = flags(args, &["--index", "--out-dir", "--source-root"])?;
    let index = Path::new(required(&opts, "--index")?);
    let out_dir = Path::new(required(&opts, "--out-dir")?);
    let output_root = resolved(out_dir)?;
    let source_root = source_root(opts.get("--source-root").copied(), index)?;
    reject_source_output(&output_root, source_root.as_deref())?;
    if resolved(index)?.starts_with(&output_root) {
        return Err("corpus index must be outside the output directory".into());
    }
    let ownership = out_dir.join("corpus-outputs.json");
    let previous: Vec<String> = if ownership.exists() {
        serde_json::from_slice(&fs::read(&ownership).map_err(|e| e.to_string())?)
            .map_err(|e| format!("invalid corpus output ownership: {e}"))?
    } else {
        Vec::new()
    };
    for name in &previous {
        if !valid_program_name(name) || !resolved(&out_dir.join(name))?.starts_with(&output_root) {
            return Err("invalid corpus output ownership name or path".into());
        }
        remove_if_present(&out_dir.join(name).join("compile-report.toml"))?;
        remove_if_present(&out_dir.join(name).join("compile-report.failure.json"))?;
    }
    let text = fs::read_to_string(index).map_err(|e| format!("read {}: {e}", index.display()))?;
    let snapshot: Snapshot =
        toml::from_str(&text).map_err(|e| format!("invalid corpus manifest: {e}"))?;
    if snapshot.program.is_empty() {
        return Err("corpus manifest contains no programs".into());
    }
    let mut names = std::collections::BTreeSet::new();
    for program in &snapshot.program {
        if !valid_program_name(&program.name) || !names.insert(&program.name) {
            return Err(format!(
                "invalid or duplicate program name {:?}",
                program.name
            ));
        }
        if program.format != "elf-bpf-relocatable"
            || program.role != "bpf_object"
            || program.mode != "bpf"
        {
            return Err(format!(
                "{}: manifest entry is not a raw BPF ELF object",
                program.name
            ));
        }
        if program.sha256.len() != 64
            || !program
                .sha256
                .bytes()
                .all(|ch| ch.is_ascii_hexdigit() && !ch.is_ascii_uppercase())
        {
            return Err(format!("{}: invalid SHA-256", program.name));
        }
    }
    let root = index.parent().unwrap_or(Path::new("."));
    for program in &snapshot.program {
        if resolved(&root.join(&program.object))?.starts_with(&output_root) {
            return Err("corpus inputs must be outside the output directory".into());
        }
    }
    for name in previous {
        if !names.contains(&name) {
            let directory = out_dir.join(&name);
            remove_if_present(&directory.join(format!("{name}.alive")))?;
            remove_if_present(&directory.join(format!("{name}.origin.json")))?;
        }
    }
    fs::create_dir_all(out_dir).map_err(|e| e.to_string())?;
    let owned: Vec<_> = names.into_iter().collect();
    let staged = out_dir.join(format!(".corpus-outputs.{}.partial", std::process::id()));
    {
        use std::io::Write;
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&staged)
            .map_err(|e| e.to_string())?;
        if let Err(e) = file.write_all(&serde_json::to_vec(&owned).map_err(|e| e.to_string())?) {
            let _ = fs::remove_file(&staged);
            return Err(e.to_string());
        }
    }
    if let Err(e) = fs::rename(&staged, ownership) {
        let _ = fs::remove_file(staged);
        return Err(e.to_string());
    }
    let mut failures = Vec::new();
    for program in snapshot.program {
        let path = root.join(&program.object);
        let dir = out_dir.join(&program.name);
        let outputs = [
            dir.join(format!("{}.alive", program.name)),
            dir.join(format!("{}.origin.json", program.name)),
            dir.join("compile-report.toml"),
        ];
        let result = compile_to(
            &path,
            [&outputs[0], &outputs[1], &outputs[2]],
            program.entry.as_deref(),
            Some((&program.sha256, program.size)),
            source_root.as_deref(),
        );
        if let Err(e) = result {
            failures.push(format!("{}: {e}", program.name));
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("\n"))
    }
}

fn valid_program_name(name: &str) -> bool {
    !name.is_empty()
        && name
            .bytes()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == b'_')
}

fn remove_if_present(path: &Path) -> Result<(), String> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(format!("remove {}: {err}", path.display())),
    }
}

fn publish(paths: [&Path; 3], bytes: [&[u8]; 3]) -> Result<(), String> {
    use std::io::Write;
    let mut staged = Vec::new();
    let result = (|| {
        for (path, body) in paths.iter().zip(bytes) {
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).map_err(|e| e.to_string())?;
            }
            let temporary = path.with_file_name(format!(
                ".{}.{}.partial",
                path.file_name().unwrap_or_default().to_string_lossy(),
                std::process::id()
            ));
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temporary)
                .map_err(|e| format!("stage {}: {e}", temporary.display()))?;
            staged.push(temporary);
            file.write_all(body)
                .map_err(|e| format!("write {}: {e}", path.display()))?;
        }
        for (from, to) in staged.iter().zip(paths) {
            fs::rename(from, to).map_err(|e| format!("publish {}: {e}", to.display()))?;
        }
        Ok(())
    })();
    if result.is_err() {
        for path in staged.iter().map(PathBuf::as_path).chain(paths) {
            let _ = fs::remove_file(path);
        }
    }
    result
}

fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn failed_report_publication_removes_products_and_preserves_unrelated_files() {
        let directory = env::temp_dir().join(format!("alive-publication-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let paths = [
            directory.join("p.alive"),
            directory.join("origin.json"),
            directory.join("report.toml"),
        ];
        fs::create_dir(&paths[2]).unwrap();
        let unrelated = paths[2].join("unrelated");
        fs::write(&unrelated, "keep").unwrap();
        assert!(publish(
            [&paths[0], &paths[1], &paths[2]],
            [b"alive", b"origin", b"report"]
        )
        .is_err());
        assert!(!paths[0].exists());
        assert!(!paths[1].exists());
        assert_eq!(fs::read_to_string(unrelated).unwrap(), "keep");
        assert_eq!(fs::read_dir(&directory).unwrap().count(), 1);
        fs::remove_dir_all(directory).unwrap();
    }
}
