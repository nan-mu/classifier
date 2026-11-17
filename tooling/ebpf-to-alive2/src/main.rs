use ebpf_to_alive2::{lift, load_function};
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
    let opts = flags(&args[1..], &["--out", "--origin", "--report", "--entry"])?;
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
    )
}

fn resolved(path: &Path) -> Result<PathBuf, String> {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        env::current_dir().map_err(|e| e.to_string())?.join(path)
    };
    let mut normalized = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::ParentDir => {
                normalized.pop();
            }
            Component::CurDir => {}
            other => normalized.push(other),
        }
    }
    if normalized.exists() {
        return normalized.canonicalize().map_err(|e| e.to_string());
    }
    let parent = normalized.parent().ok_or("output has no parent")?;
    Ok(resolved(parent)?.join(normalized.file_name().ok_or("output has no filename")?))
}

#[derive(Serialize)]
struct CompileReport<'a> {
    status: &'static str,
    entry: &'a str,
    section: &'a str,
    instructions: usize,
    #[serde(rename = "loop")]
    has_loop: bool,
    elf_sha256: &'a str,
    alive_sha256: &'a str,
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
) -> Result<(), String> {
    let input_path = resolved(input)?;
    let paths = outputs
        .iter()
        .map(|p| resolved(p))
        .collect::<Result<Vec<_>, _>>()?;
    for (i, path) in paths.iter().enumerate() {
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
    let bytes = fs::read(input).map_err(|e| format!("read {}: {e}", input.display()))?;
    let elf_sha = sha256(&bytes);
    if let Some((expected_sha, expected_size)) = expected {
        if expected_sha != elf_sha {
            return Err(format!("{}: ELF SHA-256 mismatch", input.display()));
        }
        if expected_size != bytes.len() as u64 {
            return Err(format!("{}: ELF size mismatch", input.display()));
        }
    }
    let func = load_function(&bytes, entry).map_err(|e| format!("{}: {e}", input.display()))?;
    let compiled = lift(&func).map_err(|e| format!("{}: {e}", input.display()))?;
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
            serde_json::json!({"slot": slot, "offset": slot * 8, "bytes": hex(raw), "ir": ir})
        })
        .collect();
    let origin = serde_json::to_vec_pretty(&serde_json::json!({
        "schema": "classifier-alive-origin-v1", "entry": func.name, "section": func.section,
        "elf_sha256": elf_sha, "alive_sha256": alive_sha, "instructions": instructions,
        "state_mapping": "incomplete"
    }))
    .map_err(|e| e.to_string())?;
    let report = toml::to_string(&CompileReport {
        status: "converted",
        entry: &func.name,
        section: &func.section,
        instructions: func.insns.len(),
        has_loop: compiled.loop_header,
        elf_sha256: &elf_sha,
        alive_sha256: &alive_sha,
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
    let opts = flags(args, &["--index", "--out-dir"])?;
    let index = Path::new(required(&opts, "--index")?);
    let out_dir = Path::new(required(&opts, "--out-dir")?);
    let text = fs::read_to_string(index).map_err(|e| format!("read {}: {e}", index.display()))?;
    let snapshot: Snapshot =
        toml::from_str(&text).map_err(|e| format!("invalid corpus manifest: {e}"))?;
    if snapshot.program.is_empty() {
        return Err("corpus manifest contains no programs".into());
    }
    let mut names = std::collections::BTreeSet::new();
    for program in &snapshot.program {
        if program.name.is_empty()
            || !program
                .name
                .bytes()
                .all(|ch| ch.is_ascii_alphanumeric() || ch == b'_')
            || !names.insert(&program.name)
        {
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

fn remove_if_present(path: &Path) -> Result<(), String> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(format!("remove {}: {err}", path.display())),
    }
}

fn publish(paths: [&Path; 3], bytes: [&[u8]; 3]) -> Result<(), String> {
    let temporary: Vec<_> = paths
        .iter()
        .map(|path| {
            path.with_file_name(format!(
                ".{}.{}.partial",
                path.file_name().unwrap_or_default().to_string_lossy(),
                std::process::id()
            ))
        })
        .collect();
    let result = (|| {
        for (path, body) in temporary.iter().zip(bytes) {
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).map_err(|e| e.to_string())?;
            }
            fs::write(path, body).map_err(|e| format!("write {}: {e}", path.display()))?;
        }
        for (from, to) in temporary.iter().zip(paths) {
            fs::rename(from, to).map_err(|e| format!("publish {}: {e}", to.display()))?;
        }
        Ok(())
    })();
    if result.is_err() {
        for path in temporary.iter().map(PathBuf::as_path).chain(paths) {
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
