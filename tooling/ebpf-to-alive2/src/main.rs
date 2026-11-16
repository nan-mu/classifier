use ebpf_to_alive2::{lift, load_function};
use std::env;
use std::fs;
use std::path::Path;
use std::process::{Command, exit};

fn main() {
    let mut args = env::args().skip(1);
    let cmd = args.next().unwrap_or_default();
    let status = match cmd.as_str() {
        "compile" => compile(&args.collect::<Vec<_>>()),
        "compile-corpus" => compile_corpus(&args.collect::<Vec<_>>()),
        _ => {
            eprintln!("usage: ebpf-to-alive2 compile <bpf.o> --out <file.alive> --origin <file.json> --report <file.toml> [--entry name]");
            eprintln!("       ebpf-to-alive2 compile-corpus --index <snapshot.toml> --out-dir <dir>");
            2
        }
    };
    exit(status);
}

fn compile(args: &[String]) -> i32 {
    let Some(input) = args.first() else {
        eprintln!("compile needs a BPF object path");
        return 2;
    };
    let out = flag(args, "--out");
    let origin = flag(args, "--origin");
    let report = flag(args, "--report");
    let entry = flag(args, "--entry");
    let (Some(out), Some(origin), Some(report)) = (out, origin, report) else {
        eprintln!("compile needs --out, --origin, and --report");
        return 2;
    };
    let bytes = match fs::read(input) {
        Ok(bytes) => bytes,
        Err(err) => {
            eprintln!("read {input}: {err}");
            return 1;
        }
    };
    let func = match load_function(&bytes, entry) {
        Ok(func) => func,
        Err(err) => {
            eprintln!("{input}: {err}");
            return 1;
        }
    };
    let compiled = match lift(&func) {
        Ok(compiled) => compiled,
        Err(err) => {
            eprintln!("{input}: {err}");
            return 1;
        }
    };
    if let Err(err) = publish(Path::new(out), compiled.alive.as_bytes()) {
        eprintln!("write {out}: {err}");
        return 1;
    }
    let elf_sha = match sha256(Path::new(input)) {
        Ok(sha) => sha,
        Err(err) => {
            let _ = fs::remove_file(out);
            eprintln!("hash {input}: {err}");
            return 1;
        }
    };
    let alive_sha = match sha256(Path::new(out)) {
        Ok(sha) => sha,
        Err(err) => {
            let _ = fs::remove_file(out);
            eprintln!("hash {out}: {err}");
            return 1;
        }
    };
    let origin_text = origin_json(&func.name, &func.section, &elf_sha, &alive_sha, &compiled.origin_insns, &func.bytes);
    if let Err(err) = publish(Path::new(origin), origin_text.as_bytes()) {
        let _ = fs::remove_file(out);
        eprintln!("write {origin}: {err}");
        return 1;
    }
    let report_text = format!(
        "status = \"converted\"\nentry = \"{}\"\nsection = \"{}\"\ninstructions = {}\nloop = {}\nelf_sha256 = \"{}\"\nalive_sha256 = \"{}\"\n",
        func.name,
        func.section,
        compiled.origin_insns.len(),
        compiled.loop_header,
        elf_sha,
        alive_sha
    );
    if let Err(err) = publish(Path::new(report), report_text.as_bytes()) {
        let _ = fs::remove_file(out);
        let _ = fs::remove_file(origin);
        eprintln!("write {report}: {err}");
        return 1;
    }
    0
}

fn compile_corpus(args: &[String]) -> i32 {
    let Some(index) = flag(args, "--index") else {
        eprintln!("compile-corpus needs --index");
        return 2;
    };
    let Some(out_dir) = flag(args, "--out-dir") else {
        eprintln!("compile-corpus needs --out-dir");
        return 2;
    };
    let text = match fs::read_to_string(index) {
        Ok(text) => text,
        Err(err) => {
            eprintln!("read {index}: {err}");
            return 1;
        }
    };
    let root = Path::new(index).parent().unwrap_or(Path::new("."));
    let mut names = Vec::new();
    let mut failed = 0;
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("name = ") {
            names.push(rest.trim_matches('"').to_string());
        } else if let Some(rest) = line.strip_prefix("object = ") {
            let name = names.last().cloned().unwrap_or_default();
            let path = root.join(rest.trim_matches('"'));
            let dir = Path::new(out_dir).join(&name);
            if fs::create_dir_all(&dir).is_err() {
                eprintln!("{name}: cannot create {}", dir.display());
                failed += 1;
                continue;
            }
            let code = compile(&[
                path.display().to_string(),
                "--out".into(),
                dir.join(format!("{name}.alive")).display().to_string(),
                "--origin".into(),
                dir.join(format!("{name}.origin.json")).display().to_string(),
                "--report".into(),
                dir.join("compile-report.toml").display().to_string(),
            ]);
            if code != 0 {
                failed += 1;
            }
        }
    }
    if failed == 0 { 0 } else { 1 }
}

fn origin_json(entry: &str, section: &str, elf_sha: &str, alive_sha: &str, insns: &[(u32, Vec<String>)], bytes: &[u8]) -> String {
    let mut body = String::from("{\n");
    body.push_str("  \"schema\": \"classifier-alive-origin-v1\",\n");
    body.push_str(&format!("  \"entry\": \"{entry}\",\n"));
    body.push_str(&format!("  \"section\": \"{section}\",\n"));
    body.push_str(&format!("  \"elf_sha256\": \"{elf_sha}\",\n"));
    body.push_str(&format!("  \"alive_sha256\": \"{alive_sha}\",\n"));
    body.push_str("  \"instructions\": [\n");
    for (n, (slot, irs)) in insns.iter().enumerate() {
        let at = *slot as usize * 8;
        let raw = if at + 8 <= bytes.len() { hex(&bytes[at..at + 8]) } else { String::new() };
        let ir = irs.iter().map(|name| format!("\"{name}\"")).collect::<Vec<_>>().join(", ");
        let comma = if n + 1 == insns.len() { "" } else { "," };
        body.push_str(&format!("    {{\"slot\": {slot}, \"offset\": {}, \"bytes\": \"{raw}\", \"ir\": [{ir}]}}{comma}\n", slot * 8));
    }
    body.push_str("  ]\n}\n");
    body
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn flag<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter().position(|arg| arg == name).and_then(|index| args.get(index + 1)).map(String::as_str)
}

fn publish(path: &Path, bytes: &[u8]) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|err| err.to_string())?;
    }
    let tmp = path.with_extension("partial");
    fs::write(&tmp, bytes).map_err(|err| err.to_string())?;
    fs::rename(&tmp, path).map_err(|err| err.to_string())
}

fn sha256(path: &Path) -> Result<String, String> {
    let output = Command::new("shasum").arg("-a").arg("256").arg(path).output().map_err(|err| err.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).to_string());
    }
    let text = String::from_utf8_lossy(&output.stdout);
    text.split_whitespace().next().map(str::to_string).ok_or_else(|| "shasum returned no hash".into())
}
