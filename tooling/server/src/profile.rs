//! `profile.toml` at the classifier root. ELF and bpf paths resolve under `../build`.

use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub name: String,
    pub elf: PathBuf,
    pub bpf: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Profile {
    pub build: PathBuf,
    pub programs: Vec<Program>,
}

impl Profile {
    pub fn get(&self, name: &str) -> Option<&Program> {
        self.programs.iter().find(|p| p.name == name)
    }
}

/// Walk from the process cwd, then from this crate, until `profile.toml` is found.
pub fn load() -> Result<Profile, String> {
    let path = find_file()?;
    let text = fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let base = path
        .parent()
        .ok_or_else(|| format!("{} has no parent", path.display()))?;
    parse(&text, base)
}

pub fn find_file() -> Result<PathBuf, String> {
    if let Ok(explicit) = std::env::var("CLASSIFIER_PROFILE") {
        let path = PathBuf::from(explicit);
        if path.is_file() {
            return Ok(path);
        }
        return Err(format!("CLASSIFIER_PROFILE is not a file: {}", path.display()));
    }
    let mut starts = Vec::new();
    if let Ok(cwd) = std::env::current_dir() {
        starts.push(cwd);
    }
    starts.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")));
    for start in starts {
        let mut dir = start.as_path();
        loop {
            let candidate = dir.join("profile.toml");
            if candidate.is_file() {
                return Ok(candidate);
            }
            match dir.parent() {
                Some(parent) => dir = parent,
                None => break,
            }
        }
    }
    Err("profile.toml not found from cwd or the server crate".into())
}

pub fn parse(text: &str, base: &Path) -> Result<Profile, String> {
    let mut build_rel: Option<String> = None;
    let mut programs: Vec<(String, String, String)> = Vec::new();
    let mut cur: Option<(Option<String>, Option<String>, Option<String>)> = None;

    for (lineno, raw) in text.lines().enumerate() {
        let line = strip_comment(raw).trim();
        if line.is_empty() {
            continue;
        }
        if line == "[[program]]" {
            if let Some(done) = cur.take() {
                programs.push(finish_program(done)?);
            }
            cur = Some((None, None, None));
            continue;
        }
        let (key, value) = split_assign(line).map_err(|e| format!("line {}: {e}", lineno + 1))?;
        match key {
            "build" => {
                if cur.is_some() {
                    return Err(format!("line {}: build belongs at the top", lineno + 1));
                }
                build_rel = Some(unquote(value)?);
            }
            "name" | "elf" | "bpf" => {
                let slot = cur
                    .as_mut()
                    .ok_or_else(|| format!("line {}: {key} is outside [[program]]", lineno + 1))?;
                let stored = unquote(value)?;
                match key {
                    "name" => slot.0 = Some(stored),
                    "elf" => slot.1 = Some(stored),
                    "bpf" => slot.2 = Some(stored),
                    _ => unreachable!(),
                }
            }
            other => return Err(format!("line {}: unknown key {other}", lineno + 1)),
        }
    }
    if let Some(done) = cur.take() {
        programs.push(finish_program(done)?);
    }
    let build_rel = build_rel.ok_or("profile.toml needs build = \"...\"")?;
    if programs.is_empty() {
        return Err("profile.toml has no [[program]]".into());
    }
    let build = base.join(build_rel);
    let programs = programs
        .into_iter()
        .map(|(name, elf, bpf)| Program {
            name,
            elf: build.join(elf),
            bpf: build.join(bpf),
        })
        .collect();
    Ok(Profile { build, programs })
}

fn finish_program(
    slot: (Option<String>, Option<String>, Option<String>),
) -> Result<(String, String, String), String> {
    match slot {
        (Some(name), Some(elf), Some(bpf)) if !name.is_empty() => Ok((name, elf, bpf)),
        _ => Err("[[program]] needs name, elf, and bpf".into()),
    }
}

fn strip_comment(line: &str) -> &str {
    let mut in_quote = false;
    for (i, ch) in line.char_indices() {
        match ch {
            '"' => in_quote = !in_quote,
            '#' if !in_quote => return &line[..i],
            _ => {}
        }
    }
    line
}

fn split_assign(line: &str) -> Result<(&str, &str), String> {
    let Some((key, value)) = line.split_once('=') else {
        return Err(format!("expected key = value, got {line}"));
    };
    Ok((key.trim(), value.trim()))
}

fn unquote(value: &str) -> Result<String, String> {
    let bytes = value.as_bytes();
    if bytes.len() >= 2 && bytes[0] == b'"' && bytes[bytes.len() - 1] == b'"' {
        return Ok(value[1..value.len() - 1].to_string());
    }
    Err(format!("expected a quoted string, got {value}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_build_and_programs() {
        let text = r#"
build = "../build"
[[program]]
name = "just_tx"
elf = "just_tx/just_tx.elf"
bpf = "just_tx/bpf.o"
"#;
        let profile = parse(text, Path::new("/repo")).unwrap();
        assert_eq!(profile.build, Path::new("/repo/../build"));
        assert_eq!(profile.programs.len(), 1);
        assert_eq!(
            profile.get("just_tx").unwrap().elf,
            Path::new("/repo/../build/just_tx/just_tx.elf")
        );
    }
}
