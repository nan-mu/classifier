//! `profile.toml` at the classifier root. ELF and bpf paths resolve under `../build`.

use std::fs;
use std::path::{Path, PathBuf};

/// Dual-arch outcome checked by `classifier test`.
///
/// `strict`: both sides complete, kind counts match, and branch expressions unify.
/// `weak`: both sides complete and kind counts match, but some branch expression does not.
/// `fail`: a side does not complete, or some segment's kind counts disagree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expect {
    Strict,
    Weak,
    Fail,
}

impl Expect {
    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "strict" => Some(Self::Strict),
            "weak" => Some(Self::Weak),
            "fail" => Some(Self::Fail),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Strict => "strict",
            Self::Weak => "weak",
            Self::Fail => "fail",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub name: String,
    pub elf: PathBuf,
    pub bpf: PathBuf,
    pub expect: Expect,
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
        return Err(format!(
            "CLASSIFIER_PROFILE is not a file: {}",
            path.display()
        ));
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
    let mut programs: Vec<(String, String, String, Expect)> = Vec::new();
    let mut cur: Option<RawProgram> = None;

    for (lineno, raw) in text.lines().enumerate() {
        let line = strip_comment(raw).trim();
        if line.is_empty() {
            continue;
        }
        if line == "[[program]]" {
            if let Some(done) = cur.take() {
                programs.push(finish_program(done)?);
            }
            cur = Some(RawProgram::default());
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
            "name" | "elf" | "bpf" | "expect" => {
                let slot = cur
                    .as_mut()
                    .ok_or_else(|| format!("line {}: {key} is outside [[program]]", lineno + 1))?;
                let stored = unquote(value)?;
                match key {
                    "name" => slot.name = Some(stored),
                    "elf" => slot.elf = Some(stored),
                    "bpf" => slot.bpf = Some(stored),
                    "expect" => slot.expect = Some(stored),
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
        .map(|(name, elf, bpf, expect)| Program {
            name,
            elf: build.join(elf),
            bpf: build.join(bpf),
            expect,
        })
        .collect();
    Ok(Profile { build, programs })
}

#[derive(Default)]
struct RawProgram {
    name: Option<String>,
    elf: Option<String>,
    bpf: Option<String>,
    expect: Option<String>,
}

fn finish_program(slot: RawProgram) -> Result<(String, String, String, Expect), String> {
    let RawProgram {
        name,
        elf,
        bpf,
        expect,
    } = slot;
    let (Some(name), Some(elf), Some(bpf)) = (name, elf, bpf) else {
        return Err("[[program]] needs name, elf, bpf, and expect".into());
    };
    if name.is_empty() {
        return Err("[[program]] needs name, elf, bpf, and expect".into());
    }
    let Some(expect) = expect.as_deref().and_then(Expect::parse) else {
        return Err("[[program]] expect must be \"strict\", \"weak\", or \"fail\"".into());
    };
    Ok((name, elf, bpf, expect))
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
expect = "weak"
"#;
        let profile = parse(text, Path::new("/repo")).unwrap();
        assert_eq!(profile.build, Path::new("/repo/../build"));
        assert_eq!(profile.programs.len(), 1);
        let program = profile.get("just_tx").unwrap();
        assert_eq!(program.elf, Path::new("/repo/../build/just_tx/just_tx.elf"));
        assert_eq!(program.expect, Expect::Weak);
    }
}
