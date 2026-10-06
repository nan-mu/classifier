//! Load bpftool-style assembly from a `bpf.toml` `[xdp].asm` field.

use anyhow::{Context, Result, bail};
use regex::Regex;
use std::sync::LazyLock;

static INSN_LINE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?x)
        ^\s*
        (?P<index>[0-9]+)
        :\s+
        (?P<body>.+?)
        \s*$
    ")
    .unwrap()
});

/// Parse `[xdp].asm` from a bpf.toml file into normalized `index: body` lines.
pub fn load_asm_from_toml(path: &std::path::Path) -> Result<Vec<String>> {
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("read {}", path.display()))?;
    let value: toml::Value = text
        .parse()
        .with_context(|| format!("parse toml {}", path.display()))?;
    let asm = value
        .get("xdp")
        .and_then(|x| x.get("asm"))
        .and_then(|a| a.as_str())
        .with_context(|| format!("missing [xdp].asm in {}", path.display()))?;
    normalize_asm(asm)
}

/// Drop function labels; normalize `N:\tbody` → `N: body`.
pub fn normalize_asm(asm: &str) -> Result<Vec<String>> {
    let mut out = Vec::new();
    for raw in asm.lines() {
        let line = raw.trim();
        if line.is_empty() {
            continue;
        }
        if line.contains('<') && line.ends_with(">:") {
            continue;
        }
        let Some(caps) = INSN_LINE.captures(line) else {
            bail!("unrecognized asm line: {line}");
        };
        let index = &caps["index"];
        let body = caps["body"].trim();
        out.push(format!("{index}: {body}"));
    }
    if out.is_empty() {
        bail!("no instructions in asm");
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strips_label_and_tabs() {
        let asm = "0000 <xdp>:\n\t0:\tw0 = 0x1\n\t1:\texit\n";
        let lines = normalize_asm(asm).unwrap();
        assert_eq!(lines, vec!["0: w0 = 0x1".to_string(), "1: exit".to_string()]);
    }
}
