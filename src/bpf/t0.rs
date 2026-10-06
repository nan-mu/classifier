//! T0: forward control-path expansion.

use anyhow::{Result, bail};
use regex::Regex;
use std::collections::HashMap;
use std::sync::LazyLock;

use super::text::{join_line, split_line};

static COND: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)
        ^if\s+(?P<exp>.+)\s+goto\s+(?P<path>.+)$
        ",
    )
    .unwrap()
});

static GOTO: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?x)^goto\s+(?P<path>.+)$").unwrap()
});

static JUMP_PATH: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)
        ^(?P<off>[+-]?0x[0-9a-fA-F]+|[+-]?[0-9]+)
        (?:\s+<(?P<label>[^>]+)>)?
        $
        ",
    )
    .unwrap()
});

struct Prog {
    /// Instruction entries in order: (index, body).
    insns: Vec<(u32, String)>,
    /// index → position in `insns`.
    at: HashMap<u32, usize>,
}

impl Prog {
    fn parse(lines: &[String]) -> Result<Self> {
        let mut insns = Vec::new();
        let mut at = HashMap::new();
        for line in lines {
            let Some((index, body)) = split_line(line) else {
                bail!("T0: bad line `{line}`");
            };
            if at.contains_key(&index) {
                bail!("T0: duplicate index {index}");
            }
            at.insert(index, insns.len());
            insns.push((index, body.to_string()));
        }
        if insns.is_empty() {
            bail!("T0: empty program");
        }
        // indices must be strictly increasing
        for w in insns.windows(2) {
            if w[0].0 >= w[1].0 {
                bail!("T0: indices not strictly ordered");
            }
        }
        Ok(Self { insns, at })
    }

    fn next_pos(&self, pos: usize) -> Option<usize> {
        let n = pos + 1;
        if n < self.insns.len() {
            Some(n)
        } else {
            None
        }
    }
}

#[derive(Debug)]
enum Ctrl {
    Cond { exp: String, target: u32 },
    Goto { target: u32 },
    Exit,
    Other,
}

fn parse_offset(path: &str) -> Result<(i32, Option<u32>)> {
    let path = path.trim();
    let Some(caps) = JUMP_PATH.captures(path) else {
        bail!("T0: cannot parse jump path `{path}`");
    };
    let off_s = &caps["off"];
    let off = if let Some(hex) = off_s.strip_prefix("+0x").or_else(|| off_s.strip_prefix("+0X")) {
        i32::from_str_radix(hex, 16).ok()
    } else if let Some(hex) = off_s.strip_prefix("-0x").or_else(|| off_s.strip_prefix("-0X")) {
        i32::from_str_radix(hex, 16).ok().map(|v| -v)
    } else if let Some(hex) = off_s.strip_prefix("0x").or_else(|| off_s.strip_prefix("0X")) {
        i32::from_str_radix(hex, 16).ok()
    } else {
        off_s.parse().ok()
    };
    let Some(off) = off else {
        bail!("T0: bad jump offset in `{path}`");
    };
    let label_target = caps.name("label").and_then(|m| {
        let s = m.as_str();
        // xdp_prog1+0x1c8 → byte offset after optional symbol
        let byte = if let Some((_, b)) = s.rsplit_once('+') {
            b
        } else {
            return None;
        };
        let byte = byte.strip_prefix("0x").or_else(|| byte.strip_prefix("0X")).unwrap_or(byte);
        let bytes = u32::from_str_radix(byte, 16).ok()?;
        Some(bytes / 8)
    });
    Ok((off, label_target))
}

fn resolve_target(index: u32, path: &str) -> Result<u32> {
    let (off, label_target) = parse_offset(path)?;
    let target = (index as i64 + 1 + off as i64) as u32;
    if let Some(lt) = label_target {
        if lt != target {
            bail!(
                "T0: jump label target {lt} != computed {target} at index {index}"
            );
        }
    }
    Ok(target)
}

fn classify_body(index: u32, body: &str) -> Result<Ctrl> {
    let body = body.trim();
    if body == "exit" {
        return Ok(Ctrl::Exit);
    }
    if let Some(caps) = COND.captures(body) {
        let exp = caps["exp"].trim().to_string();
        let target = resolve_target(index, caps["path"].trim())?;
        return Ok(Ctrl::Cond { exp, target });
    }
    if let Some(caps) = GOTO.captures(body) {
        let target = resolve_target(index, caps["path"].trim())?;
        return Ok(Ctrl::Goto { target });
    }
    Ok(Ctrl::Other)
}

fn expand(prog: &Prog, pos: usize, prefix: &[String], out: &mut Vec<Vec<String>>) -> Result<()> {
    let (index, body) = &prog.insns[pos];
    let line = join_line(*index, body);
    match classify_body(*index, body)? {
        Ctrl::Exit => {
            let mut path = prefix.to_vec();
            path.push(line);
            out.push(path);
            Ok(())
        }
        Ctrl::Cond { exp, target } => {
            if target > *index {
                // forward: taken then fallthrough
                if !prog.at.contains_key(&target) {
                    bail!("T0: forward cond target {target} is not an instruction entry");
                }
                // Forward cond: drop the original `if`, keep only the path assert.
                let taken_pos = prog.at[&target];
                let mut taken = prefix.to_vec();
                taken.push(join_line(*index, &format!("assert ({exp}) == true")));
                expand(prog, taken_pos, &taken, out)?;

                let Some(next) = prog.next_pos(pos) else {
                    bail!("T0: fallthrough past end at {index}");
                };
                let mut fall = prefix.to_vec();
                fall.push(join_line(*index, &format!("assert ({exp}) == false")));
                expand(prog, next, &fall, out)?;
                Ok(())
            } else {
                // backward: keep original `if`, linear next
                let mut path = prefix.to_vec();
                path.push(line);
                if let Some(next) = prog.next_pos(pos) {
                    expand(prog, next, &path, out)
                } else {
                    out.push(path);
                    Ok(())
                }
            }
        }
        Ctrl::Goto { target } => {
            if target > *index {
                if !prog.at.contains_key(&target) {
                    bail!("T0: forward goto target {target} is not an instruction entry");
                }
                let mut path = prefix.to_vec();
                path.push(line);
                expand(prog, prog.at[&target], &path, out)
            } else {
                let mut path = prefix.to_vec();
                path.push(line);
                if let Some(next) = prog.next_pos(pos) {
                    expand(prog, next, &path, out)
                } else {
                    out.push(path);
                    Ok(())
                }
            }
        }
        Ctrl::Other => {
            let mut path = prefix.to_vec();
            path.push(line);
            match prog.next_pos(pos) {
                Some(next) => expand(prog, next, &path, out),
                None => {
                    out.push(path);
                    Ok(())
                }
            }
        }
    }
}

/// Expand forward control into ordered path texts.
pub fn t0(lines: &[String]) -> Result<Vec<Vec<String>>> {
    let prog = Prog::parse(lines)?;
    let mut out = Vec::new();
    expand(&prog, 0, &[], &mut out)?;
    Ok(out)
}
