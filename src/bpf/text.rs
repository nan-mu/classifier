//! Shared text helpers for BPF stages.

use regex::Regex;
use std::sync::LazyLock;

static LINE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^(?P<index>\d+):\s+(?P<body>.+)$").unwrap()
});

/// Split `index: body`.
pub fn split_line(line: &str) -> Option<(u32, &str)> {
    let caps = LINE.captures(line)?;
    let index: u32 = caps["index"].parse().ok()?;
    Some((index, caps.name("body")?.as_str()))
}

/// Format `index: body`.
pub fn join_line(index: u32, body: &str) -> String {
    format!("{index}: {body}")
}

/// `rN` / `wN` → register number N.
pub fn reg_num(name: &str) -> Option<u8> {
    let name = name.trim();
    let rest = name.strip_prefix('r').or_else(|| name.strip_prefix('w'))?;
    rest.parse().ok()
}

/// Parse immediate: `0x…`, decimal, optional leading `+`/`-`.
pub fn parse_imm(s: &str) -> Option<i64> {
    let s = s.trim();
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        return i64::from_str_radix(hex, 16).ok();
    }
    if let Some(hex) = s.strip_prefix("+0x").or_else(|| s.strip_prefix("+0X")) {
        return i64::from_str_radix(hex, 16).ok();
    }
    if let Some(hex) = s.strip_prefix("-0x").or_else(|| s.strip_prefix("-0X")) {
        return i64::from_str_radix(hex, 16).ok().map(|v| -v);
    }
    s.parse().ok()
}

/// Format a non-negative offset the way bpftool prints (`0x…` lowercase).
pub fn fmt_hex_u64(v: u64) -> String {
    format!("0x{v:x}")
}

/// True if `body` writes register `reg` (rN or wN).
pub fn defines_reg(body: &str, reg: u8) -> bool {
    let body = core_stmt(body);
    if body.starts_with(&format!("r{reg} = ")) || body.starts_with(&format!("w{reg} = ")) {
        return true;
    }
    if body.starts_with(&format!("r{reg} set ")) || body.starts_with(&format!("w{reg} set ")) {
        return true;
    }
    let alu = [
        format!("r{reg} += "),
        format!("r{reg} -= "),
        format!("r{reg} *= "),
        format!("r{reg} /= "),
        format!("r{reg} &= "),
        format!("r{reg} |= "),
        format!("r{reg} ^= "),
        format!("r{reg} <<= "),
        format!("r{reg} >>= "),
        format!("r{reg} s>>= "),
        format!("w{reg} += "),
        format!("w{reg} -= "),
        format!("w{reg} *= "),
        format!("w{reg} /= "),
        format!("w{reg} &= "),
        format!("w{reg} |= "),
        format!("w{reg} ^= "),
        format!("w{reg} <<= "),
        format!("w{reg} >>= "),
    ];
    alu.iter().any(|p| body.starts_with(p))
}

/// Body without trailing stage annotations.
pub fn core_stmt(body: &str) -> &str {
    const MARKERS: &[&str] = &[
        ", return value {",
        ", maplookup {",
        ", maplookup check",
        ", mapupdate {",
        ", mapdelete {",
        ", data_end check {",
    ];
    let mut end = body.len();
    for m in MARKERS {
        if let Some(i) = body.find(m) {
            end = end.min(i);
        }
    }
    body[..end].trim_end()
}

/// Whether this line's core statement is an R0 definition for T5.
pub fn is_r0_definition(body: &str) -> bool {
    let core = core_stmt(body);
    core.starts_with("r0 = ") || core.starts_with("w0 = ") || core.starts_with("r0 set ")
}

/// Parse `r0 = <imm>` / `w0 = <imm>` (no `ll`).
pub fn parse_r0_imm(body: &str) -> Option<&str> {
    let core = core_stmt(body);
    for prefix in ["r0 = ", "w0 = "] {
        if let Some(rest) = core.strip_prefix(prefix) {
            let imm = rest.trim();
            if imm.contains(' ') || imm.contains('(') {
                return None;
            }
            if parse_imm(imm).is_some() {
                return Some(imm);
            }
        }
    }
    None
}

/// Parse helper rewrite `r0 = Name(V), …`.
pub fn parse_helper_r0(body: &str) -> Option<&str> {
    let core = core_stmt(body);
    let rest = core.strip_prefix("r0 = ")?;
    let (name, after) = rest.split_once('(')?;
    if after.starts_with("V)") {
        return Some(name.trim());
    }
    None
}
