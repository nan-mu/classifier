//! Relative bpftool-style jump offsets (`+0x3e`, `-0x2b`).

use anyhow::{bail, Result};

/// Parse `+0xN` / `-0xN` / decimal relative offset text into a signed delta.
pub fn parse_rel_offset(offset: &str) -> Result<i32> {
    let s = offset.trim();
    if let Some(hex) = s.strip_prefix("+0x").or_else(|| s.strip_prefix("+0X")) {
        return i32::from_str_radix(hex, 16)
            .map_err(|_| anyhow::anyhow!("pathgen: bad jump offset `{offset}`"));
    }
    if let Some(hex) = s.strip_prefix("-0x").or_else(|| s.strip_prefix("-0X")) {
        let v = i32::from_str_radix(hex, 16)
            .map_err(|_| anyhow::anyhow!("pathgen: bad jump offset `{offset}`"))?;
        return Ok(-v);
    }
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        return i32::from_str_radix(hex, 16)
            .map_err(|_| anyhow::anyhow!("pathgen: bad jump offset `{offset}`"));
    }
    s.parse()
        .map_err(|_| anyhow::anyhow!("pathgen: bad jump offset `{offset}`"))
}

/// BPF / RV relative goto: `target = index + 1 + offset`.
pub fn resolve_target(index: u32, offset: &str) -> Result<u32> {
    let off = parse_rel_offset(offset)?;
    let target = index as i64 + 1 + off as i64;
    if target < 0 {
        bail!("pathgen: jump target {target} underflows at index {index}");
    }
    Ok(target as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolve_matches_rel_goto_formula() {
        assert_eq!(resolve_target(9, "+0x3e").unwrap(), 9 + 1 + 0x3e);
        assert_eq!(resolve_target(78, "-0x2b").unwrap(), 78 + 1 - 0x2b);
    }
}
