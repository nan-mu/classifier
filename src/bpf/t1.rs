//! T1: stack access virtualization.

use regex::Regex;
use std::sync::LazyLock;

use super::text::{join_line, split_line};

static STACK: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)
        \*\(u(?P<bits>32|64)\s\*\)\(r10\s-\s(?P<nat>0x[0-9a-fA-F]+)\)
        ",
    )
    .unwrap()
});

fn rewrite_stack(s: &str) -> String {
    let spans: Vec<_> = STACK
        .captures_iter(s)
        .map(|c| {
            let m = c.get(0).unwrap();
            let bits: u32 = c["bits"].parse().unwrap();
            let nat_s = &c["nat"];
            let nat = u64::from_str_radix(nat_s.trim_start_matches("0x"), 16).unwrap();
            (m.start(), m.end(), bits, nat)
        })
        .collect();
    if spans.is_empty() {
        return s.to_string();
    }
    let mut text = s.to_string();
    for (start, end, bits, nat) in spans.into_iter().rev() {
        let slot = nat / 4;
        let repl = if bits == 32 {
            format!("ws{slot}")
        } else {
            format!("rs{slot}")
        };
        text.replace_range(start..end, &repl);
    }
    text
}

/// Rewrite `*(u32|u64 *)(r10 - N)` into `wsX` / `rsX`.
pub fn t1(path: &[String]) -> Vec<String> {
    path.iter()
        .map(|line| match split_line(line) {
            Some((index, body)) => join_line(index, &rewrite_stack(body)),
            None => line.clone(),
        })
        .collect()
}
