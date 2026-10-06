//! T2: helper call rewrite.

use regex::Regex;
use std::sync::LazyLock;

use super::text::{join_line, split_line};

static CALL: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?x)^\s*call\s+(?P<id>0x[0-9a-fA-F]+|[0-9]+)\s*$").unwrap()
});

struct Helper {
    name: &'static str,
    n_args: u8,
    adjust: bool,
}

fn helper_of(id: u32) -> Option<Helper> {
    Some(match id {
        1 => Helper {
            name: "MapLookupElem",
            n_args: 2,
            adjust: false,
        },
        2 => Helper {
            name: "MapUpdateElem",
            n_args: 4,
            adjust: false,
        },
        3 => Helper {
            name: "MapDeleteElem",
            n_args: 2,
            adjust: false,
        },
        5 => Helper {
            name: "KtimeGetNs",
            n_args: 0,
            adjust: false,
        },
        6 => Helper {
            name: "TracePrintk",
            n_args: 5,
            adjust: false,
        },
        28 => Helper {
            name: "CsumDiff",
            n_args: 5,
            adjust: false,
        },
        65 => Helper {
            name: "XdpAdjustTail",
            n_args: 2,
            adjust: true,
        },
        _ => return None,
    })
}

fn parse_id(s: &str) -> Option<u32> {
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        u32::from_str_radix(hex, 16).ok()
    } else {
        s.parse().ok()
    }
}

fn rewrite_call(body: &str) -> Option<String> {
    let caps = CALL.captures(body)?;
    let id = parse_id(&caps["id"])?;
    let h = helper_of(id)?;
    let mut regs = String::new();
    if h.n_args > 0 {
        let list: Vec<String> = (1..=h.n_args).map(|i| format!("r{i}")).collect();
        regs = format!(", {} = UB", list.join(" "));
    }
    let adjust = if h.adjust { ", adjust" } else { "" };
    Some(format!("r0 = {}(V){regs}{adjust}", h.name))
}

/// Replace recognized `call` lines with helper register state.
pub fn t2(path: &[String]) -> Vec<String> {
    path.iter()
        .map(|line| match split_line(line) {
            Some((index, body)) => {
                if let Some(rewritten) = rewrite_call(body) {
                    join_line(index, &rewritten)
                } else {
                    line.clone()
                }
            }
            None => line.clone(),
        })
        .collect()
}
