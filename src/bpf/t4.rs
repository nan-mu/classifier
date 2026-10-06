//! T4: Map helper parameter induction and value access.

use regex::Regex;
use std::sync::LazyLock;

use super::text::{
    core_stmt, defines_reg, fmt_hex_u64, join_line, parse_imm, reg_num, split_line,
};

static LOOKUP: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^r0\s+=\s+MapLookupElem\(V\),\s+r1\s+r2\s+=\s+UB(?P<rest>.*)$",
    )
    .unwrap()
});
static UPDATE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^r0\s+=\s+MapUpdateElem\(V\),\s+r1\s+r2\s+r3\s+r4\s+=\s+UB(?P<rest>.*)$",
    )
    .unwrap()
});
static DELETE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^r0\s+=\s+MapDeleteElem\(V\),\s+r1\s+r2\s+=\s+UB(?P<rest>.*)$",
    )
    .unwrap()
});
static NULL_ASSERT: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?x)^assert\s+\(r0\s+==\s+0x0\)\s+==\s+false(?P<rest>.*)$").unwrap()
});
static MAPLOOKUP_ANN: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"maplookup\s+\{\s*(?P<idx>0x[0-9a-fA-F]+|\d+)\s*,\s*\[(?P<key>[^\]]*)\]\s*\}",
    )
    .unwrap()
});
static MAP_ADDR_SET: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^r(?P<dst>\d+)\s+set\s+map_address\s+\{\s*(?P<idx>0x[0-9a-fA-F]+|\d+)\s*,\s*\[(?P<key>[^\]]*)\]\s*\}\s+\+\s+(?P<off>0x[0-9a-fA-F]+|\d+)$",
    )
    .unwrap()
});
static COPY: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^r(?P<dst>\d+)\s+=\s+r(?P<src>\d+)$").unwrap());
static ADD_IMM: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^r(?P<dst>\d+)\s+\+=\s+(?P<imm>0x[0-9a-fA-F]+|\d+)$").unwrap()
});
static MEM_LOAD: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^(?P<dst>[rw]\d+)\s+=\s+\*\(u(?P<bits>8|16|32|64)\s\*\)\(r(?P<base>\d+)\s+\+\s+(?P<off>0x[0-9a-fA-F]+|\d+)\)$",
    )
    .unwrap()
});
static MEM_STORE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^\*\(u(?P<bits>8|16|32|64)\s\*\)\(r(?P<base>\d+)\s+\+\s+(?P<off>0x[0-9a-fA-F]+|\d+)\)\s+=\s+(?P<val>.+)$",
    )
    .unwrap()
});
static IMM_ASSIGN: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^r(?P<dst>\d+)\s+=\s+(?P<imm>0x[0-9a-fA-F]+|\d+)$").unwrap()
});
static R10_COPY: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^r(?P<dst>\d+)\s+=\s+r10$").unwrap());
static R10_ADD: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^r(?P<dst>\d+)\s+\+=\s+(?P<imm>-?0x[0-9a-fA-F]+|-?\d+)$").unwrap()
});

#[derive(Clone, Debug)]
struct MapAddr {
    map_index: String,
    key: String,
    offset: u64,
}

fn latest_imm(path: &[String], before: usize, reg: u8) -> Option<String> {
    for line in path[..before].iter().rev() {
        let Some((_, body)) = split_line(line) else {
            continue;
        };
        let core = core_stmt(body);
        if let Some(c) = IMM_ASSIGN.captures(core) {
            if c["dst"].parse::<u8>().ok() == Some(reg) {
                let imm = c["imm"].to_string();
                // reject if later overwritten — we're scanning newest first, so this is latest
                return Some(imm);
            }
        }
        if defines_reg(core, reg) {
            return None;
        }
    }
    None
}

/// Resolve `rX = r10; rX += -N` with N = 4*k > 0. Returns (N, key ws list).
fn latest_stack_ptr(path: &[String], before: usize, reg: u8) -> Option<(u64, Vec<String>)> {
    // Find latest `rX += -N`, then ensure prior def is `rX = r10` with no intervening writes.
    let mut add_pos = None;
    let mut n = 0i64;
    for (i, line) in path[..before].iter().enumerate().rev() {
        let Some((_, body)) = split_line(line) else {
            continue;
        };
        let core = core_stmt(body);
        if let Some(c) = R10_ADD.captures(core) {
            if c["dst"].parse::<u8>().ok() == Some(reg) {
                n = parse_imm(&c["imm"])?;
                add_pos = Some(i);
                break;
            }
        }
        if defines_reg(core, reg) {
            return None;
        }
    }
    let add_pos = add_pos?;
    if n >= 0 || n % 4 != 0 {
        return None;
    }
    let n_abs = (-n) as u64;
    // Between r10 copy and add, no other writes to reg; find r10 copy
    for line in path[..add_pos].iter().rev() {
        let Some((_, body)) = split_line(line) else {
            continue;
        };
        let core = core_stmt(body);
        if let Some(c) = R10_COPY.captures(core) {
            if c["dst"].parse::<u8>().ok() == Some(reg) {
                let k = n_abs / 4;
                let key: Vec<String> = (1..=k).rev().map(|i| format!("ws{i}")).collect();
                // wsk .. ws1 means (1..=k).rev() → wsk, ws(k-1), ..., ws1. Good.
                return Some((n_abs, key));
            }
        }
        if defines_reg(core, reg) {
            return None;
        }
    }
    None
}

fn t4_1(path: &[String]) -> Vec<String> {
    let mut out = path.to_vec();
    for i in 0..out.len() {
        let Some((index, body)) = split_line(&out[i]) else {
            continue;
        };
        if body.contains("maplookup {") {
            continue;
        }
        if LOOKUP.is_match(core_stmt(body)) || LOOKUP.is_match(body) {
            // match on body start
        }
        let Some(c) = LOOKUP.captures(body) else {
            continue;
        };
        if c.name("rest").is_some_and(|m| m.as_str().contains("maplookup")) {
            continue;
        }
        let map_index = match latest_imm(&out, i, 1) {
            Some(v) => v,
            None => continue,
        };
        let Some((_, key)) = latest_stack_ptr(&out, i, 2) else {
            continue;
        };
        let ann = format!(
            "{body}, maplookup {{ {map_index}, [{}] }}",
            key.join(", ")
        );
        out[i] = join_line(index, &ann);
    }
    out
}

fn t4_2(path: &[String]) -> Vec<String> {
    let mut out = path.to_vec();
    for i in 0..out.len() {
        let Some((index, body)) = split_line(&out[i]) else {
            continue;
        };
        if body.contains("maplookup check") {
            continue;
        }
        if !NULL_ASSERT.is_match(core_stmt(body)) && !NULL_ASSERT.is_match(body) {
            // check exact form on core / body without prior check
            let core = core_stmt(body);
            if core != "assert (r0 == 0x0) == false" {
                continue;
            }
        } else if core_stmt(body) != "assert (r0 == 0x0) == false"
            && !body.starts_with("assert (r0 == 0x0) == false")
        {
            continue;
        }
        if core_stmt(body) != "assert (r0 == 0x0) == false" {
            continue;
        }
        // find nearest maplookup-annotated MapLookupElem with no r0 def between
        let mut found = false;
        for line in out[..i].iter().rev() {
            let Some((_, b)) = split_line(line) else {
                continue;
            };
            if b.contains("maplookup {") && b.contains("MapLookupElem") {
                found = true;
                break;
            }
            if defines_reg(b, 0) {
                break;
            }
        }
        if found {
            out[i] = join_line(index, &format!("{body}, maplookup check"));
        }
    }
    out
}

fn parse_map_addr_set(body: &str) -> Option<(u8, MapAddr)> {
    let c = MAP_ADDR_SET.captures(body)?;
    Some((
        c["dst"].parse().ok()?,
        MapAddr {
            map_index: c["idx"].to_string(),
            key: c["key"].trim().to_string(),
            offset: parse_imm(&c["off"]).filter(|v| *v >= 0)? as u64,
        },
    ))
}

fn format_map_addr(reg: u8, a: &MapAddr) -> String {
    format!(
        "r{reg} set map_address {{ {}, [{}] }} + {}",
        a.map_index,
        a.key,
        fmt_hex_u64(a.offset)
    )
}

fn t4_3(path: &[String]) -> Vec<String> {
    let mut addrs: HashMapLike = HashMapLike::default();
    let mut active_lookup: Option<MapAddr> = None;
    let mut r0_is_map = false;
    let mut out = Vec::with_capacity(path.len());

    for line in path {
        let Some((index, body)) = split_line(line) else {
            out.push(line.clone());
            continue;
        };

        if let Some(c) = MAPLOOKUP_ANN.captures(body) {
            active_lookup = Some(MapAddr {
                map_index: c["idx"].to_string(),
                key: c["key"].trim().to_string(),
                offset: 0,
            });
            r0_is_map = false;
            out.push(line.clone());
            continue;
        }

        if body.contains("maplookup check") {
            if let Some(ref a) = active_lookup {
                r0_is_map = true;
                addrs.insert(
                    0,
                    MapAddr {
                        map_index: a.map_index.clone(),
                        key: a.key.clone(),
                        offset: 0,
                    },
                );
            }
            out.push(line.clone());
            continue;
        }

        if let Some((reg, addr)) = parse_map_addr_set(body) {
            addrs.insert(reg, addr);
            out.push(line.clone());
            continue;
        }

        if let Some(c) = COPY.captures(core_stmt(body)) {
            let dst: u8 = c["dst"].parse().unwrap_or(255);
            let src: u8 = c["src"].parse().unwrap_or(255);
            if let Some(addr) = addrs.get(src) {
                let new_addr = addr.clone();
                let text = format_map_addr(dst, &new_addr);
                addrs.insert(dst, new_addr);
                if dst == 0 {
                    r0_is_map = true;
                }
                out.push(join_line(index, &text));
                continue;
            }
            addrs.remove(dst);
            if dst == 0 {
                r0_is_map = false;
            }
            out.push(line.clone());
            continue;
        }

        if let Some(c) = ADD_IMM.captures(core_stmt(body)) {
            let dst: u8 = c["dst"].parse().unwrap_or(255);
            let imm = parse_imm(&c["imm"]).unwrap_or(-1);
            if imm >= 0 {
                if let Some(addr) = addrs.get(dst) {
                    let mut new_addr = addr.clone();
                    new_addr.offset = addr.offset + imm as u64;
                    let text = format_map_addr(dst, &new_addr);
                    addrs.insert(dst, new_addr);
                    out.push(join_line(index, &text));
                    continue;
                }
            }
            addrs.remove(dst);
            out.push(line.clone());
            continue;
        }

        // invalidate written regs
        for r in 0u8..=10 {
            if defines_reg(body, r) {
                addrs.remove(r);
                if r == 0 {
                    r0_is_map = false;
                }
            }
        }
        let _ = r0_is_map;
        out.push(line.clone());
    }
    out
}

/// Tiny map wrapper to avoid importing HashMap name clash noise in signatures.
#[derive(Default)]
struct HashMapLike {
    inner: std::collections::HashMap<u8, MapAddr>,
}

impl HashMapLike {
    fn insert(&mut self, k: u8, v: MapAddr) {
        self.inner.insert(k, v);
    }
    fn get(&self, k: u8) -> Option<&MapAddr> {
        self.inner.get(&k)
    }
    fn remove(&mut self, k: u8) {
        self.inner.remove(&k);
    }
}

fn t4_4(path: &[String]) -> Vec<String> {
    let mut addrs: HashMapLike = HashMapLike::default();
    let mut out = Vec::with_capacity(path.len());

    for line in path {
        let Some((index, body)) = split_line(line) else {
            out.push(line.clone());
            continue;
        };

        if body.contains("maplookup check") {
            // r0 becomes map_address + 0 from nearest maplookup — re-parse from path context
            // Prefer already-propagated state: if previous lines set r0 via t4_3 check handling,
            // we need the maplookup info. Scan backward.
            for prev in out.iter().rev() {
                let Some((_, b)) = split_line(prev) else {
                    continue;
                };
                if let Some(c) = MAPLOOKUP_ANN.captures(b) {
                    addrs.insert(
                        0,
                        MapAddr {
                            map_index: c["idx"].to_string(),
                            key: c["key"].trim().to_string(),
                            offset: 0,
                        },
                    );
                    break;
                }
                if defines_reg(b, 0) && !b.contains("MapLookupElem") {
                    break;
                }
            }
            out.push(line.clone());
            continue;
        }

        if let Some((reg, addr)) = parse_map_addr_set(body) {
            addrs.insert(reg, addr);
            out.push(line.clone());
            continue;
        }

        if let Some(c) = MAPLOOKUP_ANN.captures(body) {
            // remember for later check
            let _ = c;
            out.push(line.clone());
            continue;
        }

        if let Some(c) = MEM_LOAD.captures(core_stmt(body)) {
            let base: u8 = c["base"].parse().unwrap_or(255);
            let off = parse_imm(&c["off"]).unwrap_or(-1);
            if off >= 0 {
                if let Some(addr) = addrs.get(base) {
                    let final_off = addr.offset + off as u64;
                    let ty = format!("u{}", &c["bits"]);
                    let dst = &c["dst"];
                    out.push(join_line(
                        index,
                        &format!(
                            "{dst} = map{{ {}, [{}] }} + {} read {ty}",
                            addr.map_index,
                            addr.key,
                            fmt_hex_u64(final_off)
                        ),
                    ));
                    if let Some(r) = reg_num(dst) {
                        addrs.remove(r);
                    }
                    continue;
                }
            }
        }

        if let Some(c) = MEM_STORE.captures(core_stmt(body)) {
            let base: u8 = c["base"].parse().unwrap_or(255);
            let off = parse_imm(&c["off"]).unwrap_or(-1);
            if off >= 0 {
                if let Some(addr) = addrs.get(base) {
                    let final_off = addr.offset + off as u64;
                    let ty = format!("u{}", &c["bits"]);
                    let val = c["val"].trim();
                    out.push(join_line(
                        index,
                        &format!(
                            "map{{ {}, [{}] }} + {} write {ty} = {val}",
                            addr.map_index,
                            addr.key,
                            fmt_hex_u64(final_off)
                        ),
                    ));
                    continue;
                }
            }
        }

        for r in 0u8..=10 {
            if defines_reg(body, r) {
                addrs.remove(r);
            }
        }
        out.push(line.clone());
    }
    out
}

fn stack_interval_key(n_abs: u64) -> Vec<String> {
    let k = n_abs / 4;
    (1..=k).rev().map(|i| format!("ws{i}")).collect()
}

fn stack_range_slots(start_from_fp: u64, end_from_fp: u64) -> Vec<String> {
    // [r10-start, r10-end) in byte offsets from r10; end < start.
    // slots: for offset o in (end, start], slot = o/4, ordered low address to high:
    // ws(start/4) ... ws(end/4 + 1)
    let mut slots = Vec::new();
    let mut o = start_from_fp;
    while o > end_from_fp {
        slots.push(format!("ws{}", o / 4));
        o -= 4;
    }
    slots
}

fn t4_5(path: &[String]) -> Vec<String> {
    let mut out = path.to_vec();
    for i in 0..out.len() {
        let Some((index, body)) = split_line(&out[i]) else {
            continue;
        };
        if body.contains("mapupdate {") {
            continue;
        }
        if !UPDATE.is_match(body) {
            continue;
        }
        let Some(map_index) = latest_imm(&out, i, 1) else {
            continue;
        };
        let Some(flags) = latest_imm(&out, i, 4) else {
            continue;
        };
        let Some((k_off, _)) = latest_stack_ptr(&out, i, 2) else {
            continue;
        };
        let Some((v_off, _)) = latest_stack_ptr(&out, i, 3) else {
            continue;
        };
        if k_off == v_off {
            continue;
        }
        // key at [r10-K, …), value at [r10-V, …)
        // closer to r10 extends to r10; farther extends to the other start
        let (key, value) = if k_off < v_off {
            // key closer: key [r10-K, r10), value [r10-V, r10-K)
            (
                stack_range_slots(k_off, 0),
                stack_range_slots(v_off, k_off),
            )
        } else {
            // value closer: value [r10-V, r10), key [r10-K, r10-V)
            (
                stack_range_slots(k_off, v_off),
                stack_range_slots(v_off, 0),
            )
        };
        let _ = stack_interval_key;
        let ann = format!(
            "{body}, mapupdate {{ {map_index}, [{}], [{}], {flags} }}",
            key.join(", "),
            value.join(", ")
        );
        out[i] = join_line(index, &ann);
    }
    out
}

fn t4_6(path: &[String]) -> Vec<String> {
    let mut out = path.to_vec();
    for i in 0..out.len() {
        let Some((index, body)) = split_line(&out[i]) else {
            continue;
        };
        if body.contains("mapdelete {") {
            continue;
        }
        if !DELETE.is_match(body) {
            continue;
        }
        let Some(map_index) = latest_imm(&out, i, 1) else {
            continue;
        };
        let Some((_, key)) = latest_stack_ptr(&out, i, 2) else {
            continue;
        };
        let ann = format!(
            "{body}, mapdelete {{ {map_index}, [{}] }}",
            key.join(", ")
        );
        out[i] = join_line(index, &ann);
    }
    out
}

/// T4 = t4_6 ∘ t4_5 ∘ t4_4 ∘ t4_3 ∘ t4_2 ∘ t4_1.
pub fn t4(path: &[String]) -> Vec<String> {
    t4_6(&t4_5(&t4_4(&t4_3(&t4_2(&t4_1(path))))))
}
