//! T3: packet pointer propagation, bounds checks, PacketRead/Write.

use regex::Regex;
use std::collections::HashMap;
use std::sync::LazyLock;

use super::text::{fmt_hex_u64, join_line, parse_imm, reg_num, split_line};

fn fmt_data_off(n: u64) -> String {
    if n == 0 {
        "0".to_string()
    } else {
        fmt_hex_u64(n)
    }
}

static COPY: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^(?P<dst>[rw]\d+)\s+=\s+(?P<src>[rw]\d+)$").unwrap());
static LOAD_U32: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^(?P<dst>[rw]\d+)\s+=\s+\*\(u32\s\*\)\((?P<base>[rw]\d+)\s+\+\s+(?P<off>0x[0-9a-fA-F]+|\d+)\)$",
    )
    .unwrap()
});
static ADD_IMM: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^(?P<dst>[rw]\d+)\s+\+=\s+(?P<imm>0x[0-9a-fA-F]+|\d+)$").unwrap()
});
static SUB_IMM: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^(?P<dst>[rw]\d+)\s+-=\s+(?P<imm>0x[0-9a-fA-F]+|\d+)$").unwrap()
});
static SET_XDP: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^(?P<dst>[rw]\d+)\s+set\s+xdp_md$").unwrap());
static SET_DATA: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^(?P<dst>[rw]\d+)\s+set\s+data\s+\+\s+(?P<off>0x[0-9a-fA-F]+|\d+)$").unwrap()
});
static SET_END: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^(?P<dst>[rw]\d+)\s+set\s+data_end$").unwrap());
static ASSERT: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^assert\s+\((?P<a>[rw]\d+)\s+(?P<op>>|<|>=|<=)\s+(?P<b>[rw]\d+)\)\s+==\s+(?P<br>true|false)(?P<rest>.*)$",
    )
    .unwrap()
});
static CHECK: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"data_end check \{\s*(?P<r>[rw]\d+)\s*:\s*data\s+\+\s+(?P<off>0x[0-9a-fA-F]+|\d+)\s*\}",
    )
    .unwrap()
});
static MEM_LOAD: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^(?P<dst>[rw]\d+)\s+=\s+\*\(u(?P<bits>8|16|32|64)\s\*\)\((?P<base>[rw]\d+)\s+\+\s+(?P<off>0x[0-9a-fA-F]+|\d+)\)$",
    )
    .unwrap()
});
static MEM_STORE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)^\*\(u(?P<bits>8|16|32|64)\s\*\)\((?P<base>[rw]\d+)\s+\+\s+(?P<off>0x[0-9a-fA-F]+|\d+)\)\s+=\s+(?P<val>.+)$",
    )
    .unwrap()
});

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tag {
    XdpMd,
    Data(u64),
    DataEnd,
}

type Tags = HashMap<u8, Tag>;

fn clear_packet(tags: &mut Tags) {
    tags.retain(|_, t| matches!(t, Tag::XdpMd));
}

fn ingest_normalized(body: &str, tags: &mut Tags) {
    if let Some(c) = SET_XDP.captures(body) {
        if let Some(r) = reg_num(&c["dst"]) {
            tags.insert(r, Tag::XdpMd);
        }
    } else if let Some(c) = SET_DATA.captures(body) {
        if let Some(r) = reg_num(&c["dst"]) {
            if let Some(off) = parse_imm(&c["off"]).filter(|v| *v >= 0) {
                tags.insert(r, Tag::Data(off as u64));
            }
        }
    } else if let Some(c) = SET_END.captures(body) {
        if let Some(r) = reg_num(&c["dst"]) {
            tags.insert(r, Tag::DataEnd);
        }
    }
    if body.contains("adjust") {
        clear_packet(tags);
    }
}

fn clear_dst_writes(body: &str, tags: &mut Tags) {
    for r in 0u8..=10 {
        let pats = [
            format!("r{r} = "),
            format!("w{r} = "),
            format!("r{r} += "),
            format!("r{r} -= "),
            format!("w{r} += "),
            format!("w{r} -= "),
            format!("r{r} set "),
            format!("w{r} set "),
        ];
        if pats.iter().any(|p| body.starts_with(p)) {
            tags.remove(&r);
        }
    }
}

fn rewrite_t3_1_line(index: u32, body: &str, tags: &mut Tags) -> String {
    if SET_XDP.is_match(body) || SET_DATA.is_match(body) || SET_END.is_match(body) {
        ingest_normalized(body, tags);
        return join_line(index, body);
    }
    if body.contains(", adjust") || body.ends_with("adjust") {
        clear_packet(tags);
        return join_line(index, body);
    }

    if let Some(c) = COPY.captures(body) {
        let d = reg_num(&c["dst"]);
        let s = reg_num(&c["src"]);
        if let (Some(d), Some(s)) = (d, s) {
            if let Some(tag) = tags.get(&s).cloned() {
                let text = match &tag {
                    Tag::XdpMd => format!("r{d} set xdp_md"),
                    Tag::Data(n) => format!("r{d} set data + {}", fmt_data_off(*n)),
                    Tag::DataEnd => format!("r{d} set data_end"),
                };
                tags.insert(d, tag);
                return join_line(index, &text);
            }
            tags.remove(&d);
        }
        return join_line(index, body);
    }

    if let Some(c) = LOAD_U32.captures(body) {
        let d = reg_num(&c["dst"]);
        let b = reg_num(&c["base"]);
        let off = parse_imm(&c["off"]).unwrap_or(-1);
        if let (Some(d), Some(b)) = (d, b) {
            if tags.get(&b) == Some(&Tag::XdpMd) {
                if off == 0 {
                    tags.insert(d, Tag::Data(0));
                    return join_line(index, &format!("w{d} set data + 0"));
                }
                if off == 4 {
                    tags.insert(d, Tag::DataEnd);
                    return join_line(index, &format!("w{d} set data_end"));
                }
            }
            tags.remove(&d);
        }
        return join_line(index, body);
    }

    if let Some(c) = ADD_IMM.captures(body) {
        let d = reg_num(&c["dst"]);
        let imm = parse_imm(&c["imm"]).unwrap_or(-1);
        if let Some(d) = d {
            match tags.get(&d).cloned() {
                Some(Tag::Data(n)) if imm >= 0 => {
                    let nn = n.saturating_add(imm as u64);
                    tags.insert(d, Tag::Data(nn));
                    return join_line(index, &format!("r{d} set data + {}", fmt_data_off(nn)));
                }
                Some(Tag::Data(_)) => {
                    tags.remove(&d);
                    return join_line(index, &format!("{body}, unset data"));
                }
                Some(Tag::DataEnd) => {
                    tags.remove(&d);
                    return join_line(index, &format!("{body}, unset data_end"));
                }
                Some(Tag::XdpMd) => {
                    tags.remove(&d);
                    return join_line(index, body);
                }
                None => {}
            }
        }
        return join_line(index, body);
    }

    if let Some(c) = SUB_IMM.captures(body) {
        let d = reg_num(&c["dst"]);
        let imm = parse_imm(&c["imm"]).unwrap_or(-1);
        if let Some(d) = d {
            match tags.get(&d).cloned() {
                Some(Tag::Data(n)) if imm >= 0 && (n as i64) >= imm => {
                    let nn = n - imm as u64;
                    tags.insert(d, Tag::Data(nn));
                    return join_line(index, &format!("r{d} set data + {}", fmt_data_off(nn)));
                }
                Some(Tag::Data(_)) => {
                    tags.remove(&d);
                    return join_line(index, &format!("{body}, unset data"));
                }
                Some(Tag::DataEnd) => {
                    tags.remove(&d);
                    return join_line(index, &format!("{body}, unset data_end"));
                }
                Some(Tag::XdpMd) => {
                    tags.remove(&d);
                    return join_line(index, body);
                }
                None => {}
            }
        }
        return join_line(index, body);
    }

    clear_dst_writes(body, tags);
    join_line(index, body)
}

fn t3_1(path: &[String]) -> Vec<String> {
    let mut cur = path.to_vec();
    loop {
        let mut tags: Tags = HashMap::new();
        tags.insert(1, Tag::XdpMd);
        let next: Vec<String> = cur
            .iter()
            .map(|line| match split_line(line) {
                Some((index, body)) => rewrite_t3_1_line(index, body, &mut tags),
                None => line.clone(),
            })
            .collect();
        if next == cur {
            return next;
        }
        cur = next;
    }
}

fn t3_2(path: &[String]) -> Vec<String> {
    let mut tags: Tags = HashMap::new();
    tags.insert(1, Tag::XdpMd);
    let mut out = Vec::with_capacity(path.len());

    for line in path {
        let Some((index, body)) = split_line(line) else {
            out.push(line.clone());
            continue;
        };

        ingest_normalized(body, &mut tags);

        if let Some(c) = ASSERT.captures(body) {
            if body.contains("data_end check") {
                out.push(line.clone());
                continue;
            }
            let a = reg_num(&c["a"]);
            let b = reg_num(&c["b"]);
            let op = &c["op"];
            let br = &c["br"];
            if let (Some(a), Some(b)) = (a, b) {
                let a_tag = tags.get(&a).cloned();
                let b_tag = tags.get(&b).cloned();
                // Pattern: (data_reg > end_reg) == false
                if let (Some(Tag::Data(n)), Some(Tag::DataEnd)) = (&a_tag, &b_tag) {
                    if matches!((op, br), (">", "false") | (">=", "false")) {
                        let annotated = format!(
                            "{body}, data_end check {{ r{a}: data + {} }}",
                            fmt_data_off(*n)
                        );
                        out.push(join_line(index, &annotated));
                        continue;
                    }
                }
                // Pattern: (end_reg > data_reg) == true  ⇒ same safety
                if let (Some(Tag::DataEnd), Some(Tag::Data(n))) = (&a_tag, &b_tag) {
                    if matches!((op, br), (">", "true") | (">=", "true")) {
                        let annotated = format!(
                            "{body}, data_end check {{ r{b}: data + {} }}",
                            fmt_data_off(*n)
                        );
                        out.push(join_line(index, &annotated));
                        continue;
                    }
                }
            }
            out.push(line.clone());
            continue;
        }

        clear_dst_writes(body, &mut tags);
        // Re-ingest if this line itself is a set (already handled) or copy rewritten
        ingest_normalized(body, &mut tags);
        out.push(line.clone());
    }
    out
}

fn bits_to_size(bits: &str) -> u64 {
    match bits {
        "8" => 1,
        "16" => 2,
        "32" => 4,
        "64" => 8,
        _ => 0,
    }
}

fn t3_3(path: &[String]) -> Vec<String> {
    let mut tags: Tags = HashMap::new();
    tags.insert(1, Tag::XdpMd);
    let mut checked: Option<u64> = None;
    let mut out = Vec::with_capacity(path.len());

    for line in path {
        let Some((index, body)) = split_line(line) else {
            out.push(line.clone());
            continue;
        };

        if body.contains("adjust") {
            checked = None;
            clear_packet(&mut tags);
            out.push(line.clone());
            continue;
        }

        ingest_normalized(body, &mut tags);

        if let Some(c) = CHECK.captures(body) {
            if let Some(off) = parse_imm(&c["off"]).filter(|v| *v >= 0) {
                let off = off as u64;
                checked = Some(checked.map_or(off, |c| c.max(off)));
            }
            out.push(line.clone());
            continue;
        }

        if let Some(c) = MEM_LOAD.captures(body) {
            let base = reg_num(&c["base"]);
            let off = parse_imm(&c["off"]).unwrap_or(-1);
            let size = bits_to_size(&c["bits"]);
            let dst = &c["dst"];
            if let (Some(b), true) = (base, off >= 0) {
                if let Some(Tag::Data(base_off)) = tags.get(&b) {
                    if let Some(ch) = checked {
                        let start = base_off + off as u64;
                        if start + size <= ch {
                            out.push(join_line(
                                index,
                                &format!("{dst} = PacketRead({}, {size})", fmt_hex_u64(start)),
                            ));
                            // load still defines dst — not a packet pointer
                            if let Some(r) = reg_num(dst) {
                                tags.remove(&r);
                            }
                            continue;
                        }
                    }
                }
            }
            clear_dst_writes(body, &mut tags);
            out.push(line.clone());
            continue;
        }

        if let Some(c) = MEM_STORE.captures(body) {
            let base = reg_num(&c["base"]);
            let off = parse_imm(&c["off"]).unwrap_or(-1);
            let size = bits_to_size(&c["bits"]);
            let val = c["val"].trim();
            if let (Some(b), true) = (base, off >= 0) {
                if let Some(Tag::Data(base_off)) = tags.get(&b) {
                    if let Some(ch) = checked {
                        let start = base_off + off as u64;
                        if start + size <= ch {
                            out.push(join_line(
                                index,
                                &format!(
                                    "PacketWrite({}, {size}, {val})",
                                    fmt_hex_u64(start)
                                ),
                            ));
                            continue;
                        }
                    }
                }
            }
            out.push(line.clone());
            continue;
        }

        clear_dst_writes(body, &mut tags);
        ingest_normalized(body, &mut tags);
        out.push(line.clone());
    }
    out
}

/// T3 = t3_3 ∘ t3_2 ∘ t3_1.
pub fn t3(path: &[String]) -> Vec<String> {
    t3_3(&t3_2(&t3_1(path)))
}
