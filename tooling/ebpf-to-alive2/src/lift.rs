use crate::decode::{AluOp, Cond, Insn, MemSize, Src, Width};
use crate::program::Func;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Uninit,
    I64,
    Ctx,
    Pkt,
    Stack,
    Map,
    MapVal,
}

#[derive(Clone, Debug)]
enum Rv {
    None,
    I64(String),
    Packet(String),
    Ptr(Kind, String),
}

struct Emit {
    n: u32,
    lines: Vec<String>,
    origin: BTreeMap<u32, Vec<String>>,
}

pub struct Compiled {
    pub alive: String,
    pub origin_insns: Vec<(u32, Vec<String>)>,
    pub maps: Vec<String>,
    pub loop_header: bool,
}

pub fn lift(func: &Func) -> Result<Compiled, String> {
    if func.insns.is_empty() {
        return Err("program has no instructions".into());
    }
    let blocks = cfg(&func.insns)?;
    let relocated: std::collections::BTreeSet<u32> =
        func.relocs.iter().map(|reloc| reloc.slot).collect();
    let kinds = kinds(&func.insns, &blocks, &relocated)?;
    let mut emit = Emit {
        n: 0,
        lines: Vec::new(),
        origin: BTreeMap::new(),
    };
    let maps = map_names(func);
    let map_at: BTreeMap<u32, String> = func
        .relocs
        .iter()
        .map(|reloc| {
            let name = format!(
                "map_{}",
                reloc
                    .symbol
                    .replace(|ch: char| !ch.is_ascii_alphanumeric(), "_")
            );
            (reloc.slot, name)
        })
        .collect();
    let mut header = String::new();
    header.push_str("; alive-file v1\n");
    header.push_str("; alive2-pin adacbd5180ccf95075e9867c4f0c259f59c9fef2\n");
    header.push_str("; rocq-pin 78d65a77592aae84b31f86385f8be4ab83b45ccb\n");
    header.push_str(&format!(
        "define i64 @{}(ptr %ctx, ptr %pkt, i64 %pkt_base",
        func.name
    ));
    for map in &maps {
        header.push_str(&format!(", ptr %{map}"));
    }
    header.push_str(") memory(argmem: readwrite, inaccessiblemem: readwrite) {\n");
    if !maps.is_empty() {
        header.push_str("declare ptr @bpf_map_lookup_elem(ptr, ptr) memory(argmem: read, inaccessiblemem: readwrite)\n\n");
    }
    emit.lines.push(header);
    emit.lines.push("entry:\n  %stack = alloca i64 512, align 8\n  %fp = gep ptr %stack, 1 x i64 512\n  br label %s0\n".into());

    let mut outs: Vec<[Rv; 11]> = Vec::new();
    let mut phi_names: Vec<Option<[String; 11]>> = Vec::new();
    for (bi, block) in blocks.iter().enumerate() {
        if block.preds.len() > 1 || block.preds.iter().any(|pred| pred.is_some_and(|p| p >= bi)) {
            let mut names = std::array::from_fn(|_| String::new());
            for (reg, name) in names.iter_mut().enumerate() {
                *name = format!("%s{}_r{reg}", block.start);
            }
            phi_names.push(Some(names));
        } else {
            phi_names.push(None);
        }
    }

    let mut bodies = Vec::new();
    let mut exit_labels = Vec::new();
    for (bi, block) in blocks.iter().enumerate() {
        let mut regs = if let Some(names) = &phi_names[bi] {
            std::array::from_fn(|reg| rv_of(kinds[bi].kind[reg], names[reg].clone()))
        } else if bi == 0 {
            entry_regs()
        } else {
            let pred = block.preds[0].ok_or("internal block has no predecessor")?;
            outs[pred].clone()
        };
        let mark = emit.lines.len();
        emit_block(
            &mut emit,
            &func.insns[block.insns.clone()],
            &map_at,
            &mut regs,
            kinds[bi].clone(),
            &relocated,
        )?;
        let before_term = emit.lines.len();
        emit_term(&mut emit, &blocks, bi, &func.insns, &regs)?;
        let last = &func.insns[block.insns.end - 1];
        emit.origin
            .entry(last.index())
            .or_default()
            .extend(defined_names(&emit.lines[before_term..]));
        let exit_label = emit.lines[mark..]
            .iter()
            .rev()
            .find_map(|line| line.strip_suffix(':'))
            .map(str::to_owned)
            .unwrap_or_else(|| format!("s{}", block.start));
        exit_labels.push(exit_label);
        bodies.push(emit.lines.split_off(mark));
        outs.push(regs);
    }
    for (bi, block) in blocks.iter().enumerate() {
        emit.lines.push(format!("s{}:", block.start));
        if let Some(names) = &phi_names[bi] {
            for reg in 0..11 {
                if kinds[bi].kind[reg] == Kind::Uninit {
                    continue;
                }
                let ty = if matches!(kinds[bi].kind[reg], Kind::I64 | Kind::Pkt) {
                    "i64"
                } else {
                    "ptr"
                };
                let mut pairs = Vec::new();
                for pred in &block.preds {
                    let (label, value) = match pred {
                        None => ("entry".into(), entry_regs()[reg].clone()),
                        Some(pi) => (exit_labels[*pi].clone(), outs[*pi][reg].clone()),
                    };
                    let shown = coerce_name(&value, kinds[bi].kind[reg])?;
                    pairs.push(format!("[ {shown}, %{label} ]"));
                }
                emit.lines
                    .push(format!("  {} = phi {ty} {}", names[reg], pairs.join(", ")));
            }
        }
        emit.lines.extend(bodies[bi].clone());
        emit.lines.push(String::new());
    }
    emit.lines.push("}\n".into());
    let alive = emit.lines.join("\n");
    let origin_insns = emit.origin.into_iter().collect();
    Ok(Compiled {
        alive,
        origin_insns,
        maps,
        loop_header: blocks.iter().any(|block| {
            block
                .preds
                .iter()
                .any(|pred| pred.is_some_and(|p| blocks[p].start >= block.start))
        }),
    })
}

fn entry_regs() -> [Rv; 11] {
    let mut regs = std::array::from_fn(|_| Rv::None);
    regs[1] = Rv::Ptr(Kind::Ctx, "%ctx".into());
    regs[10] = Rv::Ptr(Kind::Stack, "%fp".into());
    regs
}

fn rv_of(kind: Kind, name: String) -> Rv {
    match kind {
        Kind::I64 => Rv::I64(name),
        Kind::Pkt => Rv::Packet(name),
        Kind::Uninit => Rv::None,
        _ => Rv::Ptr(kind, name),
    }
}

fn coerce_name(value: &Rv, kind: Kind) -> Result<String, String> {
    match (value, kind) {
        (Rv::I64(name), Kind::I64) | (Rv::Packet(name), Kind::Pkt) => Ok(name.clone()),
        (Rv::Ptr(have, name), want) if *have == want => Ok(name.clone()),
        (Rv::None, Kind::Uninit) => Ok("undef".into()),
        _ => Err("phi predecessor type does not match the block input".into()),
    }
}

struct Block {
    start: u32,
    insns: std::ops::Range<usize>,
    preds: Vec<Option<usize>>,
    succ: Vec<Option<u32>>,
}

fn cfg(insns: &[Insn]) -> Result<Vec<Block>, String> {
    let mut slot_of = BTreeMap::new();
    for (index, insn) in insns.iter().enumerate() {
        slot_of.insert(insn.index(), index);
    }
    let mut leaders = BTreeSet::new();
    leaders.insert(0usize);
    for (index, insn) in insns.iter().enumerate() {
        if let Some(target) = crate::decode::target_slot(insn) {
            let Some(&at) = slot_of.get(&(target as u32)) else {
                return Err(format!(
                    "slot {}: jump target {target} is not an instruction",
                    insn.index()
                ));
            };
            leaders.insert(at);
            if index + 1 < insns.len() {
                leaders.insert(index + 1);
            }
        } else if matches!(
            insn,
            Insn::Jmp {
                cond: Cond::Exit,
                ..
            }
        ) && index + 1 < insns.len()
        {
            leaders.insert(index + 1);
        }
    }
    let leader_list: Vec<usize> = leaders.into_iter().collect();
    let mut blocks = Vec::new();
    for (n, &start) in leader_list.iter().enumerate() {
        let end = leader_list.get(n + 1).copied().unwrap_or(insns.len());
        blocks.push(Block {
            start: insns[start].index(),
            insns: start..end,
            preds: Vec::new(),
            succ: Vec::new(),
        });
    }
    let starts: Vec<u32> = blocks.iter().map(|block| block.start).collect();
    let block_at = |slot: u32| starts.iter().position(|start| *start == slot);
    for block in &mut blocks {
        let end = block.insns.end;
        let last = &insns[end - 1];
        let mut succ = Vec::new();
        if let Insn::Jmp { cond, .. } = last {
            if *cond != Cond::Exit {
                let target = crate::decode::target_slot(last).unwrap() as u32;
                if block_at(target).is_none() {
                    return Err(format!(
                        "slot {}: target {target} is not a block leader",
                        last.index()
                    ));
                }
                succ.push(Some(target));
                if *cond != Cond::Ja {
                    succ.push(insns.get(end).map(Insn::index));
                }
            }
        } else if end < insns.len() {
            succ.push(Some(insns[end].index()));
        } else {
            return Err("program does not end in a jump".into());
        }
        block.succ = succ;
    }
    for bi in 0..blocks.len() {
        let slots: Vec<u32> = blocks[bi].succ.iter().flatten().copied().collect();
        for slot in slots {
            let tb = block_at(slot).unwrap();
            if !blocks[tb].preds.contains(&Some(bi)) {
                blocks[tb].preds.push(Some(bi));
            }
        }
    }
    if !blocks.is_empty() {
        blocks[0].preds.insert(0, None);
    }
    let mut reachable = BTreeSet::from([0usize]);
    let mut pending = vec![0usize];
    while let Some(bi) = pending.pop() {
        for slot in blocks[bi].succ.iter().flatten() {
            let next = starts.iter().position(|start| start == slot).unwrap();
            if reachable.insert(next) {
                pending.push(next);
            }
        }
    }
    if reachable.len() != blocks.len() {
        return Err("unsupported: unreachable instruction blocks".into());
    }
    Ok(blocks)
}

fn kinds(
    insns: &[Insn],
    blocks: &[Block],
    relocated: &BTreeSet<u32>,
) -> Result<Vec<Facts>, String> {
    let live = live_in(insns, blocks, relocated)?;
    let mut input = vec![entry_facts(); blocks.len()];
    let mut output = vec![entry_facts(); blocks.len()];
    let mut visited = vec![false; blocks.len()];
    let mut guard = 0;
    loop {
        guard += 1;
        if guard > blocks.len() * 12 + 4 {
            return Err("internal: kind fixpoint did not settle".into());
        }
        let mut changed = false;
        let mut failed: Option<String> = None;
        for (bi, block) in blocks.iter().enumerate() {
            if block.preds.len() != 1 || block.preds[0].is_some() {
                let mut merged: Option<Facts> = None;
                for pred in &block.preds {
                    let from = match pred {
                        None => entry_facts(),
                        Some(pi) if visited[*pi] => output[*pi].clone(),
                        Some(_) => continue,
                    };
                    merged = Some(match merged {
                        None => from,
                        Some(prev) => merge_facts(&prev, &from, &live[bi], block.start)?,
                    });
                }
                if let Some(merged) = merged {
                    if merged != input[bi] {
                        input[bi] = merged;
                        changed = true;
                    }
                }
            }
            let mut regs = input[bi].clone();
            let mut ok = true;
            for insn in &insns[block.insns.clone()] {
                if let Err(err) = apply(&mut regs, insn, relocated) {
                    failed = Some(err);
                    ok = false;
                    break;
                }
            }
            if ok {
                visited[bi] = true;
                if regs != output[bi] {
                    output[bi] = regs;
                    changed = true;
                }
            }
        }
        if !changed {
            if let Some(err) = failed {
                return Err(err);
            }
            break;
        }
    }
    for (bi, block) in blocks.iter().enumerate() {
        if block.preds.len() < 2 {
            continue;
        }
        for reg in 0..11 {
            if !live[bi][reg] {
                continue;
            }
            for pred in &block.preds {
                let from = match pred {
                    None => &entry_facts(),
                    Some(pi) if visited[*pi] => &output[*pi],
                    Some(_) => {
                        return Err(format!(
                            "internal: block s{} predecessor was not analyzed",
                            block.start
                        ));
                    }
                };
                if from.kind[reg] == Kind::Uninit || from.kind[reg] != input[bi].kind[reg] {
                    return Err(format!(
                        "unsupported: block s{} register r{reg} is not defined on every path",
                        block.start
                    ));
                }
            }
        }
    }
    Ok(input)
}
const UNKNOWN: i64 = i64::MIN;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Slot {
    Scalar,
    Ptr(Kind, i64),
    Mixed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Facts {
    kind: [Kind; 11],
    off: [i64; 11],
    slots: BTreeMap<i64, Slot>,
}

fn is_ptr(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::Ctx | Kind::Pkt | Kind::Stack | Kind::Map | Kind::MapVal
    )
}

fn add_off(off: i64, delta: i64) -> i64 {
    if off == UNKNOWN {
        UNKNOWN
    } else {
        off.checked_add(delta).unwrap_or(UNKNOWN)
    }
}

fn merge_off(left: i64, right: i64) -> i64 {
    if left == right {
        left
    } else {
        UNKNOWN
    }
}

fn entry_facts() -> Facts {
    let mut kind = [Kind::Uninit; 11];
    let off = [0; 11];
    kind[1] = Kind::Ctx;
    kind[10] = Kind::Stack;
    Facts {
        kind,
        off,
        slots: BTreeMap::new(),
    }
}

fn need_kind(facts: &Facts, reg: u8, slot: u32) -> Result<Kind, String> {
    let kind = facts.kind[reg as usize];
    if kind == Kind::Uninit {
        Err(format!(
            "unsupported: slot {slot}: r{reg} is read before it is written"
        ))
    } else {
        Ok(kind)
    }
}

fn merge_slot(left: Slot, right: Slot, block: u32, key: i64) -> Result<Slot, String> {
    match (left, right) {
        (Slot::Scalar, Slot::Scalar) => Ok(Slot::Scalar),
        (Slot::Ptr(a, x), Slot::Ptr(b, y)) if a == b => Ok(Slot::Ptr(a, merge_off(x, y))),
        (Slot::Ptr(a, _), Slot::Ptr(b, _)) => {
            Err(format!("unsupported: block s{block} stack slot {key} is {a:?} on one path and {b:?} on another"))
        }
        (Slot::Mixed, _) | (_, Slot::Mixed) | (Slot::Ptr(_, _), Slot::Scalar) | (Slot::Scalar, Slot::Ptr(_, _)) => Ok(Slot::Mixed),
    }
}

fn widen_absent(slot: Slot) -> Slot {
    match slot {
        Slot::Scalar => Slot::Scalar,
        Slot::Ptr(_, _) | Slot::Mixed => Slot::Mixed,
    }
}

fn merge_slots(
    left: &BTreeMap<i64, Slot>,
    right: &BTreeMap<i64, Slot>,
    block: u32,
) -> Result<BTreeMap<i64, Slot>, String> {
    let mut keys = BTreeSet::new();
    keys.extend(left.keys().copied());
    keys.extend(right.keys().copied());
    let mut out = BTreeMap::new();
    for key in keys {
        let slot = match (left.get(&key).copied(), right.get(&key).copied()) {
            (Some(a), Some(b)) => merge_slot(a, b, block, key)?,
            (Some(a), None) | (None, Some(a)) => widen_absent(a),
            (None, None) => continue,
        };
        if slot != Slot::Scalar {
            out.insert(key, slot);
        }
    }
    Ok(out)
}

fn stack_load(
    facts: &Facts,
    at: i64,
    size: MemSize,
    signed: bool,
    slot: u32,
) -> Result<(Kind, i64), String> {
    let end = at.saturating_add(i64::from(align(size)));
    for (&key, value) in &facts.slots {
        if at == UNKNOWN || (at < key.saturating_add(8) && key < end) {
            return match value {
                Slot::Ptr(kind, off) if at == key && size == MemSize::Dword && !signed => Ok((*kind, *off)),
                _ => Err(format!("unsupported: slot {slot}: stack load overlaps a partial or incompatible pointer spill")),
            };
        }
    }
    Ok((Kind::I64, 0))
}

fn apply(facts: &mut Facts, insn: &Insn, relocated: &BTreeSet<u32>) -> Result<(), String> {
    let slot = insn.index();
    match insn {
        Insn::Alu {
            width,
            op,
            dst,
            src,
            ..
        } => {
            let dst_i = *dst as usize;
            if *op == AluOp::Mov && *width == Width::W64 {
                if let Src::Reg(reg) = src {
                    let kind = need_kind(facts, *reg, slot)?;
                    facts.off[dst_i] = facts.off[*reg as usize];
                    facts.kind[dst_i] = kind;
                    return Ok(());
                }
            }
            if matches!(*op, AluOp::Mov | AluOp::Movsx) && matches!(src, Src::Imm(_)) {
                facts.kind[dst_i] = Kind::I64;
                facts.off[dst_i] = 0;
                return Ok(());
            }
            let pointer_dst = is_ptr(facts.kind[dst_i]);
            if *width == Width::W64 && matches!(*op, AluOp::Add | AluOp::Sub) && pointer_dst {
                need_kind(facts, *dst, slot)?;
                match src {
                    Src::Imm(imm) => {
                        let delta = if *op == AluOp::Add {
                            *imm as i64
                        } else {
                            -(*imm as i64)
                        };
                        facts.off[dst_i] = add_off(facts.off[dst_i], delta);
                    }
                    Src::Reg(reg) => {
                        let src_kind = need_kind(facts, *reg, slot)?;
                        if is_ptr(src_kind) {
                            if *op == AluOp::Sub && src_kind == facts.kind[dst_i] {
                                facts.kind[dst_i] = Kind::I64;
                                facts.off[dst_i] = 0;
                                return Ok(());
                            }
                            return Err(format!("unsupported: slot {slot}: r{dst} and r{reg} have incompatible pointer arithmetic"));
                        }
                        facts.off[dst_i] = UNKNOWN;
                    }
                }
                return Ok(());
            }
            if let Src::Reg(reg) = src {
                let src_kind = need_kind(facts, *reg, slot)?;
                if *width == Width::W64 && *op == AluOp::Sub && is_ptr(src_kind) {
                    return Err(format!(
                        "unsupported: slot {slot}: r{reg} is a pointer subtracted from r{dst}"
                    ));
                }
            }
            if !matches!(*op, AluOp::Mov | AluOp::Movsx) {
                need_kind(facts, *dst, slot)?;
            }
            facts.kind[dst_i] = Kind::I64;
            facts.off[dst_i] = 0;
        }
        Insn::End { dst, .. } => {
            need_kind(facts, *dst, slot)?;
            facts.kind[*dst as usize] = Kind::I64;
            facts.off[*dst as usize] = 0;
        }
        Insn::Jmp {
            cond: Cond::Exit, ..
        } => {
            need_kind(facts, 0, slot)?;
        }
        Insn::Jmp { cond: Cond::Ja, .. } => {}
        Insn::Jmp { dst, src, .. } => {
            need_kind(facts, *dst, slot)?;
            if let Src::Reg(reg) = src {
                need_kind(facts, *reg, slot)?;
            }
        }
        Insn::Load {
            dst,
            base,
            off,
            size,
            signed,
            ..
        } => {
            let base_kind = need_kind(facts, *base, slot)?;
            if !is_ptr(base_kind) || base_kind == Kind::Map {
                return Err(format!(
                    "unsupported: slot {slot}: r{base} is not a dereferenceable pointer"
                ));
            }
            let at = add_off(facts.off[*base as usize], *off as i64);
            let (result, off) = match base_kind {
                Kind::Ctx if !*signed && *size == MemSize::Word && (at == 0 || at == 4) => {
                    (Kind::Pkt, UNKNOWN)
                }
                Kind::Stack => stack_load(facts, at, *size, *signed, slot)?,
                _ => (Kind::I64, 0),
            };
            facts.kind[*dst as usize] = result;
            facts.off[*dst as usize] = off;
        }
        Insn::Store {
            base,
            off,
            src,
            size,
            ..
        } => {
            let base_kind = need_kind(facts, *base, slot)?;
            if !is_ptr(base_kind) || base_kind == Kind::Map {
                return Err(format!(
                    "unsupported: slot {slot}: r{base} is not a dereferenceable pointer"
                ));
            }
            let stored = match src {
                Src::Imm(_) => Slot::Scalar,
                Src::Reg(reg) => {
                    let kind = need_kind(facts, *reg, slot)?;
                    if is_ptr(kind) {
                        if *size != MemSize::Dword || base_kind != Kind::Stack {
                            return Err(format!("unsupported: slot {slot}: pointer spill requires a full stack slot"));
                        }
                        Slot::Ptr(kind, facts.off[*reg as usize])
                    } else {
                        Slot::Scalar
                    }
                }
            };
            if base_kind == Kind::Stack {
                let at = add_off(facts.off[*base as usize], *off as i64);
                if at == UNKNOWN {
                    let pointer_slot = facts
                        .slots
                        .values()
                        .any(|item| !matches!(item, Slot::Scalar));
                    if matches!(stored, Slot::Ptr(_, _)) || pointer_slot {
                        return Err(format!(
                            "unsupported: slot {slot}: stack store through an unknown offset"
                        ));
                    }
                } else {
                    let end = at.saturating_add(i64::from(align(*size)));
                    for (&key, value) in &mut facts.slots {
                        if at < key.saturating_add(8) && key < end {
                            *value = Slot::Mixed;
                        }
                    }
                    if *size == MemSize::Dword {
                        facts.slots.remove(&at);
                    }
                    if !matches!(stored, Slot::Scalar) {
                        facts.slots.insert(at, stored);
                    }
                }
            }
        }
        Insn::Lddw {
            dst, pseudo, index, ..
        } => {
            if relocated.contains(index) {
                facts.kind[*dst as usize] = Kind::Map;
                facts.off[*dst as usize] = 0;
            } else if *pseudo == 0 {
                facts.kind[*dst as usize] = Kind::I64;
                facts.off[*dst as usize] = 0;
            } else {
                return Err(format!(
                    "unsupported: slot {index}: LDDW pseudo {pseudo} is not a map relocation"
                ));
            }
        }
        Insn::Call { id, index } => {
            if *id != 1 {
                return Err(format!(
                    "unsupported: slot {index}: helper {id} has no call contract"
                ));
            }
            let map = need_kind(facts, 1, *index)?;
            if map != Kind::Map {
                return Err(format!(
                    "unsupported: slot {index}: helper 1 expects a map pointer in r1"
                ));
            }
            let key = need_kind(facts, 2, *index)?;
            if !is_ptr(key) {
                return Err(format!(
                    "unsupported: slot {index}: helper 1 key in r2 is not a pointer"
                ));
            }
            facts.kind[0] = Kind::MapVal;
            facts.off[0] = UNKNOWN;
            for reg in 1..=5 {
                facts.kind[reg] = Kind::Uninit;
                facts.off[reg] = 0;
            }
        }
    }
    Ok(())
}

fn merge_facts(
    left: &Facts,
    right: &Facts,
    live: &[bool; 11],
    block: u32,
) -> Result<Facts, String> {
    let mut next = left.clone();
    for reg in 0..11 {
        if !live[reg] {
            next.kind[reg] = Kind::Uninit;
            next.off[reg] = 0;
            continue;
        }
        let (kind, off) = if left.kind[reg] == Kind::Uninit {
            (right.kind[reg], right.off[reg])
        } else if right.kind[reg] == Kind::Uninit || left.kind[reg] == right.kind[reg] {
            let off = if right.kind[reg] == Kind::Uninit {
                left.off[reg]
            } else if left.kind[reg] == Kind::Uninit {
                right.off[reg]
            } else {
                merge_off(left.off[reg], right.off[reg])
            };
            (
                if left.kind[reg] == Kind::Uninit {
                    right.kind[reg]
                } else {
                    left.kind[reg]
                },
                off,
            )
        } else {
            return Err(format!(
                "unsupported: block s{block} register r{reg} is a pointer on one path and a different value on another"
            ));
        };
        next.kind[reg] = kind;
        next.off[reg] = off;
    }
    next.slots = merge_slots(&left.slots, &right.slots, block)?;
    Ok(next)
}

fn live_in(
    insns: &[Insn],
    blocks: &[Block],
    _relocated: &std::collections::BTreeSet<u32>,
) -> Result<Vec<[bool; 11]>, String> {
    let mut gen = vec![[false; 11]; blocks.len()];
    let mut kill = vec![[false; 11]; blocks.len()];
    for (bi, block) in blocks.iter().enumerate() {
        record_uses(&insns[block.insns.clone()], &mut gen[bi], &mut kill[bi]);
    }
    let mut live = vec![[false; 11]; blocks.len()];
    let mut guard = 0;
    loop {
        guard += 1;
        if guard > blocks.len() * 12 + 4 {
            return Err("liveness did not settle".into());
        }
        let mut changed = false;
        for bi in (0..blocks.len()).rev() {
            let mut out = [false; 11];
            for succ in &blocks[bi].succ {
                let Some(slot) = succ else { continue };
                let Some(si) = blocks.iter().position(|block| block.start == *slot) else {
                    continue;
                };
                for reg in 0..11 {
                    out[reg] |= live[si][reg];
                }
            }
            let mut inn = gen[bi];
            for reg in 0..11 {
                if out[reg] && !kill[bi][reg] {
                    inn[reg] = true;
                }
            }
            if inn != live[bi] {
                live[bi] = inn;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    Ok(live)
}

fn record_uses(insns: &[Insn], gen: &mut [bool; 11], kill: &mut [bool; 11]) {
    let mut defined = [false; 11];
    for insn in insns {
        let mut uses = Vec::new();
        let mut defs = Vec::new();
        match insn {
            Insn::Alu { op, dst, src, .. } => {
                if !matches!(op, AluOp::Mov | AluOp::Movsx) {
                    uses.push(*dst);
                }
                if let Src::Reg(reg) = src {
                    uses.push(*reg);
                }
                defs.push(*dst);
            }
            Insn::End { dst, .. } => {
                uses.push(*dst);
                defs.push(*dst);
            }
            Insn::Jmp {
                cond: Cond::Exit, ..
            } => uses.push(0),
            Insn::Jmp { cond: Cond::Ja, .. } => {}
            Insn::Jmp { dst, src, .. } => {
                uses.push(*dst);
                if let Src::Reg(reg) = src {
                    uses.push(*reg);
                }
            }
            Insn::Load { dst, base, .. } => {
                uses.push(*base);
                defs.push(*dst);
            }
            Insn::Store { base, src, .. } => {
                uses.push(*base);
                if let Src::Reg(reg) = src {
                    uses.push(*reg);
                }
            }
            Insn::Lddw { dst, .. } => defs.push(*dst),
            Insn::Call { .. } => {
                uses.extend([1, 2]);
                defs.push(0);
            }
        }
        for reg in uses {
            if !defined[reg as usize] {
                gen[reg as usize] = true;
            }
        }
        for reg in defs {
            defined[reg as usize] = true;
            kill[reg as usize] = true;
        }
    }
}

fn map_names(func: &Func) -> Vec<String> {
    let mut names = Vec::new();
    for reloc in &func.relocs {
        let name = format!(
            "map_{}",
            reloc
                .symbol
                .replace(|ch: char| !ch.is_ascii_alphanumeric(), "_")
        );
        if !names.contains(&name) {
            names.push(name);
        }
    }
    names
}

fn emit_block(
    emit: &mut Emit,
    insns: &[Insn],
    maps: &BTreeMap<u32, String>,
    regs: &mut [Rv; 11],
    mut facts: Facts,
    relocated: &BTreeSet<u32>,
) -> Result<(), String> {
    for insn in insns {
        if matches!(insn, Insn::Jmp { .. }) {
            break;
        }
        let before = emit.lines.len();
        apply(&mut facts, insn, relocated)?;
        match insn {
            Insn::Alu {
                width,
                op,
                dst,
                src,
                extra,
                ..
            } => {
                if *width == Width::W64 && *op == AluOp::Mov && matches!(src, Src::Reg(_)) {
                    let Src::Reg(reg) = src else { unreachable!() };
                    regs[*dst as usize] = regs[*reg as usize].clone();
                } else if *width == Width::W64
                    && matches!(*op, AluOp::Add | AluOp::Sub)
                    && is_ptr(facts.kind[*dst as usize])
                    && matches!(regs[*dst as usize], Rv::Ptr(_, _))
                {
                    let Rv::Ptr(kind, name) = regs[*dst as usize].clone() else {
                        unreachable!()
                    };
                    let raw = match src {
                        Src::Imm(imm) => (*imm as i64).to_string(),
                        Src::Reg(reg) => i64_view(emit, &regs[*reg as usize])?,
                    };
                    let delta = if *op == AluOp::Sub {
                        bin(emit, "i64", "sub", "0", &raw)
                    } else {
                        raw
                    };
                    let updated = emit.fresh();
                    emit.lines
                        .push(format!("  {updated} = gep ptr {name}, 1 x i64 {delta}"));
                    regs[*dst as usize] = Rv::Ptr(kind, updated);
                } else {
                    emit_alu(emit, regs, *width, *op, *dst, src, *extra)?;
                    if facts.kind[*dst as usize] == Kind::Pkt {
                        let Rv::I64(name) = regs[*dst as usize].clone() else {
                            unreachable!()
                        };
                        regs[*dst as usize] = Rv::Packet(name);
                    }
                }
            }
            Insn::End {
                dst, bits, to_be, ..
            } => emit_end(emit, regs, *dst, *bits, *to_be)?,
            Insn::Load {
                size,
                signed,
                dst,
                base,
                off,
                ..
            } => emit_load(
                emit,
                regs,
                *size,
                *signed,
                *dst,
                *base,
                *off,
                facts.kind[*dst as usize],
            )?,
            Insn::Store {
                size,
                base,
                off,
                src,
                ..
            } => emit_store(emit, regs, *size, *base, *off, src)?,
            Insn::Lddw {
                dst,
                imm,
                pseudo,
                index,
            } => {
                if let Some(name) = maps.get(index) {
                    regs[*dst as usize] = Rv::Ptr(Kind::Map, format!("%{name}"));
                } else if *pseudo != 0 {
                    return Err(format!(
                        "slot {index}: LDDW pseudo {pseudo} is not a constant or a map relocation"
                    ));
                } else {
                    regs[*dst as usize] = Rv::I64(imm.to_string());
                }
            }
            Insn::Call { id, index } => {
                if *id != 1 {
                    return Err(format!("slot {index}: helper {id} has no call contract"));
                }
                let map = as_ptr(&regs[1], "helper 1 map")?;
                let key = address(emit, &regs[2], 0)?;
                let name = emit.fresh();
                emit.lines.push(format!(
                    "  {name} = call ptr @bpf_map_lookup_elem({map}, {key})"
                ));
                regs[0] = Rv::Ptr(Kind::MapVal, name);
                for slot in &mut regs[1..=5] {
                    *slot = Rv::None;
                }
            }
            Insn::Jmp { .. } => {}
        }
        let created = defined_names(&emit.lines[before..]);
        emit.origin.entry(insn.index()).or_default().extend(created);
    }
    Ok(())
}

fn defined_names(lines: &[String]) -> Vec<String> {
    lines
        .iter()
        .filter_map(|line| {
            line.trim()
                .split_once(" = ")
                .map(|(name, _)| name.to_owned())
        })
        .collect()
}

fn emit_term(
    emit: &mut Emit,
    blocks: &[Block],
    bi: usize,
    insns: &[Insn],
    regs: &[Rv; 11],
) -> Result<(), String> {
    let last = &insns[blocks[bi].insns.end - 1];
    let Insn::Jmp {
        cond,
        dst,
        src,
        width,
        index,
        ..
    } = last
    else {
        let next = blocks.get(bi + 1).ok_or("block falls off the end")?;
        emit.lines.push(format!("  br label %s{}", next.start));
        return Ok(());
    };
    if *cond == Cond::Exit {
        let value = i64_view(emit, &regs[0])
            .map_err(|_| format!("slot {index}: exit reads r0 before it is written"))?;
        emit.lines.push(format!("  ret i64 {value}"));
        return Ok(());
    }
    let target = crate::decode::target_slot(last).unwrap() as u32;
    if *cond == Cond::Ja {
        emit.lines.push(format!("  br label %s{target}"));
        return Ok(());
    }
    let left = i64_view(emit, &regs[*dst as usize])?;
    let right = match src {
        Src::Reg(reg) => i64_view(emit, &regs[*reg as usize])?,
        Src::Imm(imm) => if *width == Width::W32 {
            (*imm as u32) as i64
        } else {
            *imm as i64
        }
        .to_string(),
    };
    let (lhs, rhs, cmp_ty) = if *width == Width::W32 {
        (trunc(emit, &left), trunc(emit, &right), "i32")
    } else {
        (left, right, "i64")
    };
    let cmp = emit.fresh();
    let pred = icmp_name(*cond);
    emit.lines
        .push(format!("  {cmp} = icmp {pred}{cmp_ty} {lhs}, {rhs}"));
    let fall = insns
        .get(blocks[bi].insns.end)
        .map(Insn::index)
        .ok_or("conditional jump has no fallthrough")?;
    emit.lines
        .push(format!("  br i1 {cmp}, label %s{target}, label %s{fall}"));
    Ok(())
}

fn emit_alu(
    emit: &mut Emit,
    regs: &mut [Rv; 11],
    width: Width,
    op: AluOp,
    dst: u8,
    src: &Src,
    extra: u8,
) -> Result<(), String> {
    if op == AluOp::Mov && matches!(src, Src::Imm(_)) {
        let Src::Imm(imm) = *src else { unreachable!() };
        let value = if width == Width::W32 {
            (imm as u32) as i64
        } else {
            imm as i64
        };
        regs[dst as usize] = Rv::I64(value.to_string());
        return Ok(());
    }
    let dst_v = if matches!(op, AluOp::Mov | AluOp::Movsx) {
        "0".to_owned()
    } else {
        i64_view(emit, &regs[dst as usize])?
    };
    let src_v = match src {
        Src::Reg(reg) => i64_view(emit, &regs[*reg as usize])?,
        Src::Imm(imm) => if width == Width::W32 {
            (*imm as u32) as i64
        } else {
            *imm as i64
        }
        .to_string(),
    };
    let result = if op == AluOp::Movsx {
        let signed = movsx(emit, &src_v, extra)?;
        if width == Width::W32 {
            let narrow = trunc(emit, &signed);
            zext(emit, &narrow)
        } else {
            signed
        }
    } else if width == Width::W32 {
        let a = trunc(emit, &dst_v);
        let b = if matches!(src, Src::Imm(_)) {
            src_v
        } else {
            trunc(emit, &src_v)
        };
        let narrow = alu_op(emit, "i32", op, &a, &b, extra, &dst_v)?;
        zext(emit, &narrow)
    } else {
        alu_op(emit, "i64", op, &dst_v, &src_v, extra, &dst_v)?
    };
    regs[dst as usize] = Rv::I64(result);
    Ok(())
}

fn alu_op(
    emit: &mut Emit,
    ty: &str,
    op: AluOp,
    dst: &str,
    src: &str,
    extra: u8,
    wide_dst: &str,
) -> Result<String, String> {
    let name = match op {
        AluOp::Add => bin(emit, ty, "add", dst, src),
        AluOp::Sub => bin(emit, ty, "sub", dst, src),
        AluOp::Mul => bin(emit, ty, "mul", dst, src),
        AluOp::Or => bin(emit, ty, "or", dst, src),
        AluOp::And => bin(emit, ty, "and", dst, src),
        AluOp::Xor => bin(emit, ty, "xor", dst, src),
        AluOp::Neg => bin(emit, ty, "sub", "0", dst),
        AluOp::Lsh => {
            let amount = masked(emit, ty, src);
            bin(emit, ty, "shl", dst, &amount)
        }
        AluOp::Rsh => {
            let amount = masked(emit, ty, src);
            bin(emit, ty, "lshr", dst, &amount)
        }
        AluOp::Arsh => {
            let amount = masked(emit, ty, src);
            bin(emit, ty, "ashr", dst, &amount)
        }
        AluOp::Mov => src.to_string(),
        AluOp::Movsx => movsx(emit, src, extra)?,
        AluOp::Div => divmod(emit, ty, "udiv", dst, src, false, wide_dst)?,
        AluOp::Mod => divmod(emit, ty, "urem", dst, src, false, wide_dst)?,
        AluOp::Sdiv => divmod(emit, ty, "sdiv", dst, src, true, wide_dst)?,
        AluOp::Smod => divmod(emit, ty, "srem", dst, src, true, wide_dst)?,
    };
    Ok(name)
}

fn masked(emit: &mut Emit, ty: &str, src: &str) -> String {
    let mask = if ty == "i32" { "31" } else { "63" };
    bin(emit, ty, "and", src, mask)
}

fn bin(emit: &mut Emit, ty: &str, op: &str, lhs: &str, rhs: &str) -> String {
    let name = emit.fresh();
    emit.lines
        .push(format!("  {name} = {op} {ty} {lhs}, {rhs}"));
    name
}

fn trunc(emit: &mut Emit, value: &str) -> String {
    let name = emit.fresh();
    emit.lines
        .push(format!("  {name} = trunc i64 {value} to i32"));
    name
}

fn zext(emit: &mut Emit, value: &str) -> String {
    let name = emit.fresh();
    emit.lines
        .push(format!("  {name} = zext i32 {value} to i64"));
    name
}

fn movsx(emit: &mut Emit, value: &str, bits: u8) -> Result<String, String> {
    let ty = match bits {
        8 => "i8",
        16 => "i16",
        32 => "i32",
        _ => return Err(format!("MOVSX width {bits} is not supported")),
    };
    let narrow = emit.fresh();
    emit.lines
        .push(format!("  {narrow} = trunc i64 {value} to {ty}"));
    let wide = emit.fresh();
    emit.lines
        .push(format!("  {wide} = sext {ty} {narrow} to i64"));
    Ok(wide)
}

fn divmod(
    emit: &mut Emit,
    ty: &str,
    op: &str,
    dst: &str,
    src: &str,
    signed: bool,
    _wide_dst: &str,
) -> Result<String, String> {
    let zero = emit.fresh();
    emit.lines.push(format!("  {zero} = icmp eq {ty} {src}, 0"));
    let zero_lab = emit.lab();
    let ok_lab = emit.lab();
    let join = emit.lab();
    emit.lines.push(format!(
        "  br i1 {zero}, label %{zero_lab}, label %{ok_lab}"
    ));
    emit.lines.push(format!("{zero_lab}:"));
    let zero_res = if op == "udiv" || op == "sdiv" {
        "0".to_string()
    } else {
        dst.to_string()
    };
    emit.lines.push(format!("  br label %{join}"));
    let (ok_res, ok_from) = if signed {
        let min_lab = emit.lab();
        let wrap_lab = emit.lab();
        let do_lab = emit.lab();
        emit.lines.push(format!("{ok_lab}:"));
        let minv = if ty == "i32" {
            "-2147483648"
        } else {
            "-9223372036854775808"
        };
        let is_min = emit.fresh();
        emit.lines
            .push(format!("  {is_min} = icmp eq {ty} {dst}, {minv}"));
        emit.lines.push(format!(
            "  br i1 {is_min}, label %{min_lab}, label %{do_lab}"
        ));
        emit.lines.push(format!("{min_lab}:"));
        let is_m1 = emit.fresh();
        emit.lines
            .push(format!("  {is_m1} = icmp eq {ty} {src}, -1"));
        emit.lines.push(format!(
            "  br i1 {is_m1}, label %{wrap_lab}, label %{do_lab}"
        ));
        emit.lines.push(format!("{wrap_lab}:"));
        let wrap_res = if op == "srem" {
            "0".to_string()
        } else {
            dst.to_string()
        };
        emit.lines.push(format!("  br label %{join}"));
        emit.lines.push(format!("{do_lab}:"));
        let quot = bin(emit, ty, op, dst, src);
        emit.lines.push(format!("  br label %{join}"));
        let phi = emit.fresh();
        emit.lines.push(format!("{join}:"));
        emit.lines.push(format!("  {phi} = phi {ty} [ {zero_res}, %{zero_lab} ], [ {wrap_res}, %{wrap_lab} ], [ {quot}, %{do_lab} ]"));
        return Ok(phi);
    } else {
        emit.lines.push(format!("{ok_lab}:"));
        let quot = bin(emit, ty, op, dst, src);
        emit.lines.push(format!("  br label %{join}"));
        (quot, ok_lab)
    };
    emit.lines.push(format!("{join}:"));
    let phi = emit.fresh();
    emit.lines.push(format!(
        "  {phi} = phi {ty} [ {zero_res}, %{zero_lab} ], [ {ok_res}, %{ok_from} ]"
    ));
    Ok(phi)
}

fn emit_end(
    emit: &mut Emit,
    regs: &mut [Rv; 11],
    dst: u8,
    bits: u8,
    to_be: bool,
) -> Result<(), String> {
    let value = i64_view(emit, &regs[dst as usize])?;
    let result = if to_be {
        swab(emit, &value, bits)?
    } else {
        zero_ext(emit, &value, bits)?
    };
    regs[dst as usize] = Rv::I64(result);
    Ok(())
}

fn zero_ext(emit: &mut Emit, value: &str, bits: u8) -> Result<String, String> {
    if bits == 64 {
        return Ok(value.to_string());
    }
    let ty = if bits == 16 {
        "i16"
    } else if bits == 32 {
        "i32"
    } else {
        return Err("bad END size".into());
    };
    let narrow = emit.fresh();
    emit.lines
        .push(format!("  {narrow} = trunc i64 {value} to {ty}"));
    let wide = emit.fresh();
    emit.lines
        .push(format!("  {wide} = zext {ty} {narrow} to i64"));
    Ok(wide)
}

fn swab(emit: &mut Emit, value: &str, bits: u8) -> Result<String, String> {
    let nbytes = (bits / 8) as i32;
    if nbytes == 0 || bits > 64 {
        return Err("bad END size".into());
    }
    let mut acc: Option<String> = None;
    for byte in 0..nbytes {
        let shift = byte * 8;
        let moved = if shift == 0 {
            value.to_string()
        } else {
            bin(emit, "i64", "lshr", value, &shift.to_string())
        };
        let piece = bin(emit, "i64", "and", &moved, "255");
        let dest = (nbytes - 1 - byte) * 8;
        let placed = if dest == 0 {
            piece
        } else {
            bin(emit, "i64", "shl", &piece, &dest.to_string())
        };
        acc = Some(match acc {
            None => placed,
            Some(prev) => bin(emit, "i64", "or", &prev, &placed),
        });
    }
    Ok(acc.unwrap())
}

fn emit_load(
    emit: &mut Emit,
    regs: &mut [Rv; 11],
    size: MemSize,
    signed: bool,
    dst: u8,
    base: u8,
    off: i16,
    kind: Kind,
) -> Result<(), String> {
    let ptr = address(emit, &regs[base as usize], off as i64)?;
    let ty = if is_ptr(kind) && kind != Kind::Pkt {
        "ptr"
    } else {
        mem_ty(size)
    };
    let loaded = emit.fresh();
    emit.lines.push(format!(
        "  {loaded} = load {ty}, {ptr}, align {}",
        align(size)
    ));
    let wide = if ty == "ptr" {
        loaded
    } else if signed {
        let name = emit.fresh();
        emit.lines
            .push(format!("  {name} = sext {ty} {loaded} to i64"));
        name
    } else if size == MemSize::Dword {
        loaded
    } else {
        let name = emit.fresh();
        emit.lines
            .push(format!("  {name} = zext {ty} {loaded} to i64"));
        name
    };
    regs[dst as usize] = rv_of(kind, wide);
    Ok(())
}

fn emit_store(
    emit: &mut Emit,
    regs: &[Rv; 11],
    size: MemSize,
    base: u8,
    off: i16,
    src: &Src,
) -> Result<(), String> {
    let ptr = address(emit, &regs[base as usize], off as i64)?;
    if let Src::Reg(reg) = src {
        if matches!(regs[*reg as usize], Rv::Ptr(_, _)) {
            let stored = as_ptr(&regs[*reg as usize], "stored value")?;
            emit.lines
                .push(format!("  store {stored}, {ptr}, align {}", align(size)));
            return Ok(());
        }
    }
    let raw = match src {
        Src::Reg(reg) => i64_view(emit, &regs[*reg as usize])?,
        Src::Imm(imm) => imm.to_string(),
    };
    let ty = mem_ty(size);
    let stored = if size == MemSize::Dword {
        raw
    } else {
        let name = emit.fresh();
        emit.lines
            .push(format!("  {name} = trunc i64 {raw} to {ty}"));
        name
    };
    emit.lines.push(format!(
        "  store {ty} {stored}, {ptr}, align {}",
        align(size)
    ));
    Ok(())
}

fn address(emit: &mut Emit, base: &Rv, off: i64) -> Result<String, String> {
    match base {
        Rv::Ptr(Kind::Ctx | Kind::Stack | Kind::MapVal, name) => {
            Ok(gep(emit, &format!("ptr {name}"), off))
        }
        Rv::Packet(name) => {
            let delta = bin(emit, "i64", "sub", name, "%pkt_base");
            let adjusted = if off == 0 {
                delta
            } else {
                bin(emit, "i64", "add", &delta, &off.to_string())
            };
            let ptr = emit.fresh();
            emit.lines
                .push(format!("  {ptr} = gep ptr %pkt, 1 x i64 {adjusted}"));
            Ok(format!("ptr {ptr}"))
        }
        _ => Err("memory base is not a dereferenceable pointer".into()),
    }
}

fn gep(emit: &mut Emit, ptr: &str, off: i64) -> String {
    if off == 0 {
        return ptr.to_string();
    }
    let name = emit.fresh();
    emit.lines
        .push(format!("  {name} = gep {ptr}, 1 x i64 {off}"));
    format!("ptr {name}")
}

fn i64_view(emit: &mut Emit, value: &Rv) -> Result<String, String> {
    match value {
        Rv::I64(name) | Rv::Packet(name) => Ok(name.clone()),
        Rv::Ptr(_, name) => {
            let out = emit.fresh();
            emit.lines
                .push(format!("  {out} = ptrtoint ptr {name} to i64"));
            Ok(out)
        }
        Rv::None => Err("value is uninitialized".into()),
    }
}

fn as_ptr(value: &Rv, what: &str) -> Result<String, String> {
    match value {
        Rv::Ptr(_, name) => Ok(format!("ptr {name}")),
        _ => Err(format!("{what} is not a pointer")),
    }
}

fn mem_ty(size: MemSize) -> &'static str {
    match size {
        MemSize::Byte => "i8",
        MemSize::Half => "i16",
        MemSize::Word => "i32",
        MemSize::Dword => "i64",
    }
}

fn align(size: MemSize) -> u8 {
    match size {
        MemSize::Byte => 1,
        MemSize::Half => 2,
        MemSize::Word => 4,
        MemSize::Dword => 8,
    }
}

fn icmp_name(cond: Cond) -> &'static str {
    match cond {
        Cond::Jeq => "eq ",
        Cond::Jne => "ne ",
        Cond::Jgt => "ugt ",
        Cond::Jge => "uge ",
        Cond::Jlt => "ult ",
        Cond::Jle => "ule ",
        Cond::Jsgt => "sgt ",
        Cond::Jsge => "sge ",
        Cond::Jslt => "slt ",
        Cond::Jsle => "sle ",
        Cond::Ja | Cond::Exit => "",
    }
}

impl Emit {
    fn fresh(&mut self) -> String {
        let name = format!("%v{}", self.n);
        self.n += 1;
        name
    }

    fn lab(&mut self) -> String {
        let name = format!("d{}", self.n);
        self.n += 1;
        name
    }
}
