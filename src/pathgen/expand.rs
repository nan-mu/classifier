//! Structured path expansion: forward `IfGoto` → `Assert` (taken then fallthrough).

use anyhow::{bail, ensure, Context, Result};
use std::collections::HashMap;

use crate::predicate::{Insn, Origin, Predicate, PredicateId, Prefix};

use super::offset::resolve_target;
use super::Path;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GotoPolicy {
    /// Follow forward `goto` only; backward keeps text and continues sequentially.
    Bpf,
    /// Always follow `goto` target (acyclic address-backward edges allowed).
    Rv32,
}

#[derive(Clone, Copy, Debug)]
pub struct ExpandConfig {
    /// Program-table position to start from.
    pub entry_pos: usize,
    pub goto: GotoPolicy,
    pub max_paths: usize,
    pub max_path_len: usize,
}

enum Ctrl {
    Cond {
        condition: crate::predicate::Condition,
        target: u32,
    },
    Goto {
        target: u32,
    },
    Exit,
    Trap {
        reason: String,
    },
    Other,
}

struct Prog<'a> {
    insns: &'a [Insn],
    at: HashMap<u32, usize>,
    next_id: u64,
}

impl<'a> Prog<'a> {
    fn new(insns: &'a [Insn]) -> Result<Self> {
        ensure!(!insns.is_empty(), "pathgen: empty program");
        let mut at = HashMap::new();
        let mut next_id = 0u64;
        for (pos, insn) in insns.iter().enumerate() {
            if at.insert(insn.index, pos).is_some() {
                bail!("pathgen: duplicate index {}", insn.index);
            }
            for node in &insn.prefix.0 {
                next_id = next_id.max(node.id.0 + 1);
            }
        }
        for w in insns.windows(2) {
            ensure!(
                w[0].index < w[1].index,
                "pathgen: indices not strictly ordered"
            );
        }
        Ok(Self {
            insns,
            at,
            next_id,
        })
    }

    fn pos_of(&self, index: u32) -> Result<usize> {
        self.at
            .get(&index)
            .copied()
            .with_context(|| format!("pathgen: target index {index} is not an instruction entry"))
    }

    fn next_pos(&self, pos: usize) -> Option<usize> {
        let n = pos + 1;
        (n < self.insns.len()).then_some(n)
    }

    fn alloc_id(&mut self) -> PredicateId {
        let id = PredicateId(self.next_id);
        self.next_id += 1;
        id
    }
}

fn classify(insn: &Insn) -> Result<Ctrl> {
    let mut ctrl = Ctrl::Other;
    for node in &insn.prefix.0 {
        match &node.predicate {
            Predicate::IfGoto { condition, offset } => {
                let target = resolve_target(insn.index, offset)?;
                ctrl = Ctrl::Cond {
                    condition: condition.clone(),
                    target,
                };
            }
            Predicate::Goto { offset } => {
                let target = resolve_target(insn.index, offset)?;
                ctrl = Ctrl::Goto { target };
            }
            Predicate::Exit => ctrl = Ctrl::Exit,
            Predicate::Trap { reason } => {
                ctrl = Ctrl::Trap {
                    reason: reason.clone(),
                };
            }
            Predicate::Assert { .. }
            | Predicate::Call { .. }
            | Predicate::Set { .. }
            | Predicate::AluAssign { .. }
            | Predicate::Alu { .. }
            | Predicate::AluCall { .. }
            | Predicate::Load { .. }
            | Predicate::Store { .. }
            | Predicate::Empty => {}
        }
    }
    Ok(ctrl)
}

fn replace_if_with_assert(
    prog: &mut Prog<'_>,
    insn: &Insn,
    condition: crate::predicate::Condition,
    expected: bool,
) -> Insn {
    let id = prog.alloc_id();
    let mut prefix = Prefix::new();
    let mut replaced = false;
    for node in &insn.prefix.0 {
        match &node.predicate {
            Predicate::IfGoto { .. } if !replaced => {
                prefix.push(
                    id,
                    Predicate::Assert {
                        condition: condition.clone(),
                        expected,
                    },
                    Origin::stage("pathgen"),
                );
                replaced = true;
            }
            Predicate::IfGoto { .. } => {}
            other => prefix.push(node.id, other.clone(), node.origin.clone()),
        }
    }
    if !replaced {
        prefix.push(
            id,
            Predicate::Assert {
                condition,
                expected,
            },
            Origin::stage("pathgen"),
        );
    }
    Insn {
        index: insn.index,
        machine: insn.machine.clone(),
        prefix,
    }
}

fn push_clone(path: &mut Path, insn: &Insn) {
    path.insns.push(insn.clone());
}

/// Expand control into ordered syntax paths (`taken_paths ++ fallthrough_paths`).
///
/// Path filename codes start at `"0"`; each forward conditional appends `'1'`
/// (taken) or `'0'` (fallthrough).
pub fn expand(insns: &[Insn], cfg: ExpandConfig) -> Result<Vec<Path>> {
    let mut prog = Prog::new(insns)?;
    ensure!(
        cfg.entry_pos < insns.len(),
        "pathgen: entry position {} outside table",
        cfg.entry_pos
    );
    let mut out = Vec::new();
    expand_from(&mut prog, cfg, cfg.entry_pos, Path::at_entry(), &mut out)?;
    Ok(out)
}

fn expand_from(
    prog: &mut Prog<'_>,
    cfg: ExpandConfig,
    mut pos: usize,
    mut path: Path,
    out: &mut Vec<Path>,
) -> Result<()> {
    loop {
        ensure!(
            path.insns.len() < cfg.max_path_len,
            "pathgen: path length budget exceeded; no partial result returned"
        );
        ensure!(
            out.len() < cfg.max_paths,
            "pathgen: path count budget exceeded; no partial result returned"
        );
        let insn = prog
            .insns
            .get(pos)
            .with_context(|| format!("pathgen: position {pos} outside table"))?
            .clone();
        match classify(&insn)? {
            Ctrl::Exit => {
                push_clone(&mut path, &insn);
                out.push(path);
                return Ok(());
            }
            Ctrl::Trap { reason } => {
                bail!(
                    "pathgen: reachable trap at index {}: {reason}",
                    insn.index
                );
            }
            Ctrl::Cond { condition, target } => {
                if target > insn.index {
                    let taken_pos = prog.pos_of(target)?;
                    let mut taken = path.clone();
                    taken.code.push('1');
                    taken.insns.push(replace_if_with_assert(
                        prog,
                        &insn,
                        condition.clone(),
                        true,
                    ));
                    expand_from(prog, cfg, taken_pos, taken, out)?;

                    path.code.push('0');
                    path.insns
                        .push(replace_if_with_assert(prog, &insn, condition, false));
                    let Some(next) = prog.next_pos(pos) else {
                        bail!(
                            "pathgen: forward if at index {} has no fallthrough",
                            insn.index
                        );
                    };
                    pos = next;
                } else {
                    // Backward if: keep IfGoto, continue sequentially (code unchanged).
                    push_clone(&mut path, &insn);
                    let Some(next) = prog.next_pos(pos) else {
                        out.push(path);
                        return Ok(());
                    };
                    pos = next;
                }
            }
            Ctrl::Goto { target } => match cfg.goto {
                GotoPolicy::Bpf => {
                    if target > insn.index {
                        let tgt = prog.pos_of(target)?;
                        push_clone(&mut path, &insn);
                        pos = tgt;
                    } else {
                        push_clone(&mut path, &insn);
                        let Some(next) = prog.next_pos(pos) else {
                            out.push(path);
                            return Ok(());
                        };
                        pos = next;
                    }
                }
                GotoPolicy::Rv32 => {
                    let tgt = prog.pos_of(target)?;
                    push_clone(&mut path, &insn);
                    pos = tgt;
                }
            },
            Ctrl::Other => {
                push_clone(&mut path, &insn);
                let Some(next) = prog.next_pos(pos) else {
                    out.push(path);
                    return Ok(());
                };
                pos = next;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate::{
        BitVec, CmpOp, Condition, Machine, Operand, Origin, Predicate, PredicateId, Prefix, Reg,
    };
    use crate::predicate::print::print_prefix;

    fn insn(index: u32, pred: Predicate) -> Insn {
        let mut prefix = Prefix::new();
        prefix.push(PredicateId(index as u64), pred, Origin::stage("prefixgen"));
        Insn {
            index,
            machine: Machine::Rv32(index),
            prefix,
        }
    }

    fn if_goto(index: u32, target: u32) -> Insn {
        let off = target as i64 - index as i64 - 1;
        let offset = if off >= 0 {
            format!("+{off:#x}")
        } else {
            format!("-{0:#x}", (-off) as u64)
        };
        insn(
            index,
            Predicate::IfGoto {
                condition: Condition {
                    lhs: Operand::Reg(Reg::w(1)),
                    op: CmpOp::Eq,
                    rhs: Operand::Imm(BitVec::Bv32(0)),
                },
                offset,
            },
        )
    }

    fn goto(index: u32, target: u32) -> Insn {
        let off = target as i64 - index as i64 - 1;
        let offset = if off >= 0 {
            format!("+{off:#x}")
        } else {
            format!("-{0:#x}", (-off) as u64)
        };
        insn(index, Predicate::Goto { offset })
    }

    fn exit(index: u32) -> Insn {
        insn(index, Predicate::Exit)
    }

    fn set(index: u32) -> Insn {
        insn(
            index,
            Predicate::Set {
                dst: Reg::w(0),
                src: Operand::Imm(BitVec::Bv32(1)),
            },
        )
    }

    fn cfg(goto: GotoPolicy) -> ExpandConfig {
        ExpandConfig {
            entry_pos: 0,
            goto,
            max_paths: 64,
            max_path_len: 64,
        }
    }

    #[test]
    fn forward_if_becomes_asserts_taken_first() {
        let prog = vec![if_goto(0, 2), set(1), exit(2)];
        let paths = expand(&prog, cfg(GotoPolicy::Bpf)).unwrap();
        assert_eq!(paths.len(), 2);
        assert_eq!(paths[0].code, "01");
        assert_eq!(paths[1].code, "00");
        assert!(print_prefix(&paths[0].insns[0].prefix).contains("assert"));
        assert!(print_prefix(&paths[0].insns[0].prefix).contains("true"));
        assert!(print_prefix(&paths[1].insns[0].prefix).contains("false"));
        assert_eq!(paths[0].insns[0].machine, prog[0].machine);
        assert_eq!(paths[1].insns[0].machine, prog[0].machine);
        assert!(!paths.iter().any(|p| {
            p.insns
                .iter()
                .any(|i| print_prefix(&i.prefix).starts_with("if "))
        }));
        assert!(matches!(
            paths[0].insns.last().unwrap().prefix.0[0].predicate,
            Predicate::Exit
        ));
    }

    #[test]
    fn backward_if_kept() {
        let prog = vec![set(0), if_goto(1, 0), exit(2)];
        let paths = expand(&prog, cfg(GotoPolicy::Bpf)).unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].code, "0");
        assert!(print_prefix(&paths[0].insns[1].prefix).starts_with("if "));
    }

    #[test]
    fn bpf_backward_goto_falls_through() {
        let prog = vec![set(0), goto(1, 0), exit(2)];
        let paths = expand(&prog, cfg(GotoPolicy::Bpf)).unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].code, "0");
        assert_eq!(
            paths[0].insns.iter().map(|i| i.index).collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
    }

    #[test]
    fn rv32_goto_always_follows() {
        // 0: set; 1: goto 3; 2: set (skipped); 3: exit
        let prog = vec![set(0), goto(1, 3), set(2), exit(3)];
        let paths = expand(&prog, cfg(GotoPolicy::Rv32)).unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].code, "0");
        assert_eq!(
            paths[0].insns.iter().map(|i| i.index).collect::<Vec<_>>(),
            vec![0, 1, 3]
        );
    }

    #[test]
    fn nested_forward_appends_bits() {
        // 0: if → 3; 1: if → 3; 2: set; 3: exit
        let prog = vec![if_goto(0, 3), if_goto(1, 3), set(2), exit(3)];
        let paths = expand(&prog, cfg(GotoPolicy::Bpf)).unwrap();
        let codes: Vec<_> = paths.iter().map(|p| p.code.as_str()).collect();
        assert_eq!(codes, vec!["01", "001", "000"]);
    }

    #[test]
    fn reachable_trap_fails() {
        let prog = vec![insn(
            0,
            Predicate::Trap {
                reason: "IllegalInstruction".into(),
            },
        )];
        assert!(expand(&prog, cfg(GotoPolicy::Rv32)).is_err());
    }
}
