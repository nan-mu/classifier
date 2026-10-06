//! T0: forward `if` → assert; backward `if` kept; unconditional `goto` always follows.
use super::environment::Environment;
use super::op::*;
use super::state;
use anyhow::{bail, ensure, Context, Result};

fn next_index(table: &[Line], i: usize) -> Option<usize> {
    let n = i + 1;
    (n < table.len()).then_some(n)
}

/// Expand forward `if` into asserts (taken first); leave backward control in place.
pub(crate) fn run(table: &[Line], env: &Environment) -> Result<Vec<Path>> {
    ensure!(!table.is_empty(), "T0: empty table");
    ensure!(env.entry < table.len(), "T0: entry outside table");
    let mut paths = Vec::new();
    expand(table, env, env.entry, Vec::new(), &mut paths)?;
    Ok(paths)
}

fn expand(
    table: &[Line],
    env: &Environment,
    mut i: usize,
    mut path: Path,
    out: &mut Vec<Path>,
) -> Result<()> {
    loop {
        ensure!(
            path.len() < env.max_path_len,
            "T0: path length budget exceeded; no partial result returned"
        );
        ensure!(
            out.len() < env.max_paths,
            "T0: path count budget exceeded; no partial result returned"
        );
        let line = table.get(i).context("T0: index outside table")?;
        match line.op {
            Op::Branch {
                cmp,
                a,
                b,
                target,
            } => {
                if target > i {
                    // Forward conditional: taken first, then fallthrough.
                    let mut taken = path.clone();
                    taken.push(Line::new(
                        i,
                        Op::Assert {
                            cmp,
                            a,
                            b,
                            taken: true,
                        },
                    ));
                    expand(table, env, target, taken, out)?;
                    path.push(Line::new(
                        i,
                        Op::Assert {
                            cmp,
                            a,
                            b,
                            taken: false,
                        },
                    ));
                    let Some(n) = next_index(table, i) else {
                        bail!("T0: forward if has no fallthrough");
                    };
                    i = n;
                } else {
                    // Backward if: keep text, continue at next.
                    path.push(line.clone());
                    let Some(n) = next_index(table, i) else {
                        out.push(path);
                        return Ok(());
                    };
                    i = n;
                }
            }
            Op::Jump(target) => {
                // Unconditional goto always continues at the target (keep text).
                // Address-backward edges that remain acyclic (e.g. 74→36) must be
                // followed; falling through would reach padding traps.
                ensure!(
                    target < table.len(),
                    "T0: goto target {target} outside table at index {i}"
                );
                path.push(line.clone());
                i = target;
            }
            Op::Exit => {
                path.push(line.clone());
                state::walk(&mut path, env, "T0 return guard", |_, _| Ok(()))?;
                out.push(path);
                return Ok(());
            }
            Op::Trap => bail!("T0 index {i}: reachable trap"),
            Op::Call { next, .. } => {
                path.push(line.clone());
                i = next;
            }
            _ => {
                path.push(line.clone());
                let Some(n) = next_index(table, i) else {
                    out.push(path);
                    return Ok(());
                };
                i = n;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn forward_if_becomes_asserts_taken_first() {
        let table = vec![
            Line::new(
                0,
                Op::Branch {
                    cmp: Cmp::Eq,
                    a: 1,
                    b: 2,
                    target: 2,
                },
            ),
            Line::new(
                1,
                Op::Set {
                    rd: 10,
                    src: Operand::Imm(1),
                },
            ),
            Line::new(
                2,
                Op::Set {
                    rd: 10,
                    src: Operand::Imm(2),
                },
            ),
            Line::new(3, Op::Exit),
        ];
        let paths = run(&table, &Environment::default()).unwrap();
        assert_eq!(paths.len(), 2);
        assert!(paths[0][0].body.contains("assert") && paths[0][0].body.contains("true"));
        assert!(paths[1][0].body.contains("assert") && paths[1][0].body.contains("false"));
        assert!(!paths.iter().any(|p| p.iter().any(|l| l.body.starts_with("if "))));
    }
    #[test]
    fn backward_if_kept_and_not_followed() {
        let table = vec![
            Line::new(
                0,
                Op::Set {
                    rd: 10,
                    src: Operand::Imm(0),
                },
            ),
            Line::new(
                1,
                Op::Branch {
                    cmp: Cmp::Ne,
                    a: 10,
                    b: 0,
                    target: 0,
                },
            ),
            Line::new(2, Op::Exit),
        ];
        let paths = run(&table, &Environment::default()).unwrap();
        assert_eq!(paths.len(), 1);
        assert!(paths[0][1].body.starts_with("if "));
        assert_eq!(
            paths[0].iter().map(|l| l.index).collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
    }
}
