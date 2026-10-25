---
name: verify-classifier
description: Drive classifier's three gates. Use for profile.toml dual-arch outcomes, the sorry-free Verification library, or Rust unit and functional tests. Not for the web UI.
---

# Verify classifier

验证面是命令，不是网页。三类测试只有两个执行器：cargo 跑 profile 集成测试和 Rust 测试，lake 构建 `Verification`。没有 xtask。不跑 `npm test`，不跑 `tooling/scripts/smoke.py`，也不把 `lake run dev` 当作测试。

工作目录是 classifier 仓库根。`drive.py` 只负责启动那两条命令之一并保存输出。

## Launch

没有常驻进程。先构建 Lean 共享库，再编译 profile 集成测试。

```bash
lake build Core Node RV32 EBPF
cargo test --manifest-path tooling/Cargo.toml -p server --test profile_expect --no-run
```

就绪条件是 `python3 .cursor/skills/verify-classifier/scripts/doctor.py` 退出码 0，并且最后一行是 `doctor ok`。`--no-run` 只说明测试二进制已生成。

## Doctor

```bash
python3 .cursor/skills/verify-classifier/scripts/doctor.py
```

脚本只读。它检查 `cargo` 和 `lake` 在 PATH 上，`lakefile.lean` 声明了 `lean_lib Verification`，`profile.toml` 里每个程序的 ELF 和 bpf 都是文件，以及 `.lake/build/lib` 里有 Core、Node、RV32、EBPF 的共享库。失败时先补 Launch，不要改 profile。

## Drive

先跑 doctor。然后从仓库根启动一类：

```bash
python3 .cursor/skills/verify-classifier/scripts/drive.py --gate profile
python3 .cursor/skills/verify-classifier/scripts/drive.py --gate formal
python3 .cursor/skills/verify-classifier/scripts/drive.py --gate rust
```

同一 checkout 不要并行第二条 cargo 或 lake。`lake test` 会按 profile、Verification、Rust 的顺序把三类都跑一遍；复现某一类时用上面的 `--gate`，不要用 `lake test` 代替。

`expect` 的含义以 `tooling/server/src/harness.rs` 为准：

- `strict`：两边 `complete`，compare-tree `fail` 为 0，`expr_incomplete` 为 0。
- `weak`：两边 `complete`，`fail` 为 0，`expr_incomplete` 至少为 1。
- `fail`：有一边没有 `complete`，或某个节点的 kind 顺序不一致。

## Evidence

`drive.py` 打印 `.audit/verify-classifier/<UTC>-<gate>/`。该目录已在 `.gitignore` 里。保留它。

- `command.txt` 是实际 argv。
- `stdout.txt` 和 `stderr.txt` 是完整输出。
- `exit_code.txt` 是进程退出码。
- `pid` 是产生这些文件的进程。

profile 的证明是退出码 0，`stdout.txt` 里有 `test result: ok`，并且每个 `[[program]]` 都有 `profile <name> ok pass`。formal 的证明是退出码 0，并且下面这些定理的 axiom 列表出现在日志里、其中没有 `sorryAx`：

- `Verification.Verified.StateUpdate.assign_lookup`
- `Verification.Verified.StateUpdate.kept_lookup`
- `Verification.Verified.SolveMeaning.solve_preserves_interpretation`
- `Verification.Verified.HistoryAndPath.dependency_blocks_ignoring`
- `Verification.Verified.HistoryAndPath.linearTrace_of_step_preservation`
- `Verification.Verified.HistoryAndPath.drive_equal_states`
- `Verification.Verified.HistoryAndPath.both_directions_rejected`
- `Verification.Verified.UnifyMatch.unify_structural`
- `Verification.Verified.HelperProjection.update_flag_denotation_lost`
- `Verification.Verified.Acceptance.accept_is_structural`
- `Verification.Verified.Acceptance.meanings_if_arguments_survive`

Rust 的证明是退出码 0，且每个执行过的测试二进制都有 `test result: ok`。不要改 `expect`、删程序或跳过失败用例来换通过。

## Cleanup

```bash
python3 .cursor/skills/verify-classifier/scripts/cleanup.py .audit/verify-classifier/<stamp>-<gate>
```

参数必须在 `.audit/verify-classifier/` 下面。cleanup 只向该目录里记录的、仍在运行的 PID 发 `SIGTERM`。它不删除证据目录。不要按进程名结束 cargo 或 lake。

## Helpers

- `python3 .cursor/skills/verify-classifier/scripts/doctor.py`
- `python3 .cursor/skills/verify-classifier/scripts/drive.py --gate profile`
- `python3 .cursor/skills/verify-classifier/scripts/drive.py --gate formal`
- `python3 .cursor/skills/verify-classifier/scripts/drive.py --gate rust`
- `python3 .cursor/skills/verify-classifier/scripts/cleanup.py <evidence-dir>`

feature 地图在 `features/README.md`。
