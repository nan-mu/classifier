# Profile integration

对 `profile.toml` 里每一个程序，确认 XDP ELF 和 eBPF 对象都在，并且双架构比较结果等于该程序声明的 `expect`。

## Sub-features

- `profile-artifacts` 确认每个 `[[program]]` 的 `elf` 和 `bpf` 都是文件。
- `profile-outcome` 按 `strict`、`weak` 或 `fail` 比较展开结果。

## How to get to it (user POV)

- 在 classifier 仓库运行 `python3 .cursor/skills/verify-classifier/scripts/drive.py --gate profile`。
- 这条命令执行 `cargo test --manifest-path tooling/Cargo.toml -p server --test profile_expect -- --nocapture`。

## Driving it with verify-classifier

Preconditions:

- doctor 的最后一行是 `doctor ok`。
- 本轮没有另一条 cargo 在编译 `tooling/`。

- **跑完全部程序。** 运行 `python3 .cursor/skills/verify-classifier/scripts/drive.py --gate profile`。脚本打印 `.audit/verify-classifier/<stamp>-profile/`。
- **证明。** `exit_code.txt` 是 `0`。`stdout.txt` 含 `test result: ok`。`stderr.txt` 里每个 `[[program]]` 都有 `profile <name> ok pass`。缺一个程序名就是失败。

## Gotchas

- `expect = "weak"` 时，表达式没对齐并且 kind 顺序一致才是通过。改 `expect` 来迎合这次结果，验证作废。
- doctor 已经报缺失 ELF 或 bpf 时，不要删掉该 `[[program]]` 再重跑。
- 不带 `--nocapture` 时，cargo 会藏起 `profile <name> ok pass`。`drive.py` 已经带上。手跑 cargo 时漏掉它，就不能用退出码单独当证明。
- 展开全部程序大约需要一分钟。中途停掉后，半截日志不是通过。
