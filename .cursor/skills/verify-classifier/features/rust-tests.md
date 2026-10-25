# Rust tests

Rust 功能测试覆盖 workspace 里的库、二进制，以及 profile 以外的集成测试。profile 预期由另一条 feature 负责。

## Sub-features

- `crate-units` 跑 `lean-binding`、`server`、`xpost-elf` 的库内测试和二进制测试。
- `crate-functional` 跑 `tests/` 里除 `profile_programs_match_expect` 以外的用例。

## How to get to it (user POV)

- 在 classifier 仓库运行 `python3 .cursor/skills/verify-classifier/scripts/drive.py --gate rust`。
- 这条命令执行 `cargo test --manifest-path tooling/Cargo.toml --workspace --lib --bins --tests -- --skip profile_programs_match_expect`。

## Driving it with verify-classifier

Preconditions:

- doctor 的最后一行是 `doctor ok`。
- 本轮没有另一条 cargo 在编译 `tooling/`。

- **跑测试。** 运行 `python3 .cursor/skills/verify-classifier/scripts/drive.py --gate rust`。脚本打印 `.audit/verify-classifier/<stamp>-rust/`。
- **证明。** `exit_code.txt` 是 `0`。`stdout.txt` 里每个实际执行的测试二进制都有 `test result: ok`。出现 `FAILED` 就是失败。`profile_programs_match_expect` 不在这次结果里。

## Gotchas

- 去掉 `--skip profile_programs_match_expect` 会把 profile 集成测试卷进来。那不再是这一条 feature。
- `tooling/web` 的 Vitest 不在这条命令里。网页断言失败不影响这条门，也不要为了它去跑 `npm test`。
- `src/main.rs` 的 HTTP 测试会临时监听本机端口。它们随测试进程退出，不要另起 `lake run dev`。
- `lean-binding` 的测试调用已经构建的 Lean 共享库。doctor 报共享库缺失时先跑 Launch，不要把链接错误改成忽略。
