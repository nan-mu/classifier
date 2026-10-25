# Classifier verification map

先读本索引，再按其中一个 feature 驱动。一次验证只覆盖该文件里的入口。

## Baseline preconditions

- 工作目录是 classifier 仓库根。
- `python3 .cursor/skills/verify-classifier/scripts/doctor.py` 的最后一行是 `doctor ok`。
- 本轮没有另一条 cargo 或 lake 在使用这个 checkout。
- 证据留在 `.audit/verify-classifier/`。cleanup 不删除它。

## Driving conventions

- profile 用 `drive.py --gate profile`。
- 形式化用 `drive.py --gate formal`。
- Rust 测试用 `drive.py --gate rust`。
- 不跑 `npm test`，不跑 `smoke.py`，不把 `classifier test` 的 CLI 输出当作这三类的证明。

## Proof and skip reporting

- 证据目录里要有命令、stdout、stderr 和退出码。
- profile 通过意味着每个 `[[program]]` 都有 `ok pass`。
- 形式化通过意味着 `Verification` 构建成功，且技能 Evidence 列出的定理没有 `sorryAx`。
- Rust 通过意味着每个测试二进制都是 `test result: ok`。
- 入口没跑到时记下命令和未满足的前提。不要用另一个 gate 代替。

## Feature entry contract

每个 feature 文件按固定的四个 H2：`Sub-features`、`How to get to it (user POV)`、`Driving it with verify-classifier`、`Gotchas`。

## Features

- [Profile integration](./profile-integration.md) 核对 `profile.toml` 声明的全部 ELF 和 bpf，以及 strict、weak、fail 预期。
- [Formal relations](./formal-relations.md) 构建已整理的关系命题，并确认证明不依赖 `sorryAx`。
- [Rust tests](./rust-tests.md) 跑库、二进制和其余集成测试里的功能单元。
