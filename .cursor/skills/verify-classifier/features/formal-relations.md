# Formal relations

`Verification` 库里已经整理的关系命题要能构建，并且列出的定理不依赖 `sorryAx`。这是语义对应的形式化门，不是某一次展开的测量。

## Sub-features

- `verification-build` 构建 `lean_lib Verification`。
- `axiom-audit` 核对技能 Evidence 中列出的定理，其 axiom 列表没有 `sorryAx`。

## How to get to it (user POV)

- 在 classifier 仓库运行 `python3 .cursor/skills/verify-classifier/scripts/drive.py --gate formal`。
- 这条命令执行 `lake build Verification`。

## Driving it with verify-classifier

Preconditions:

- doctor 的最后一行是 `doctor ok`。
- 本轮没有另一条 lake 在写这个仓库的 `.lake`。

- **构建。** 运行 `python3 .cursor/skills/verify-classifier/scripts/drive.py --gate formal`。脚本打印 `.audit/verify-classifier/<stamp>-formal/`。
- **证明。** `exit_code.txt` 是 `0`。stdout 和 stderr 里，技能 Evidence 列出的每个定理都有 axiom 输出，并且这些输出里没有 `sorryAx`。缺一个定理名就是失败。

## Gotchas

- `lake build VerificationGaps` 会构建仍带 `sorry` 的义务。它成功不代表这些关系已经证明。
- `Verification/Unverified` 下的 `sorry` 是未完成义务。不要把它们移进 `Verification.Verified`，也不要删掉 `sorry` 来让构建变绿。
- `#print axioms` 在 `Verification/Verified.lean`。证据里若没有这段输出，不能把退出码单独当成 axiom 审计通过。
- 这条门不建立 RV32 与 eBPF 的行为等价。`behavioralEquivalence` 仍是 `notEstablished`。
