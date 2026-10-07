# 谓词等价目标与 QF_BV 后端

## 两类不同的结论

Pathgen 的功能正确性与跨 ISA 谓词等价不是同一个命题。

- `rocq/theories/pathgen/Functional.v` 证明 Pathgen 保留来源机器码、生成的
  path code 以 `0` 开头，以及局部 `IfGoto -> Assert` 改写保留指令身份。
- `rocq/theories/pathgen/PredicateEquiv.v` 表达由 `Assert` 选定的行为等价。
  它不声称两套机器的全部状态、全部副作用或完整 trace 等价。

令一条路径的全部 assert 合取为 `Phi_p(v)`，共享输入与环境约束为 `C(v)`。
基础的左右路径不等价反例目标是：

```text
C(v) AND (Phi_left(v) XOR Phi_right(v))
```

该目标为 `UNSAT` 时，才得到这对路径在契约下的 assert 行为相等。Path code
只是 Pathgen 的遍历/Huffman 标识，不是语义标识；BPF 与 RV32 的分支顺序可能
不同，不能按同名文件配对。

当前 XDP 查询还比较证明 assert 所依赖的 MapLookup map/key 中间观察量 `O`：

```text
C(v) AND ((Phi_left(v) XOR Phi_right(v)) OR (O_left(v) != O_right(v)))
```

这是基础反例公式的加强，而不是改变最终观察量。Rocq 定理
`no_strengthened_counterexample_implies_path_assert_equiv` 证明加强公式无反例仍然
推出原来的 assertion-only 等价。

路径族结论使用显式双射 `M`：左右每条路径恰好各出现一次，且 `M` 中每一对
的反例目标均为 `UNSAT`。Rocq 定理
`no_counterexample_matching_implies_family_equiv` 证明这些前提推出双向的
path-family assert 行为覆盖。

## 已实现的 Rust 链路

- `src/qfbv/ast.rs`：typed BV/Bool AST；位宽限定为 1--64，构造时拒绝位宽错误。
- `src/qfbv/goal.rs`：通用的寄存器/assert 符号执行器；未知效果失败即停。
- `src/qfbv/xdp.rs`：当前 XDP fixture 使用的逻辑区域语义。
- `src/qfbv/smtlib.rs`：确定性 SMT-LIB2 序列化；稳定声明顺序，每个文件只有
  一个 `assert` 和一个 `check-sat`。
- `src/qfbv/family.rs`：穷举候选边、构造完美匹配、用权威后端重验匹配边，
  并输出 manifest 和最终查询。
- `src/qfbv.rs`：文件级求解器驱动；只接受成功进程输出中的唯一一行
  `sat` 或 `unsat`。

通用执行器支持寄存器 `Set`、模算术、位运算、带掩码移位、signed/unsigned
比较、RV32 `slt[u]`/高位乘法、BPF `wN`/`rN` 别名和 RV32 `w0`。内存、
helper、trap、残余 `IfGoto`，以及尚未固定边界语义的除法/余数，都会返回带
path code、instruction index、Predicate ID 的 `Unsupported`，不会用自由变量
悄悄替代。

XDP 执行器额外提供受限的逻辑区域：

- BPF `r1` 与 RV 环境指定寄存器指向同一个逻辑 context；
- context `+0/+4` 分别产生共享的 packet base/end；
- 每个反例目标都显式加入 `data <= data_end`、`data <= data_max` 与 packet
  alignment 契约，以排除32位地址回绕；
- packet/map 字节使用两边共享的定宽输入变量；
- 两边的物理栈、入口寄存器和 context/stack 地址保持私有；
- 只有能在符号状态中归类为 packet/map/stack 的 load/store 才能执行；
- 当前单-map范围内，BPF helper 1 的零 relocation 占位、RV map handle/selector、
  两边私有栈上的已初始化 key 槽都会在调用点检查；通过后，两边按调用序号共享
  MapLookup 结果。

查询会直接证明两个 key 值和逻辑 map ID 一致；剩余的显式环境假设是BPF
relocation实际解析到配置map，以及两边helper实现服从同一MapLookup契约。
最终 packet/map 写入和返回值还不是本命题的观察量；它们只在影响后续 assert
时参与符号执行。

## 发现与认证严格分离

可选快速 oracle 只用于发现候选配对：

```text
所有 left/right 组合
  -> oracle 对反例目标判定 SAT/UNSAT
  -> 只把 UNSAT 候选作为二分图边
  -> 求完美匹配
  -> standalone CoqQFBV 逐条重验匹配边
  -> 全部为 UNSAT 后才输出路径族 evidence
```

oracle 的 `UNSAT` 本身没有证明效力。权威阶段任一查询返回 `SAT`、无状态行、
多个状态行、非零退出或进程错误，整个路径族检查立即失败，不返回部分证明。

单文件调用：

```bash
cargo run -- qfbv query.smt2
cargo run -- qfbv query.smt2 --solver /path/to/coqQFBV.exe
```

真实 fixture 的路径族调用：

```bash
cargo run -- xdp-assert-equiv \
  --oracle z3 \
  --solver /path/to/coqQFBV.exe \
  --output out/qfbv/xdp-assert-equiv
```

不指定 `--oracle` 时，权威后端也负责候选发现，因此会检查所有路径组合。

## 可复核产物

成功后输出：

```text
out/qfbv/xdp-assert-equiv/
  manifest.txt
  inputs/bpf/{prefixgen,pathgen}/...
  inputs/rv32imc/{prefixgen,pathgen}/...
  queries/match-....smt2
```

manifest 记录左右路径数、候选检查数、候选 UNSAT 边数、发现/验证后端，以及
每个左右 path code 到最终查询文件的映射。只有最终双射中的查询需要承担结论；
候选发现结果不属于证明前提。输入子目录保留原机器码列与结构化 Prefix，供
查询中的 instruction/Predicate 来源回溯。开始一次运行时 manifest 先被标记为
`status=incomplete`；只有全部重验和文件写入成功后才改为 `status=complete`。

## 可信边界与尚未完成的链路

当前结论应准确表述为“在给定逻辑输入/环境假设下，两组结构化 Prefix path 的
selected-assert 行为族等价”，不能表述为完整机器码语义或物理世界 trace 等价。

仍在可信计算基或待证明的部分是：

- Rust `Prefix -> typed QF_BV -> SMT-LIB2` 翻译器；
- Prefix 对原机器指令语义的完备/可靠标注，目前 Rocq 只证明机器字段保留和
  已实现 decode/pathgen 的结构性质；
- ELF 提取、RV 指令切分和显式 `Environment` 契约；
- helper/map relocation 的跨 ISA 对应假设；
- standalone CoqQFBV 可执行文件及其已验证 checker 的正确构建与运行环境。

Rocq 不启动求解器，也不把字符串 `unsat` 声明成公理。它只给出命题与组合定理；
Rust 负责生成和归档可由外部认证工具独立复验的具体 QF_BV 文件。
