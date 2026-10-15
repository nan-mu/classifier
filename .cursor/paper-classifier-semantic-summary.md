# 分类器跨架构谓词路径：论文可用摘要（草稿）

> 供作者改写进论文正文/附录。主张分级以仓库文档与 Lean 为准；`fail=0` 是产品测量，不是行为等价证明。
> Cursor 起草于 just_tx 绿测之后；omp 形式化普查完成后应以 `doc/` 普查表为准修订本草稿。

## 一句话

我们把同一 XDP 程序在 RV32IMC 与原生 eBPF 上展开得到的**局部观察列表**，经可机检的载体擦除与合一，变成可比较的规范键；在 `just_tx` 上测量到比较树节点全部 `matchStatus=pass`，但**尚未**建立两端执行的行为等价。

## 问题与方法（Explanation）

MCU 上跑经 eBPF verifier 约束过的策略时，需要回答：两端编译器发出的控制与存储观察，是否在去掉 ABI/位宽噪声后仍指同一类事件。分类器不做指令级模拟对齐，而做**谓词层**对齐。

1. 各侧 expand 产生五类观察：`helper`、`branch`、`ret`、`mapWrite`、`packetWrite`。
2. 按局部增量 \(P_i\)（相对父节点的新到达）进入比较树节点。
3. Lean `toCross` / `lean_cross_pred_normalize` 得到规范观察键；`lean_cross_pred_unify` 在保序最大对齐下做带单射重命名的列表合一。
4. Host 负责树臂极性、写入跑偏序、边方向上的 `dir`、以及逐观察的 `storeBytes`；VLAN 两个 TPID 析取臂在常量不同但字段树相同且关系相同的单例分支上，仅作 `matchStatus` 合同性回退（规范键仍区分两常元）。

报告字段固定 `claim: crossPred`，`behavioralEquivalence: notEstablished`。

## 语义一致目前停在哪一层（主张分级）

| 层级 | 内容 | 状态（据现有 doc/Lean） |
|---|---|---|
| A. 结构比较 | 节点/边覆盖的 `sameStructure` | 有定义与有限检查；**不**蕴涵行为等价 |
| B. 规范键相等 | 擦除载体、`zext`/`sext` 切片、ABI 尾、加法次序、Map 进位形状等后的观察相等 | 多项 **Lean 结构定理** + 大量 `#guard`；解释保持多属 **CP-*** 义务 |
| C. 列表合一 | 局部增量上的保序对齐与寄存器 alpha 重命名 | 实现与有限 fixture；搜索/对称/歧义等 **义务仍开** |
| D. 产品测量 | 双架构 `just_tx`、budget 1024、比较树 89 节点 | **实测 fail=0**（测量，非证明） |
| E. 行为等价 | 两端对任意包的可观察结果相同 | **未建立** |
| F. 架构无关 | 换非 RISC-V 目标后同样结论 | **研究假设**；单实例不足以作实证结论 |

对论文最稳妥的表述是：我们证明了（或机检了）**规范观察键构造的一批结构性质**，并在标准样例上展示**跨 ISA 观察对齐的工程闭合**；行为等价与跨架构一般化仍是开放义务。

## 已机检的典型结果（宜进附录）

- 二元加法规范次序无关：`cross_term_add_comm`（结构等式；模加法解释仍归 CP-Add）。
- 关系对偶与交换：`cross_rel_dual` 及若干 `rel_*_swap`。
- 返回小正整数跨 32/64 载体：`cross_return_small`（\(n<2^{31}\)）。
- 分支位置不进入规范键：`cross_branch_position`。
- Map 双字写：生成侧拆成偏移 0/4；R5/R6 将低半覆盖切片与高半进位链收到同一规范键形状（前提归 CP-Q/CP-Bytes）。
- VLAN：`liveNode3EthertypeDistinct` 固定两 TPID **不得**在 `toCross` 中合并；host 合同性只影响 `matchStatus`。

## 仍须写进“局限”的义务（摘）

CP-Add（解释）、CP-Q、CP-Quotient、CP-ABI、CP-Reg、CP-Bytes、CP-End、CP-Unify-Order / Search / Symmetry / Amb。完整列表见 `doc/Predicate/跨架构谓词.md` 待证明义务。

## 可直接改写的英文短段落（草案）

We compare RV32IMC and native eBPF expansions of the same XDP program at the level of local observation lists (helper, branch, ret, map and packet writes). A Lean normalization erases ABI and width noise and yields canonical observation keys; an order-preserving unifier matches the lists under injective register renaming. On the `just_tx` product path the dual compare tree reports all nodes as matched, but the pipeline explicitly does not establish behavioral equivalence. Several structural lemmas about the normalizer are machine-checked; semantic obligations that connect erased carriers, freeze bytes, and control-order correspondence remain open.

## 与 omp 普查的衔接（已落地）

正式表与可粘贴附录见 `doc/NodeInference/跨架构比较.md` 的「形式化证据普查」与「论文附录用形式化范围」。
普查划分（omp 实测）：约 20 行已证明 · 5 有限固定 · 1 产品实测 · 1 host 合同性 · 12 未决义务。
合一实现与文档关系 \(\mathcal{A}\) 的显式定义域闭包尚有一处算子决策缺口（identity collision）；不影响 just_tx 绿测表述，但附录宜一句带过。
