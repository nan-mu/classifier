# Branch谓词

## 类型定义

Branch谓词记录条件控制流在一条候选路径中选定的后继方向，以及选择该方向所需成立的比较条件。普通条件分支与循环中的条件分支均适用。术语统一为 `branch`；`for` 谓词名称废止。

比较条件的类型为：

\[
\mathrm{Cond}:=\bigsqcup_{w\in\{32,64\}}
\bigl(\mathrm{Term}_w\times\mathrm{Rel}_w\times\mathrm{Term}_w\bigr).
\]

其中 \(\bigsqcup\) 为保留位宽标签的不交并，\(\mathrm{Term}_w\) 为 \(w\) 位有限符号项集合，\(\mathrm{Rel}_w\) 为作用于两个 \(w\) 位值的比较关系符集合；三元组 \(c=(u,\bowtie,t)\) 的两端均为同位宽项。项与关系符的定义见 [Expr 的Term](../Expr/Term/Term.md#term)及[关系符定义](../Expr/Expr.md#关系符定义)。

关系符 \(\bowtie^{[q]}\) 保留比较宽度 \(q\)，其中 \(1\le q\le w\)，全宽比较可省略上标。无符号、有符号、相等及按位测试的解释沿用 Expr 的关系符，不能仅以机器寄存器宽度代替比较宽度。

给定指令序列 \(\mathbf I\)，Branch谓词的类型为：

\[
\mathrm{Branch}_{\mathbf I}:=
\mathrm{Pos}_{\mathbf I}\times
\{\mathrm{Taken},\mathrm{NotTaken}\}\times\mathrm{Cond}.
\]

其中 \(\mathrm{Pos}_{\mathbf I}\) 是[程序位置](../NodeInference/路径.md#程序位置)的合法域；\(j\in\mathrm{Pos}_{\mathbf I}\) 为从 1 开始的条件指令序号，对应 \(\mathbf I[j-1]\)。\(d\) 为方向，Taken 选择条件成立的跳转后继，NotTaken 选择条件不成立的顺序后继；位置与方向是结构标记，没有机器位宽。元素记作 \(\operatorname{branch}(j,d,c)\)，良构生成还要求该位置确为条件指令且 \(c\) 与 \(d\) 对应。Exit 是独立的正常结束标记，不属于这里的位置域。

\(\operatorname{branch}(j,d,c)\) 的三个分量及 \(c\) 的位宽、两端项和关系符均参与结构相等。相同三元组不携带额外的动态分支身份；其在有限集合中的重复累积按[结构并集](谓词定义.md#结构并集)去重。逐次发生及次序由历史路径记录。

\(c\) 需要上述项—关系符—项类型，而不能直接取裸 Expr。现有比较 Expr 的左端是当前寄存器标记，解释依赖当前寄存器赋值；其完整旧值项须从规则读取的 \(E_g\) 中取得。将该项固定为 \(c\) 的左端后，两端项均脱离后续寄存器覆写。例：比较时 \(r=a\) 且成立方向要求 \(r<_u C_{32}(10)\)，对应条件为 \((a,<_u,C_{32}(10))\)；之后将 \(r\) 赋为 20，不改变这个条件。

### 条件与谓词的解释

在固定的符号赋值 \(\nu\) 与未解释运算补全 \(\theta\) 下，条件解释为布尔事实：

\[
\llbracket (u,\bowtie,t)\rrbracket_{\nu,\theta}
:=\widehat{\bowtie}\bigl(\llbracket u\rrbracket_{\nu,\theta},
\llbracket t\rrbracket_{\nu,\theta}\bigr).
\]

其中 \(\llbracket u\rrbracket_{\nu,\theta}\)、\(\llbracket t\rrbracket_{\nu,\theta}\) 是同位宽项的值，\(\widehat{\bowtie}\) 是 Expr 关系符对应的全定义布尔函数，结果属于 \(\mathbb T=\{\mathsf{true},\mathsf{false}\}\)；\(\nu\) 与 \(\theta\) 的定义见 [Expr 的Term](../Expr/Term/Term.md#term)。

Branch谓词解释为其方向条件的真值：

\[
\llbracket\operatorname{branch}(j,d,c)\rrbracket_{\nu,\theta}
:=\llbracket c\rrbracket_{\nu,\theta}.
\]

其中 \(j\)、\(d\) 是控制流标记，\(c\) 是该方向要求成立的条件；一条具体执行满足该事实当且仅当右侧为 \(\mathsf{true}\)。未确定比较保留的两侧分别记录各自候选路径的选择，不断言同一具体执行同时选择两侧。单次解释取相同真值不足以证明两个条件在全部对应输入下语义等价。

## 触发逻辑

### RV32IMC

位置 \(j\) 的合法 `BEQ`、`BNE`、`BLT`、`BGE`、`BLTU`、`BGEU` 触发分支候选及Branch谓词构造。两源为 `rs1`、`rs2` 的完整 32 位旧值项，均取自同一 \(E_g\)；读取 `x0` 使用固定零项 \(C_{32}(0)\)。项位宽与比较宽度均为 32。

Taken 的关系符分别为：`BEQ` 对应 \(=\)，`BNE` 对应 \(\ne\)，`BLT` 对应 \(<_s\)，`BGE` 对应 \(\ge_s\)，`BLTU` 对应 \(<_u\)，`BGEU` 对应 \(\ge_u\)。NotTaken 使用相应补关系。

合法压缩分支 `C.BEQZ`、`C.BNEZ` 读取指定的 `x8` 至 `x15` 寄存器完整 32 位旧项，第二源为 \(C_{32}(0)\)。Taken 分别使用 \(=\)、\(\ne\)，NotTaken 使用补关系。分支目标采用已解码的合法有符号字节偏移及既定机器地址—位置绑定；顺序后继为下一指令位置。普通与压缩编码长度的差异由位置绑定处理。

比较后产生 0 或 1 的 `SLT`、`SLTU`、`SLTI`、`SLTIU` 是数值赋值，未选择条件控制流后继，不触发Branch谓词。无条件跳转、调用及正常返回分别使用各自规则。机器码依据为 [RV32I](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html)与 [C 扩展](https://docs.riscv.org/reference/isa/v20260120/unpriv/c-st-ext.html)。

### eBPF

位置 \(j\) 的合法 `JMP`、`JMP32` 条件跳转触发分支候选及Branch谓词构造。第一源为 `dst_reg` 指定寄存器的完整 64 位旧项；第二源为 `src_reg` 指定寄存器的完整 64 位旧项，或立即数模式 \(\iota\) 经符号扩展得到的项 \(C_{64}(M_{64}(s_{32}(\iota)))\)。寄存器源均取自同一 \(E_g\)，两端项的位宽为 64。

`JMP` 使用比较宽度 \(q=64\)，`JMP32` 使用 \(q=32\)。\(M_{64}\) 为模 \(2^{64}\) 归一化，\(s_{32}\) 为 32 位补码解释，\(C_{64}\) 构造 64 位常元；低位截取由 \(\mathrm{Rel}_{64}\) 中的 \([q]\) 完成，完整项保持 64 位，定义见 [Expr 的关系符](../Expr/Expr.md#关系符定义)。

Taken 的关系符对应如下，所有关系均带本指令的比较宽度 \([q]\)：

- `JEQ`、`JNE` 分别使用 \(=\)、\(\ne\)。
- `JLT`、`JLE`、`JGT`、`JGE` 分别使用 \(<_u\)、\(\le_u\)、\(>_u\)、\(\ge_u\)。
- `JSLT`、`JSLE`、`JSGT`、`JSGE` 分别使用 \(<_s\)、\(\le_s\)、\(>_s\)、\(\ge_s\)。
- `JSET` 使用 \(\mathrm{BITSNZ}\)，即两源低 \(q\) 位按位与的结果非零。

NotTaken 使用对应补关系；`JSET` 的补关系为 \(\mathrm{BITSZ}^{[q]}\)。目标采用既定的合法偏移与位置绑定，顺序后继采用下一指令位置。`JA`、`CALL`、`EXIT` 不属于条件跳转。`MAY_GOTO` 尚缺独立的完整局部语义，不据此生成Branch谓词。机器码依据为 [BPF ISA 的跳转指令](https://docs.kernel.org/bpf/standardization/instruction-set.html#jump-instructions)。

## 生成条件

\(E_g\) 是条件局部规则实际读取的有效 Expr 列表；\(\operatorname{bindings}(E_g)\) 提供唯一的完整源值绑定，\(\operatorname{constraints}(E_g)\) 是比较行，见 [Expr 表达式分量](../Expr/Expr.md#表达式分量)。\(P_g\) 是执行前的谓词列表，Branch谓词构造对它无成员前提。

固定当前架构的解码与取源规则。令 \(\lambda:\mathrm{Pos}_{\mathbf I}\times\{\mathrm{Taken},\mathrm{NotTaken}\}\rightharpoonup\mathrm{Pos}_{\mathbf I}\) 为该程序的条件后继位置绑定；\(\lambda(j,d)\) 在方向 \(d\) 的目标唯一有效时有定义，无定义表示该目标未取得合法绑定。

在合法解码、位置绑定及取源齐备的前提下，令 \(u\)、\(t\) 为从同一 \(E_g\) 取得并经 solve 折叠的两端项，\(r_a\) 为第一源寄存器，\(e=(r_a,\bowtie,t)\) 为本指令原条件的比较 Expr。\(\bowtie\) 取自[触发逻辑](#触发逻辑)中 Taken 对应的关系，\(\overline{\bowtie}\) 为它的补关系。固定零与立即数由对应架构规则构造，不要求额外源绑定。

每个方向固定自己的条件：

\[
c_d:=
\begin{cases}
(u,\bowtie,t),&d=\mathrm{Taken},\\
(u,\overline{\bowtie},t),&d=\mathrm{NotTaken}.
\end{cases}
\]

其中 \(d\in\{\mathrm{Taken},\mathrm{NotTaken}\}\)，\(c_d\in\mathrm{Cond}\) 保存执行前两源及选定方向的关系，\(u\)、\(t\) 的项位宽相同。

按 Expr 的[部分判定](../Expr/Expr.md#比较关系)选择保留方向：

\[
R(\mathbf I,j,E_g):=
\begin{cases}
\{\mathrm{Taken}\},&\operatorname{decide}(e,u)=\mathsf{true},\\
\{\mathrm{NotTaken}\},&\operatorname{decide}(e,u)=\mathsf{false},\\
\{\mathrm{Taken},\mathrm{NotTaken}\},&\operatorname{decide}(e,u)=\bot.
\end{cases}
\]

其中 \(R\) 是本次条件指令保留的方向集合，\(\operatorname{decide}\) 使用旧左源项 \(u\) 判定 \(e\)，\(\bot\) 表示源项齐备但数值判定未知；\(e\)、\(u\) 均由参数 \((\mathbf I,j,E_g)\) 按上述取源规则确定。此规则不求解 \(\operatorname{constraints}(E_g)\) 或 \(P_g\) 的累积可满足性。

所有保留方向的目标均绑定成功时，合法局部分支候选集合为：

\[
K(\mathbf I,j,E_g,\lambda):=
\{(d,\lambda(j,d),c_d):d\in R(\mathbf I,j,E_g)\}.
\]

其中 \(K\in\mathscr F(\{\mathrm{Taken},\mathrm{NotTaken}\}\times\mathrm{Pos}_{\mathbf I}\times\mathrm{Cond})\)，\(\mathscr F\) 表示有限子集集合；\(j'_d=\lambda(j,d)\) 为方向 \(d\) 的已绑定后继指令位置，\(c_d\) 为同一 \(E_g\) 固定的条件。\(K\) 是后继状态组合之前的局部候选，不包含已组合的后继状态。若一个保留目标无定义，\(K\) 无定义，不返回其余候选的部分集合。

对每个 \((d,j'_d,c_d)\in K(\mathbf I,j,E_g,\lambda)\)，生成唯一Branch谓词：

\[
\operatorname{makeBranchPredicate}(\mathbf I,j,E_g,\lambda,d)
:=\operatorname{branch}(j,d,c_d).
\]

其中 \(\operatorname{makeBranchPredicate}\) 为部分构造，输入包含指令序列、当前条件指令位置、局部规则读取的 Expr 关系、条件后继位置绑定 \(\lambda\) 及保留方向；\(j\) 记录产生事实的条件位置，\(j'_d\) 仅用于候选的后继位置，不替代 \(j\)。该构造只在 \(K\) 有定义且 \(d\) 为其方向时有定义。

该候选的 \(P_{i,d}\) 为：

\[
P_{i,d}:=
\{\operatorname{makeBranchPredicate}(\mathbf I,j,E_g,\lambda,d)\}.
\]

其中 \(P_{i,d}\in\mathscr F(\mathrm{Branch}_{\mathbf I})\) 是方向 \(d\) 的单元素增量；step 按[结构并集](谓词定义.md#结构并集)将其与同一父状态的 \(P_g\) 组合。后继状态准备见 [step](../NodeInference/step.md#状态变换的组合)。两个候选分别携带各自的增量，不将两侧谓词同时加入一个后继。

### 错误类型

已进入条件分支处理的步骤在下列情形下构造无定义，拒绝整个步骤，不提交部分候选：

- \(j\) 不属于合法程序位置，当前位置指令不是所选规则覆盖的条件指令，或解码参数、比较宽度、寄存器编号非法。
- 局部规则读取的 \(E_g\) 无效；所需完整源值绑定缺失、不唯一或位宽不符。仅有比较约束或低位等式不能补足完整源项。
- 一个保留方向的目标缺少唯一位置绑定，或顺序方向已越过指令序列末尾。
- 请求方向不属于 \(K\)，或请求的条件不等于该候选由旧源与对应关系构成的 \(c_d\)。

源项齐备但数值求值未知时保留两侧，属于成功候选生成；未知不作为假或无定义。已由本次确定比较排除的方向无需目标绑定。无成功规则与绑定失败均不充当不可行性证明，拒绝行为见 [step 的规则定义域](../NodeInference/step.md#局部规则的合法域)。

## 数学性质

**命题 B1（候选生成唯一性）。** 固定 \(\mathbf I\)、\(j\)、有效 \(E_g\) 及条件后继位置绑定 \(\lambda\)，若 \(K(\mathbf I,j,E_g,\lambda)\) 有定义，则每个保留方向恰有一个Branch谓词，每个候选的局部增量恰有一个元素。

**证明。** 合法指令确定关系符与比较宽度。完整源值绑定唯一，固定零与立即数构造确定，solve 是确定函数，故 \(u\)、\(t\) 唯一。每个方向的补关系及目标绑定唯一，因而 \(c_d\) 与三元组谓词唯一。单元素增量的定义给出最后结论。\(\square\)

**命题 B2（同次条件互补）。** 对从同一 \(E_g\) 取得的 \(u\)、\(t\)，在固定 \((\nu,\theta)\) 下，Taken 条件与 NotTaken 条件恰有一个为真。

**证明。** 两端项在固定解释下得到确定的同位宽值。Expr 的补关系将原关系的真值映为布尔否定，因此两条件分别取 \(\beta\)、\(\neg\beta\)，恰有一个为真。\(\square\)

**命题 B3（旧源保持）。** 固定已生成的 \(p=\operatorname{branch}(j,d,c_d)\) 及 \((\nu,\theta)\)。后续 Expr 更新只要不修改已构造的项，则不改变 \(p\) 的结构或解释。

**证明。** \(c_d\) 已包含构造时取得的两端有限项与关系符，其解释不读取当前寄存器赋值。更新寄存器绑定不修改这些项；位置与方向也固定，故结构及解释均保持。\(\square\)

### 跨架构条件比较

同程序 Branch 保留条件位置、方向和完整条件。跨侧比较将已固定的两端项送入[条件规范化](跨架构谓词.md#条件分类)，包结束资源来自各侧入口单元 1 的绑定。M2 的载体与包裹、M3 的关系对偶与比较宽度、M4 的位置擦除分别由[对应规范规则与证据](跨架构谓词.md#不匹配类别的处理)维护。方向继续参与规范分支相等。

`packetField` 保留组装字段项，故 ethertype 条件的统一还依赖相同字节来源及组装解释；`packetBound` 使用调用方给出的结束资源对应。一般宽度、组装代数与地址重结合的证明义务见[跨架构待证明义务](跨架构谓词.md#待证明义务)。

### 待证明义务

- **机器指令对应。** 证明两架构的取源、立即数扩展、比较宽度、关系符及目标绑定与实际条件指令语义对应；B1 至 B3 是定义层面的结论，不提供该对应证明。
- **保留方向的可靠性与覆盖性。** 证明部分判定给出确定真假时排除方向可靠，未知时保留两侧覆盖所有可能执行，并证明每个满足方向条件的执行与相应后继状态组合一致。
- **历史与合并保持。** 证明记录Branch谓词的历史解释保留逐次条件检查及控制流次序，并证明路径合并不会丢失所需分支事实。重复同结构谓词由集合去重，因而分支次数与次序的保持须依赖历史表示另行论证。

## 相关文档

- [Expr 的比较关系](../Expr/Expr.md#比较关系)：比较 Expr 的当前左值、部分判定与补关系。
- [Expr 的关系符与符号项](../Expr/Expr.md#关系符定义)：比较位宽、符号性与按位测试；[Term](../Expr/Term/Term.md#term)维护项及解释补全。
- [Expr 的列表与值绑定](../Expr/Expr.md#表达式分量)：局部规则读取的源值与比较行的区分。
- [Expr 的 solve 化简与求值](../Expr/Term/solve.md#solve-的化简与求值)：solve、部分数值求值及未知结果。
- [谓词定义](谓词定义.md)：结构相等、有限集合累积与历史顺序。
- [Helper 各类谓词](Helper谓词.md#类型定义)：外部调用观察。
- [程序位置与执行路径](../NodeInference/路径.md)：1-based 位置、方向与历史路径。
- [step](../NodeInference/step.md)：局部规则读态、候选目标校验与后继状态组合。
