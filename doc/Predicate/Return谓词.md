# Return谓词

## 类型定义

Return谓词记录最外层正常结束的返回结果，使返回值进入统一的 Predicate 语义。其类型为：

\[
\mathrm{Return}
:=\bigsqcup_{w\in\{32,64\}}
\{\operatorname{return}(t):t\in\mathrm{Term}_w\}.
\]

其中 \(\bigsqcup\) 为保留位宽标签的不交并，\(w\) 为返回项的位宽，\(\mathrm{Term}_w\) 为 \(w\) 位有限符号项集合，\(\operatorname{return}(t)\) 为保存完整返回项 \(t\) 的构造。项的构造与位宽见 [Expr Term](../Expr/Term/Term.md#term)。

Return谓词结构相等，当且仅当返回项的位宽与项结构分别相同。运算符、参数与变元身份参与项结构比较。

令架构参数 \(A\in\{\mathrm{RV32IMC},\mathrm{eBPF}\}\)。返回寄存器由架构及其返回约定确定：

\[
r_{\mathrm{ret}}(A):=
\begin{cases}
a_0,&A=\mathrm{RV32IMC},\\
r_0,&A=\mathrm{eBPF}.
\end{cases}
\]

其中 \(r_{\mathrm{ret}}\) 将架构映到其真实返回寄存器，\(a_0=\mathrm{Real}_{32}(10)\) 为 RV32 的 32 位返回寄存器，\(r_0=\mathrm{Real}_{64}(0)\) 为 eBPF 的 64 位返回寄存器；\(\mathrm{Real}_w(k)\) 是编号为 \(k\) 的 \(w\) 位真实寄存器标记，身份见[寄存器定义](../寄存器定义.md#架构中的真实寄存器标识)。

\[
w_{\mathrm{ret}}(A):=
\begin{cases}
32,&A=\mathrm{RV32IMC},\\
64,&A=\mathrm{eBPF}.
\end{cases}
\]

其中 \(w_{\mathrm{ret}}\) 将架构映到返回寄存器的完整位宽，与 \(r_{\mathrm{ret}}(A)\) 的项位宽一致。

### 返回结果的解释

\[
\left[\!\left[\operatorname{return}(t)\right]\!\right]_{\nu,\theta}
:=\bigl(\mathsf{return},w,\left[\!\left[t\right]\!\right]_{\nu,\theta}\bigr).
\]

其中 \(t\in\mathrm{Term}_w\)，\(\mathsf{return}\) 为正常返回观察的类别标签，\(\nu\) 为将各位宽变元映到对应位向量集合 \(\mathbb B_w\) 的赋值族，\(\theta\) 为按运算签名提供值函数的解释补全；项解释 \(\left[\!\left[t\right]\!\right]_{\nu,\theta}\in\mathbb B_w\) 见 [Expr 项的解释](../Expr/Term/Term.md#项的解释)。观察保留返回值及其位宽。

## 触发逻辑

触发输入为当前指令及已识别的最外层正常返回，见[后继位置绑定](../NodeInference/step.md#绑定后继位置)。只有已经识别为最外层正常返回的步骤进入 Return谓词生成。普通指令位置从 1 开始，\(\mathbf I[j-1]\) 为位置 \(j\) 的指令；Exit 是独立的正常返回后继，位置定义见[路径](../NodeInference/路径.md#指令序列与程序位置)。

### RV32IMC

RV32 的返回通常通过 `JALR x0, 0(x1)`，或压缩形式 `C.JR x1` 实现。处理间接转移时，按既定源项与目标绑定规则取得目标；只有该目标已被识别为既定最外层正常返回位置时，才触发 Return谓词构造。指令形态本身不足以确定返回的层次。

满足该识别后，从当前 \(E_g\) 读取 32 位 \(a_0\) 的完整返回项，按[生成条件](#生成条件)产生谓词。目标计算所需的源项与返回项分别接受各自的完整性检查。

### eBPF

eBPF 的 `EXIT` 指令在已识别为最外层程序正常返回时，触发 Return谓词构造。程序内子函数的 `EXIT` 按调用返回配对继续执行程序内的后续指令，其处理边界见[错误类型](#错误类型)。

满足最外层识别后，从当前 \(E_g\) 读取 64 位 \(r_0\) 的完整返回项，按[生成条件](#生成条件)产生谓词；32 位低位视图不能替代该完整项。

## 生成条件

\(E_g=(\mathcal V_g,\mathcal C_g)\) 为当前返回指令执行前的有效 [Expr 关系](../Expr/Expr.md#表达式分量)，\(\mathcal V_g\) 为有限完整值绑定集合，\(\mathcal C_g\) 为有限比较关系集合；\(P_g\) 为执行前的有限谓词集合。完整返回值取自 \(\mathcal V_g\)，不从 \(\mathcal C_g\) 的比较约束补出。

令 \(b\in\{\mathrm{true},\mathrm{false}\}\) 表示本次返回指令是否已被判定为最外层正常返回。构造的输入是架构 \(A\)、该识别结果 \(b\) 及当前关系 \(E_g\)。其定义域要求 \(b=\mathrm{true}\)、\(E_g\) 有效，并且存在唯一的完整等式：

\[
\bigl(r_{\mathrm{ret}}(A)=t\bigr)\in\mathcal V_g,
\qquad t\in\mathrm{Term}_{w_{\mathrm{ret}}(A)}.
\]

其中 \(r_{\mathrm{ret}}(A)\) 为架构返回寄存器，\(w_{\mathrm{ret}}(A)\) 为其完整位宽，\(t\) 为该完整等式唯一的右侧项。唯一性按真实寄存器完整绑定的键检查。

返回项可以含变元或未解释运算，不要求其数值可求。谓词直接保存所取得的完整项；构造对 \(P_g\) 无成员前提。从当前 \(E_g\) 取得的项与正常返回后继及实际返回结果的一致性列为[证明义务](#证明义务)。

\[
\operatorname{makeReturnPredicate}(A,b,E_g)
:=\operatorname{return}(t).
\]

其中 \(\operatorname{makeReturnPredicate}\) 为上述定义域上的部分构造，\(t\) 为从输入 \(E_g\) 唯一取得的完整返回项；成功结果属于 \(\mathrm{Return}\)。

\[
P_i:=\{\operatorname{return}(t)\}.
\]

其中 \(P_i\in\mathscr F(\mathrm{Return})\) 为该正常返回步骤的谓词分量，\(\mathscr F\) 为有限子集族，\(t\) 为成功构造取得的项。其加入 \(P_g\) 的累积规则见[结构并集](谓词定义.md#结构并集)。

### 错误类型

以下情形均不生成 Return谓词；处理失败时不得伪造返回值：

- 程序内部函数返回：未满足最外层触发条件，按既定调用返回配对继续内部后继。
- 未解析的间接跳转：最外层正常返回尚未识别，采用[既有拒绝处理](../NodeInference/step.md#失败情形)。
- 推理失败：不以拒绝结果代替正常返回，采用[step 输出](../NodeInference/step.md#两种结果)。
- 已识别最外层正常返回，但 \(E_g\) 无效，返回寄存器完整等式缺失或不唯一，或项位宽非法：构造无定义，拒绝整个步骤，不返回部分候选。只有低位关系、不等式或比较分量中的同名等式，均不满足完整返回值条件。

## 数学性质

**命题 R1（生成唯一性与位宽）。** 对固定的 \(A\)、\(b=\mathrm{true}\) 及满足生成条件的 \(E_g\)，成功生成的 Return谓词唯一，所含项的位宽为 \(w_{\mathrm{ret}}(A)\)。

**证明。** 架构确定返回寄存器及位宽。生成条件要求该寄存器的完整绑定唯一，故右侧项 \(t\) 唯一；\(\operatorname{return}\) 构造确定，且只接受规定完整位宽的项。\(\square\)

**命题 R2（保存完整返回项的解释）。** 在 R1 的前提下，固定适配该项的赋值与解释补全 \((\nu,\theta)\)，生成谓词的值分量等于所取得的完整返回项的解释。

**证明。** 构造保存完整等式的右侧项 \(t\)。按[返回结果的解释](#返回结果的解释)，谓词的值分量正是 \(\left[\!\left[t\right]\!\right]_{\nu,\theta}\)，没有截断或扩展步骤。\(\square\)

### 跨架构返回比较

正常返回取源仍保留本架构完整项。M1 的跨侧比较使用[仅含 payload 的 CrossReturn](跨架构谓词.md#条件与各类观察)，其常元代表与严格共同范围由[返回常元命题](跨架构谓词.md#返回常元的共同范围)维护。该命题与返回 `1` 的有限实例分别提供一般结构等式和特定动作码检查；符号 payload 的机器解释需要[跨架构宽度与对应义务](跨架构谓词.md#待证明义务)。

### 证明义务

1. **最外层正常返回判定的可靠性。** 证明该判定确实对应最外层正常返回，并区分内部返回与未解析目标，使 RV32 返回地址及 eBPF 调用返回配对满足各自执行语义。
2. **源项与正常返回后继的一致性。** 证明完整绑定的取源正确、返回步骤保留相应返回寄存器，且从当前 \(E_g\) 取得的项解释等于正常返回后继及实际执行的返回结果。R1、R2 只证明给定绑定下的构造性质。

## 相关文档

- [统一谓词类型与结构相等](谓词定义.md#类型与结构相等)
- [Expr 完整值绑定与比较分量](../Expr/Expr.md#表达式分量)
- [Expr 项解释](../Expr/Term/Term.md#项的解释)
- [后继位置绑定](../NodeInference/step.md#绑定后继位置)
- [后继状态准备](../NodeInference/step.md#准备全部后继状态)
- [正常返回历史](../NodeInference/step.md#正常返回历史)
