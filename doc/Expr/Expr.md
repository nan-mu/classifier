# Expression

## 索引

- [表达式定义](#表达式定义)：表达式定义、比较运算符定义。
- [比较关系](#比较关系)：比较关系。
- [关系集合更新](#关系集合按键覆写)：关系集合按键覆写、多目标更新与同一来源。
- [指令结果](#指令结果的前提)：指令结果的前提、局部值效果的类型与解释保持。
- [未记录虚拟寄存器的取源](#未记录虚拟寄存器的取源)：未记录虚拟寄存器的取源。
- [资源读取与位置赋值](寄存器/资源读取与位置赋值.md)：资源读取与位置赋值。
- [单元字段读写](寄存器/单元字段读写.md)：Stack、Map 与 Context 的规范单元字段读写。
- [原子数值更新与旧值返回](寄存器/原子数值更新与旧值返回.md)：顺序 RMW、旧值返回，以及两个 SW32 与原 Map64 字段的[规范单元桥接](寄存器/原子数值更新与旧值返回.md#规范单元桥接)。
- [Helper 生成的 Expression](../Predicate/Helper谓词.md#生成的-expression)：辅助调用的返回赋值与 Map 关联。
- [Term/Term](Term/Term.md)：Term。
- [Term/solve](Term/solve.md)：整项闭项折叠与 R2 至 R6 规范化；解释保持要求[完整外部补全](Term/Term.md#未解释运算的解释补全)。
- [寄存器/真实寄存器](寄存器/真实寄存器.md)：真实寄存器赋值、真实寄存器低位视图与写回、常元赋值、移动与符号扩展赋值、算术与位运算赋值、乘法高半赋值、除法与余数赋值、字节序转换赋值、跳转链接值赋值。
- [寄存器/虚拟栈](寄存器/虚拟栈.md)：虚拟栈读写。
- [寄存器/虚拟映射](寄存器/虚拟映射.md)：虚拟映射读写。
- [寄存器/包字节](寄存器/包字节.md)：包字节读写。
- [Term/位向量](Term/位向量.md)：记号与位向量。
- [Term/数值函数](Term/数值函数.md)：共同数值函数。
- [工程模块与迁移](../NodeInference/路径合并FFI.md#工程模块与迁移)：表达式实现的 Core 归属，以及与 Node、RV32、EBPF 的依赖分工；跨架构研究与证明限度见[语义范围与证据边界](../NodeInference/路径合并FFI.md#语义范围与证据边界)。

## 表达式定义

位宽集合 \(W\) 与寄存器集合 \(\mathrm{Reg}_w\) 见[寄存器定义](../寄存器定义.md)。\(\mathrm{op}_w\) 是[比较运算符](#比较运算符定义)集合，\(\mathrm{Term}_w\) 是[Term](Term/Term.md#term)项集合。
\[
\boxed{
\mathrm{Expression}=\bigsqcup_{w\in W}
\bigl(\mathrm{Reg}_w\times\mathrm{op}_w\times\mathrm{Term}_w\bigr).
}
\]
\(E=(r_w,\mathbin{\mathrm{op}},t_w)\) 表示关系 \(r_w\mathbin{\mathrm{op}} t_w\)。完整值绑定与比较约束的角色由列表顺序推导，不单独存成两个集合。比较仅使用 Expression。

### 左值

左值指定关系所描述的寄存器对象；对象的完整定义见[寄存器定义](../寄存器定义.md)。

#### 左值的类型

对位宽 \(w\in\{32,64\}\)，Expression 的左值是 \(r_w\in\mathrm{Reg}_w\)。左值与右值必须同位宽。

Real、Stack、Map、Context、Packet 均可作为左值；对象身份与相等见[寄存器定义](../寄存器定义.md)。

#### 左值与写入对象

完整等式 \(r_w=t_w\) 可以给出对象的完整值；局部等式见[低位约束不确定完整值](#低位约束不确定完整值)。

LOAD 与普通 STORE 的栈左值选择见[虚拟栈读写](寄存器/虚拟栈.md#虚拟栈读写)。
LOAD 与普通 STORE 的 Map 左值选择见[虚拟映射读写](寄存器/虚拟映射.md#虚拟映射读写)。
LOAD 与普通 STORE 的 Context 左值由[上下文字段绑定](../NodeInference/create.md#上下文六槽关系)确定，读写采用[单元字段读写](寄存器/单元字段读写.md#单元字段读写)。
LOAD 与普通 STORE 的包左值选择见[包字节读写](寄存器/包字节.md#包字节读写)。
访问对象见[指令结果的前提](#指令结果的前提)。

别名标记与访问宽度下的规范单元划分见[寄存器定义](../寄存器定义.md)。

值绑定与比较约束的更新规则见[关系集合按键覆写](#关系集合按键覆写)。

### 表达式分量

语义状态的表达式分量为有限列表 \(\bar{E}\in\mathrm{List}(\mathrm{Expression})\)，形状与观察分量 \(\mathrm{List}(\mathrm{Observation})\) 相同。每一行是 \((r_w,\mathbin{\mathrm{op}},t_w)\)。列表按结构相等去重；角色不另存字段。

对每个寄存器，列表中**第一条**完整等式 \(r=t\) 是该寄存器的值绑定。其后各行，包括另一条 \(r=t'\)，都是比较约束，不替换该值。记

\[
\operatorname{bindings}(\bar{E})
=\text{各寄存器首次出现的完整等式，按列表顺序},
\qquad
\operatorname{constraints}(\bar{E})
=\bar{E}\setminus\operatorname{bindings}(\bar{E}).
\]

\(\{r=t\}\) 表示只含该赋值的一元列表。空分量为 \([]\)。

源值查询只读取 \(\operatorname{bindings}(\bar{E})\)。单独出现的 \(r=10\) 若是该寄存器的第一条等式，按当前顺序就是值绑定；分支比较通过[局部更新](#赋值覆盖全部旧关系)追加，使它落在既有值绑定之后。比较约束与值绑定可以具有相同左值和比较运算符。

### 右侧项的求解

\(\operatorname{solve}_{\mathrm{Expression}}\) 只对右侧项应用[整项求解](Term/solve.md#化简规则)，保留左值 \(r_w\) 与比较运算符 \(\mathbin{\mathrm{op}}\)。
\[
\operatorname{solve}_{\mathrm{Expression}}(r_w,\mathbin{\mathrm{op}},t_w)
=(r_w,\mathbin{\mathrm{op}},\operatorname{solve}_w(t_w)).
\]
没有寄存器值解释时，不能仅凭左侧标记判定关系真假。

### 关系解释

\(\rho_w:\mathrm{Reg}_w\to\mathbb B_w\) 是寄存器赋值族，寄存器见[寄存器定义](../寄存器定义.md)。\(\widehat{\mathrm{op}}\) 是比较运算符的解释，\(\nu\) 是[项的变元赋值](Term/Term.md#项的解释)。
\[
\left[\!\left[(r_w,\mathbin{\mathrm{op}},t_w)\right]\!\right]_{\rho,\nu}
=\widehat{\mathrm{op}}(\rho_w(r_w),\left[\!\left[ t_w\right]\!\right]_\nu).
\]
**推论 8（纯数值子域的解释保持）。** 在[假设 A](Term/Term.md#叶子与运算符)下，\(E\in\mathrm{Expression}\) 的关系解释满足
\[
\left[\!\left[\operatorname{solve}_{\mathrm{Expression}}(e)\right]\!\right]_{\rho,\nu}
=\left[\!\left[ e\right]\!\right]_{\rho,\nu}.
\]
**证明。** 左侧寄存器与比较运算符不变，右侧解释由[命题 7](Term/solve.md#解释保持性)保持。\(\square\)

\(\rho,\nu\) 是关系的数学解释。推论仅保证单个关系的解释保持性，不包含两个架构的中间关系集合相同这一结论。

含外部结果或包输入的良构右侧项在固定完整补全 \(\theta\) 下也有相同的单关系结论。Lean 实现 `interpretExpr ρ ν θ e : Option Bool` 显式接收外部环境；在 `θ.Total` 与 `e.term.wellFormed=true` 下，`Core.solve_interpret` 保持右侧解释，`solve_width` 保持位宽检查，故按 `interpretExpr` 定义可得求解前后结果相等。这是由项定理得到的推论，未另行声称存在独立的 Expression 保持定理。一般项定理及部分环境反例见 [solve 的解释保持性](Term/solve.md#解释保持性)。

## 比较运算符定义

等式、比较等关系用于指令直接构造基础对象时，其值规则见[真实寄存器的各赋值小节](寄存器/真实寄存器.md)，栈、Map、Context 和包目标的访问规则分别见[虚拟栈读写](寄存器/虚拟栈.md#虚拟栈读写)、[虚拟映射读写](寄存器/虚拟映射.md#虚拟映射读写)、[单元字段读写](寄存器/单元字段读写.md#单元字段读写)与[包字节读写](寄存器/包字节.md#包字节读写)。
用于构造跳转相关事实的关系由 [step](../NodeInference/step.md#生成指令结果) 与 [Jump 的比较指令处理](../NodeInference/Jump/待处理.md#比较指令处理)处理，寄存器文档不讨论这些关系。

项位宽 \(w\in\{32,64\}\)。\(\mathbb T=\{\mathsf{true},\mathsf{false}\}\) 是真值集合，\(\widehat{\mathrm{op}}\) 是比较运算符 \(\mathbin{\mathrm{op}}\in\mathrm{op}_w\) 的解释。
\[
\widehat{\mathrm{op}}:\mathbb B_w\times\mathbb B_w\to\mathbb T.
\]
\(\mathrm{op}_w\) 包含以下比较运算符；下标 u、s 分别对应无符号、有符号比较。
\[
=,\ne,<_{u},\le_u,>_u,\ge_u,<_{s},\le_s,>_s,\ge_s.
\]
对整数关系 \(\diamond\in\{=,\ne,<,\le,>,\ge\}\)，\(u_w,s_w\) 是[无符号与有符号解释](Term/位向量.md#位向量)。
\[
\widehat{\diamond_u}(a,b)\iff u_w(a)\diamond u_w(b),
\qquad
\widehat{\diamond_s}(a,b)\iff s_w(a)\diamond s_w(b).
\]
等式与非等式无需区分有符号、无符号解释。对 \(1\le q\le w\)，上标 \([q]\) 指低 q 位比较，\(M_q\) 截取低 q 位。
\[
\widehat{\diamond_u^{[q]}}(a,b)
\iff M_q(a)\diamond M_q(b),
\qquad
\widehat{\diamond_s^{[q]}}(a,b)
\iff s_q(M_q(a))\diamond s_q(M_q(b)).
\]
\(\diamond_u^{[w]},\diamond_s^{[w]}\) 分别为 \(\diamond_u,\diamond_s\)。低位等式与非等式分别为 \(=^{[q]}\)、\(\ne^{[q]}\)。

\(\mathrm{BITSNZ}^{[q]}\) 判断低 q 位按位与是否非零，\(\mathrm{AND}_q\) 是按位与函数。
\[
\widehat{\mathrm{BITSNZ}^{[q]}}(a,b)
\iff\mathrm{AND}_q(M_q(a),M_q(b))\ne0,
\]
\(\mathrm{BITSZ}^{[q]}\) 判断低 q 位按位与是否为零，\(\overline{\mathrm{op}}\) 是比较运算符 \(\mathbin{\mathrm{op}}\) 的补关系。
\[
\widehat{\mathrm{BITSZ}^{[q]}}(a,b)
\iff\mathrm{AND}_q(M_q(a),M_q(b))=0,
\qquad
\widehat{\overline{\mathrm{op}}}(a,b)
=\neg\widehat{\mathrm{op}}(a,b).
\]
例如 \(\overline{<_s}=\ge_s\)。对确定的 \(a,b\)，某关系与其补关系恰有一个成立。

### 低位约束不确定完整值

对 32 位栈对象的完整等式 \(\mathrm{SW}(\alpha)=t_{32}\)，\(Z_{32\to64}^{(32),\star}\) 是零扩展的符号提升，\(\mathrm{Real}_{64}(\alpha)\) 是读取结果的真实寄存器。
\[
\mathrm{Real}_{64}(\alpha)=Z_{32\to64}^{(32),\star}(t_{32}).
\]
局部约束 \(\mathrm{SW}(\alpha)=^{[8]}t_{32}\) 只确定低 8 位。

**命题 4（局部关系不确定完整值）。** 固定低 \(q\) 位且 \(q<w\) 时，恰有 \(2^{w-q}\) 个 \(w\) 位值满足该约束。

**证明。** 设固定低位为 \(b\in\mathbb B_q\)。全部解恰为 \(a=b+2^q h\)，其中 \(h\in\mathbb B_{w-q}\)。这些值两两不同，并穷尽所有满足 \(M_q(a)=b\) 的值。\(\square\)

局部等式不能替代完整值等式。局部写入如何保留其他位，由具体指令的值函数规定。


## 比较关系

比较使用已有 Expression \(E=(r_w,\mathbin{\mathrm{op}},t_w)\)。\(r_w\) 是 w 位寄存器标记，\(t_w\) 是同位宽右值，\(\mathbin{\mathrm{op}}\in\mathrm{op}_w\) 指定关系；w 为 32 或 64。左值、比较运算符与右值分别见[左值](#左值)、[比较运算符定义](#比较运算符定义)与[Term](Term/Term.md#term)。

### 值关系与比较约束

例如，\(r_1=a\) 在列表靠前时是值绑定，等值分支再追加 \(r_1=C_{32}(10)\) 是比较约束。[表达式分量](#表达式分量)由顺序区分两种角色及源值查询。约束的并存与赋值覆写见[关系集合按键覆写](#关系集合按键覆写)。

### 关系解释（比较关系）

\(\rho_w(r_w)\) 表示当前寄存器的 w 位值；\(\nu\) 为符号输入赋值，\(\theta\) 为[未解释运算的解释补全](Term/Term.md#未解释运算的解释补全)。\(\llbracket t\rrbracket_{\nu,\theta}\) 是右值在固定赋值和补全下的数值；\(\widehat{\mathrm{op}}\) 是关系对应的布尔函数：

\[
\llbracket r_w\mathbin{\mathrm{op}} t_w\rrbracket_{\rho,\nu,\theta}
=\widehat{\mathrm{op}}\bigl(\rho_w(r_w),\llbracket t_w\rrbracket_{\nu,\theta}\bigr).
\]

已取得右值项的含义见[叶子与运算符](Term/Term.md#叶子与运算符)。

### 部分判定

\(\operatorname{decide}(e,u)\) 用执行前取得的左值项 u 判定比较 Expression e，结果为真、假或未知，不求解累积条件。

\(E=(r_w,\mathbin{\mathrm{op}},t_w)\)，\(u\in\mathrm{Term}_w\) 为 r 的完整旧值项，a、b 为取得的确定数值。\(\operatorname{solve}_w\)、部分数值求值 \(D_w\) 与未确定结果 \(\bot\) 见[部分求值与未解释运算](Term/solve.md#部分求值与未解释运算)，w=32 时使用 \(D_{32}\)。\(\land\) 表示两个条件都满足：

\[
\operatorname{decide}(e,u)=
\begin{cases}
\widehat{\mathrm{op}}(a,b),&D_w(\operatorname{solve}_w(u))=a\ \land\ D_w(\operatorname{solve}_w(t_w))=b,\\
\bot,&D_w(\operatorname{solve}_w(u))=\bot\ \lor\ D_w(\operatorname{solve}_w(t_w))=\bot.
\end{cases}
\]

源项缺失属于[前提检查失败](../NodeInference/step.md)。无变元不保证可求值：含未解释包输入或外部结果的闭项仍可为未知。即使未知两源结构相同，判定也不以化简结果代替数值：化简把带变元的项化成更简的等价形，但判定要求两端取得确定数值，未取得数值时返回未知。

### 位宽与补关系

比较宽度 q 满足 \(1\le q\le w\)；\(\mathbin{\mathrm{op}}^{[q]}\) 的定义与 q=w 时的记号约定见[比较运算符定义](#比较运算符定义)。eBPF JMP32 可以在 Real64 左值与 Term64 右值之间使用带 \([32]\) 的关系，无需创建 Real32 身份。

补关系 \(\overline{\mathrm{op}}\) 及 BITSNZ、BITSZ 的定义见[比较运算符定义](#比较运算符定义)，例如 \(\overline{<_s^{[q]}}=\ge_s^{[q]}\)。

**命题（互补方向）。** 对同一状态的左值 r、右值项 t 及固定的 \((\rho,\nu,\theta)\)，\(r\mathbin{\mathrm{op}} t\) 与 \(r\overline{\mathrm{op}}t\) 恰有一个为真。

**证明。** 两源在该解释下有确定的同位宽值，原条件及补条件的真值为 \(\beta\)、\(\neg\beta\)；\(\neg\) 是布尔否定，二者恰有一个成立。\(\square\)

该命题不证明完整路径可行，也不证明后继位置有效。不同状态的左值可能已经改变，不能仅凭比较运算符互补就断言两次条件矛盾。

比较的指令侧处理见 [NodeInference/Jump/待处理](../NodeInference/Jump/待处理.md#比较指令处理)。


## 关系集合按键覆写

### 唯一性与新增比较

比较约束不按 \((r,\mathbin{\mathrm{op}})\) 强制右值唯一。同一列表里 \(r=a\) 的值绑定和其后的 \(r=10\) 可以并存。\(r<10\) 与 \(r<20\) 两个约束也可以并存。

结构去重不承担可满足性求解。

### 赋值覆盖全部旧关系

设输入列表为 \(\bar{E}\)，指令局部结果为 \(\sigma_i=(\bar{E}_i,\mathcal{O}_i)\)，其中 \(\bar{E}_i\) 是 Expression 列表，\(\mathcal{O}_i\) 是观察列表。记 \(\operatorname{lhs}(E)\) 为左值。赋值与比较的基本操作：

- \(\operatorname{insertEq}(E,r,t)\)：将求解后的 \(r=t\) 置于列表头部，并删除该寄存器的全部旧行。
- \(\operatorname{insertConstraint}(E,e)\)：若 \(e\) 尚未出现则追加到末尾；即使 \(e\) 的关系是 =，也不删除既有值绑定。
- \(\operatorname{override}(E,\bar{E}_i)\)：以 \(\operatorname{bindings}(\bar{E}_i)\) 为写入集 \(W_i\)，删除 \(\bar{E}\) 中左值属于 \(W_i\) 的全部旧行，再接上这些新赋值，最后把 \(\operatorname{constraints}(\bar{E}_i)\) 逐条 \(\operatorname{insertConstraint}\)。

分支比较不得把单独的 \(r=10\) 当成赋值。`applyLocal` 先识别与 \(\mathcal{O}_i\) 中 Branch 条件同关系、同右侧、且当前值绑定仍等于条件左侧的行，对这些行只做 \(\operatorname{insertConstraint}\)；其余行再经 \(\operatorname{override}\)。因此

\[
\operatorname{updateExpr}(E,\bar{E}_i,\mathcal{O}_i)
=\operatorname{insertConstraint}^\ast\bigl(
\operatorname{override}(E,\bar{E}_i\setminus F),\,F\bigr),
\]

其中 \(F\subseteq \bar{E}_i\) 是上述分支事实，\(\operatorname{insertConstraint}^\ast\) 表示依次追加。直接调用 \(\operatorname{override}\)（溢出、ALU、Map 等）仍把 \(\bar{E}_i\) 的首条等式当作写入。

既有完整值与比较约束都在对应左值被赋值时删除。未写入的其他寄存器关系保持不变。

例如 \(\bar{E}=[r_1=a,\,r_1<10]\)，执行赋值 \(r_1=20\) 后得到 \([r_1=20]\)。新状态不会继续约束当前值 20 小于 10。

### 结构性质

**命题 9（有效性保持）。** 输入与 \(\bar{E}_i\) 有限、行结构去重且位宽正确时，更新结果仍满足这些条件。

**证明。** 赋值删除该寄存器全部旧行后再前置新等式，故每个寄存器至多保留一条作为首条等式的值绑定，其余为后置比较。有限列表过滤与追加仍有限。关系本身的位宽不变。约束按结构去重，不要求同比较运算符右值唯一。\(\square\)

**推论 10（更新代数）。** 对上述有效列表 \(\bar{E},\bar{F},\bar{H}\)，\(\times\) 表示 \(\operatorname{override}\)，\([]\) 是空效果；有空更新、重复更新与结合性质：

\[
\bar{E}\times[]=\bar{E},
\qquad (\bar{E}\times\bar{F})\times\bar{F}=\bar{E}\times\bar{F},
\qquad (\bar{E}\times\bar{F})\times\bar{H}=\bar{E}\times(\bar{F}\times\bar{H}).
\]

**证明。** 对每个寄存器分别考察。没有赋值时保留原行并合并约束。有赋值时取最后一次赋值，删除它之前的绑定与约束，只保留其后新增约束。空效果、相同效果重复及括号位置均不改变这个选择。\(\square\)

这些结论不证明当前约束可满足。这些结论不证明指令更新可交换。末态约束不能当成整条路径的历史条件。历史条件见[比较指令处理](../NodeInference/Jump/待处理.md)。

## 多目标更新与同一来源

一次 \(\sigma_i\) 可以写多个对象，更新一次性应用。设实际目标为互异的 \(r_1,\ldots,r_m\)，所需旧源项为 \(t_1,\ldots,t_n\)，均从补充输入后的同一写入前关系 \(\bar{E}_g^{\mathrm{in}}\) 取得；没有输入补充时 \(\bar{E}_g^{\mathrm{in}}=\bar{E}_g\)。\(f_j^\star\) 是第 j 个输出函数的[符号提升](Term/solve.md#化简规则)，\(\bar{E}_i\) 是 Expression 分量，\(\bar{E}_g'\) 是更新后关系：

\[
\bar{E}_i=\{r_j=f_j^\star(t_1,\ldots,t_n):1\le j\le m\},
\qquad \bar{E}_g'=\bar{E}_g\times \bar{E}_i.
\]

某个 \(f_j\) 只使用其中实际所需的源，不因此增加其他输入要求。目标可以同时包含真实寄存器和虚拟单元。即使真实源同时也是写回目标，其旧项也在更新前固定。顺序计算并立即覆写某个目标，会改变其他输出的取源，不能替代本规则。

[FETCH、XCHG、CMPXCHG 的公式与旧值返回证明](寄存器/原子数值更新与旧值返回.md#原子数值更新与旧值返回)、[包存储的多字节写入](寄存器/包字节.md#包字节读写)、[辅助调用的返回赋值和 Map 关系](../Predicate/Helper谓词.md#生成的-expression)。

局部目标互异不代替右侧的类型检查或访问条件。[键唯一性](#局部值效果的类型与解释保持)、[按键覆写](#关系集合按键覆写)。


## 未记录虚拟寄存器的取源

访问指令涉及尚未记录的虚拟寄存器时，在 step 的[检查源项与访问对象](../NodeInference/step.md#检查源项与访问对象)中判断能否补充其输入关系。补充成功才生成 \(\sigma_i\)，无依据时拒绝。RV32 的 LOAD/STORE 与 eBPF 的 LDX/ST/STX 访问已确定的资源中尚未记录的虚拟寄存器时适用这一规则。

指令首次涉及某个虚拟单元时，可以引入该单元的标记。

- 读取已有绑定的虚拟寄存器，直接使用其当前完整等式。
- 读取尚未记录的虚拟寄存器，只能根据输入契约引入其当前值关系。该关系必须复用同一资源输入，且有依据说明此前写入没有改变它。
- 完整写入新规范单元，可以由源值建立完整等式，无需目标旧值。
- 部分写入新规范单元，若其余位没有当前值依据，不能建立完整结果。

输入补充只增加值绑定：按输入契约引入本次读取所需的有限个完整等式，每个左值在补充前列表中尚无值绑定；既有比较行全部保留。补充输入后的关系记作 \(\bar{E}_g^{\mathrm{in}}\)。指令效果从该关系计算。仅有比较而缺少完整源值时，不能当成尚未记录的入口输入。未定义的真实源寄存器不适用这一补充规则。

## 指令结果的前提

[真实寄存器读写](寄存器/真实寄存器.md#真实寄存器赋值)、[栈读写](寄存器/虚拟栈.md#虚拟栈读写)、[Map 读写](寄存器/虚拟映射.md#虚拟映射读写)、[包读写](寄存器/包字节.md#包字节读写)。

成功结果须满足以下前提：

- 指令参数合法。
- 必需源等式唯一且存在。
- 指令操作数与访问规则唯一确定所访问的资源单元。
- 访问有效。

无法确定来源或单元的访问无定义，不能以空 Expression 或新变元代替缺失语义。

真实源值可由已有完整等式取得，或由架构固定值取得，例如 RV32 的 \(x_0\) 恒为零。这个例外不允许为其他缺失源补任意值。

### 局部 Expression 的共同形状

每个实际写入对象在局部效果列表中产生一个完整等式，其中的右侧项是该对象的新完整值项；写入效果不含比较行。

\(\bar{E}_i\) 依[多目标取源规则](#多目标更新与同一来源)从[补充输入后的关系](#未记录虚拟寄存器的取源)计算；\(\bar{E}_g'\) 是最终关系，\(\times\) 是[完整值按键覆写](#赋值覆盖全部旧关系)：

\[
\bar{E}_g'=\bar{E}_g^{\mathrm{in}}\times \bar{E}_i.
\]

读取对象与写入对象可以重叠，例如二元原地算术和原子交换。

### 来源与结构性质

**引理 M1（分类由来源决定）。** 同一访问在指令操作数与访问规则唯一确定资源单元时，确定唯一虚拟类别。同一资源单元的别名访问使用相同标记。不同类别的标记不相等。

**证明。** 第一项使用访问对象的唯一性；后两项由[寄存器定义](../寄存器定义.md)的别名标记要求与寄存器三元组的类别分量不同得到。\(\square\)

指令操作数所确定的访问对象与实际访问对象的一致性、跨规范单元的一致性、访问有效性的证明仍需独立论证。

### Expression 与 Observation 的效果组合

设某个指令实例产生 \(\sigma_i\)。可区分：

- 仅产生 Expression：寄存器赋值、算术结果或链接值。
- Expression 仅增加比较行、Observation 产生 Branch：分支两侧的关系不替换完整值；每个保留候选另按[Branch 的生成条件](../Predicate/Branch谓词.md#生成条件)生成观察。
- 同时产生二者：值关系与调用观察共同发生；Map 元素内写入按[MapWrite 生成条件](../Predicate/MapWrite谓词.md#生成条件)生成观察，包实际存储按[PacketWrite 生成条件](../Predicate/PacketWrite谓词.md#生成条件)生成观察。
- 仅产生 Return：不带链接值的最外层正常返回，其 Expression 列表为空；正常返回仍须[检查返回寄存器的完整等式](../NodeInference/step.md)，并在已识别为最外层正常返回的步骤按[Return 的生成条件](../Predicate/Return谓词.md#生成条件)生成观察。
- 二者均为空：只改变后继位置的无条件跳转或观察范围外的操作。
- 局部规则无定义：不产生成功候选。

分类由指令实例及选定观察范围共同决定。带链接值的跳转与无链接跳转不同。普通间接跳转与已绑定的最外层返回也不同。

后继位置不作为额外语义状态。若某实例明确产生 PC 等式，就按实际局部关系分类。Map 元素内写入与包写入的观察由各类观察维护；栈访问及其余资源访问的观察形式仍须规定。数值传值公式不能代替这些观察。

未选取观察的算术赋值、普通传值及未被识别为最外层正常返回的无条件跳转可以取 \(\mathcal{O}_i=\varnothing\)。空局部观察仅表示所用规则未增加观察。它不证明没有副作用。它不证明访问或调用满足全部有效性条件。局部观察集合的元素域为[五类观察域](../Predicate/谓词定义.md#类型与结构相等)，构造分别见[Helper观察](../Predicate/Helper谓词.md#生成条件)、[Branch观察](../Predicate/Branch谓词.md#生成条件)、[Return观察](../Predicate/Return谓词.md#生成条件)、[MapWrite观察](../Predicate/MapWrite谓词.md#生成条件)与[PacketWrite观察](../Predicate/PacketWrite谓词.md#生成条件)。混合观察接入 step 的规则见[结构累积及解释义务](../Predicate/谓词定义.md#观察集合累积与可满足性)。已绑定 helper 的值关系见[Helper 生成的 Expression](../Predicate/Helper谓词.md#生成的-expression)。

### 部分值函数与符号提升

值效果由所选规则在给定执行前关系上确定。

[局部关系与完整值的区别](#低位约束不确定完整值)。普通赋值不要求目标旧值。原地算术和部分单元覆盖按实际规则读取。虚拟运算还依赖绑定单元位宽 w，严格记作 \(f_{i,w}\)。不同 w 可有不同签名和元数。目标身份不是数值函数的额外输入。

[纯数值规则的符号提升、闭项折叠及未解释结果的处理](Term/solve.md#solve-的化简与求值)、[局部结果的类型与解释一致性](#局部值效果的类型与解释保持)。

## 局部值效果的类型与解释保持

输入键唯一、源项类型正确且齐备，以及[指令参数、访问对象与访问前提](#指令结果的前提)均作为前提。数值运算的解释必须遵循所给签名。未解释外部结果不套用纯数值全函数假设。

**命题。** 对成功的 \(\bar{E}_i\)：

1. \(\bar{E}_i\) 是有限 Expression 集合，每个关系左右两侧位宽一致。
2. 对任一类型正确、完整应用项属于纯数值子域的规则，在其解释域内有以下等式。\(t_1,\ldots,t_n\) 是源项，\(f_i^\star\) 是规则的符号提升，\(\widehat f_i\) 是其数值解释；\(\nu\) 是变元赋值，\(\theta\) 是[未解释运算的解释补全](Term/Term.md#未解释运算的解释补全)，双括号表示项解释：

\[
\left[\!\left[f_i^\star(t_1,\ldots,t_n)\right]\!\right]_{\nu,\theta}
=\widehat f_i(\left[\!\left[t_1\right]\!\right]_{\nu,\theta},\ldots,
\left[\!\left[t_n\right]\!\right]_{\nu,\theta}).
\]

3. 局部关系键唯一，整体按键覆写保持键唯一。

**证明。** 算术、常元、链接与读取规则产生匹配真实目标宽度的项。32 位运算写 Real64 时明确零扩展。虚拟单元写入由[字段覆盖性质](寄存器/单元字段读写.md#字段覆盖性质)保持目标宽度。[包字节规则](寄存器/包字节.md#包字节读写)同时满足 32 位项与 \(\mathbb B_8\) 取值。原子数值结果按单元宽度取模。普通规则写一个目标，包写入写有限个不同字节，原子多目标分别写虚拟与真实身份，故目标有限且键互异。

符号提升是应用项的 solve。由[解释保持性](Term/solve.md#解释保持性)，solve 不改变应用项的解释。再用应用项定义得到第二项。最后应用[按键覆写性质](#关系集合按键覆写)。\(\square\)

第二项的纯数值前提约束整个应用项，包括其全部子项。含外部结果或包输入的良构项在完整解释补全下也适用[命题 7](Term/solve.md#解释保持性)。任意缺失外部值的部分 `Option` 解释不满足无条件保持等式。

[固定与只读寄存器的保持](寄存器/真实寄存器.md#真实寄存器赋值)、[高位清零](寄存器/真实寄存器.md#真实寄存器低位视图与写回)、[字段覆盖](寄存器/单元字段读写.md#字段覆盖性质)、[旧值返回](寄存器/原子数值更新与旧值返回.md#原子数值更新与旧值返回)。访问对象与实际指令操作数的一致性、完整调用与访问观察、并发语义仍需独立论证。不将数学推导视为 ISA 语义正确性的完整证明。

