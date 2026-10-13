# Expr

## 索引

- [表达式定义](#表达式定义)：表达式定义、关系符定义。
- [比较关系](#比较关系)：比较关系。
- [关系集合更新](#关系集合按键覆写)：关系集合按键覆写、多目标更新与同一来源。
- [指令结果](#指令结果的前提)：指令结果的前提、局部值效果的类型与解释保持。
- [未记录虚拟寄存器的取源](#未记录虚拟寄存器的取源)：未记录虚拟寄存器的取源。
- [资源读取与位置赋值](寄存器/资源读取与位置赋值.md)：资源读取与位置赋值。
- [单元字段读写](寄存器/单元字段读写.md)：单元字段读写。
- [原子数值更新与旧值返回](寄存器/原子数值更新与旧值返回.md)：原子数值更新与旧值返回。
- [Helper 生成的 Expr](../Predicate/Helper谓词.md#生成的-expr)：辅助调用的返回赋值与 Map 关联。
- [Term/Term](Term/Term.md)：Term。
- [Term/solve](Term/solve.md)：solve 的化简与求值。
- [寄存器/真实寄存器](寄存器/真实寄存器.md)：真实寄存器赋值、真实寄存器低位视图与写回、常元赋值、移动与符号扩展赋值、算术与位运算赋值、乘法高半赋值、除法与余数赋值、字节序转换赋值、跳转链接值赋值。
- [寄存器/虚拟栈](寄存器/虚拟栈.md)：虚拟栈读写。
- [寄存器/虚拟映射](寄存器/虚拟映射.md)：虚拟映射读写。
- [寄存器/包字节](寄存器/包字节.md)：包字节读写。
- [Term/位向量](Term/位向量.md)：记号与位向量。
- [Term/数值函数](Term/数值函数.md)：共同数值函数。
- [工程模块与迁移](../NodeInference/路径合并FFI.md#工程模块与迁移)：表达式实现的 ClassifierExpr 归属，以及与 PathMerge、RV32IMC、EBPF 的依赖分工；跨架构研究与证明限度见[语义范围与证据边界](../NodeInference/路径合并FFI.md#语义范围与证据边界)。

## 表达式定义

位宽集合 \(W\) 与寄存器集合 \(\mathrm{Reg}_w\) 见[寄存器定义](../寄存器定义.md)。\(\mathrm{Rel}_w\) 是[关系符](#关系符定义)集合，\(\mathrm{Term}_w\) 是[Term](Term/Term.md#term)项集合。
\[
\boxed{
\mathrm{Expr}=\bigsqcup_{w\in W}
\bigl(\mathrm{Reg}_w\times\mathrm{Rel}_w\times\mathrm{Term}_w\bigr).
}
\]
\(e=(r_w,\bowtie,t_w)\) 表示关系 \(r_w\bowtie t_w\)。完整值绑定与比较约束的角色由表达式分量中的归属确定。比较仅使用 Expr。

### 左值

左值指定关系所描述的寄存器对象；对象的完整定义见[寄存器定义](../寄存器定义.md)。

#### 左值的类型

对位宽 \(w\in\{32,64\}\)，Expr 的左值是 \(r_w\in\mathrm{Reg}_w\)。左值与右值必须同位宽。

Real、Stack、Map、Packet 均可作为左值；对象身份与相等见[寄存器定义](../寄存器定义.md)。

#### 左值与写入对象

完整等式 \(r_w=t_w\) 可以给出对象的完整值；局部等式见[低位约束不确定完整值](#低位约束不确定完整值)。

LOAD 与普通 STORE 的栈左值选择见[虚拟栈读写](寄存器/虚拟栈.md#虚拟栈读写)。
LOAD 与普通 STORE 的 Map 左值选择见[虚拟映射读写](寄存器/虚拟映射.md#虚拟映射读写)。
LOAD 与普通 STORE 的包左值选择见[包字节读写](寄存器/包字节.md#包字节读写)。
访问对象见[指令结果的前提](#指令结果的前提)。

别名标记与访问宽度下的规范单元划分见[寄存器定义](../寄存器定义.md)。

值绑定与比较约束的更新规则见[关系集合按键覆写](#关系集合按键覆写)。

### 表达式分量

\(\mathscr F(\mathrm{Expr})\) 的元素为 \(\mathcal E=(\mathcal V,\mathcal C)\)。\(\mathcal V\) 是有限完整值绑定集合，只使用 =，且每个寄存器的绑定唯一。\(\mathcal C\) 是按结构相等去重的有限比较 Expr 集合。集合归属保留角色信息。

\(\{r=t\}\) 表示 \((\{r=t\},\varnothing)\)。空表达式分量为 \((\varnothing,\varnothing)\)。

源值查询只读取 \(\mathcal V\) 的完整等式。\(\mathcal C\) 中的 \(r=10\) 不自动成为 r 的完整源值。比较约束与值绑定可以具有相同左值和关系符。

### 右侧项的求解

\(\operatorname{solve}_{\mathrm{Expr}}\) 只对右侧项应用[整项求解](Term/solve.md#化简规则)，保留左值 \(r_w\) 与关系符 \(\bowtie\)。
\[
\operatorname{solve}_{\mathrm{Expr}}(r_w,\bowtie,t_w)
=(r_w,\bowtie,\operatorname{solve}_w(t_w)).
\]
没有寄存器值解释时，不能仅凭左侧标记判定关系真假。

### 关系解释

\(\rho_w:\mathrm{Reg}_w\to\mathbb B_w\) 是寄存器赋值族，寄存器见[寄存器定义](../寄存器定义.md)。\(\widehat{\bowtie}\) 是关系符的解释，\(\nu\) 是[项的变元赋值](Term/Term.md#项的解释)。
\[
\left[\!\left[(r_w,\bowtie,t_w)\right]\!\right]_{\rho,\nu}
=\widehat{\bowtie}(\rho_w(r_w),\left[\!\left[ t_w\right]\!\right]_\nu).
\]
**推论 8（纯数值子域的解释保持）。** 在[假设 A](Term/Term.md#叶子与运算符)下，\(e\in\mathrm{Expr}\) 的关系解释满足
\[
\left[\!\left[\operatorname{solve}_{\mathrm{Expr}}(e)\right]\!\right]_{\rho,\nu}
=\left[\!\left[ e\right]\!\right]_{\rho,\nu}.
\]
**证明。** 左侧寄存器与关系符号不变，右侧解释由[命题 7](Term/solve.md#解释保持性)保持。\(\square\)

\(\rho,\nu\) 是关系的数学解释。推论仅保证单个关系的解释保持性，不包含两个架构的中间关系集合相同这一结论。

## 关系符定义

等式、比较等关系用于指令直接构造基础对象时，其值规则见[真实寄存器的各赋值小节](寄存器/真实寄存器.md)，栈、Map 和包目标的访问规则分别见[虚拟栈读写](寄存器/虚拟栈.md#虚拟栈读写)、[虚拟映射读写](寄存器/虚拟映射.md#虚拟映射读写)与[包字节读写](寄存器/包字节.md#包字节读写)。
用于构造跳转相关事实的关系由 [step](../NodeInference/step.md#生成指令结果) 与 [Jump 的比较指令处理](../NodeInference/Jump/待处理.md#比较指令处理)处理，寄存器文档不讨论这些关系。

项位宽 \(w\in\{32,64\}\)。\(\mathbb T=\{\mathsf{true},\mathsf{false}\}\) 是真值集合，\(\widehat{\bowtie}\) 是关系符 \(\bowtie\in\mathrm{Rel}_w\) 的解释。
\[
\widehat{\bowtie}:\mathbb B_w\times\mathbb B_w\to\mathbb T.
\]
\(\mathrm{Rel}_w\) 包含以下关系符；下标 u、s 分别对应无符号、有符号比较。
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
\(\mathrm{BITSZ}^{[q]}\) 判断低 q 位按位与是否为零，\(\overline{\bowtie}\) 是关系符 \(\bowtie\) 的补关系。
\[
\widehat{\mathrm{BITSZ}^{[q]}}(a,b)
\iff\mathrm{AND}_q(M_q(a),M_q(b))=0,
\qquad
\widehat{\overline{\bowtie}}(a,b)
=\neg\widehat{\bowtie}(a,b).
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

比较使用已有 Expr \(e=(r_w,\bowtie,t_w)\)。\(r_w\) 是 w 位寄存器标记，\(t_w\) 是同位宽右值，\(\bowtie\in\mathrm{Rel}_w\) 指定关系；w 为 32 或 64。左值、关系符与右值分别见[左值](#左值)、[关系符定义](#关系符定义)与[Term](Term/Term.md#term)。

### 值关系与比较约束

例如，\(r_1=a\) 是值绑定，等值分支新增 \(r_1=C_{32}(10)\) 是比较约束。[表达式分量](#表达式分量)区分两种角色及源值查询。约束的并存与赋值覆写见[关系集合按键覆写](#关系集合按键覆写)。

### 关系解释（比较关系）

\(\rho_w(r_w)\) 表示当前寄存器的 w 位值；\(\nu\) 为符号输入赋值，\(\theta\) 为[未解释运算的解释补全](Term/Term.md#未解释运算的解释补全)。\(\llbracket t\rrbracket_{\nu,\theta}\) 是右值在固定赋值和补全下的数值；\(\widehat{\bowtie}\) 是关系对应的布尔函数：

\[
\llbracket r_w\bowtie t_w\rrbracket_{\rho,\nu,\theta}
=\widehat{\bowtie}\bigl(\rho_w(r_w),\llbracket t_w\rrbracket_{\nu,\theta}\bigr).
\]

已取得右值项的含义见[叶子与运算符](Term/Term.md#叶子与运算符)。

### 部分判定

\(\operatorname{decide}(e,u)\) 用执行前取得的左值项 u 判定比较 Expr e，结果为真、假或未知，不求解累积条件。

\(e=(r_w,\bowtie,t_w)\)，\(u\in\mathrm{Term}_w\) 为 r 的完整旧值项，a、b 为取得的确定数值。\(\operatorname{solve}_w\)、部分数值求值 \(D_w\) 与未确定结果 \(\bot\) 见[部分求值与未解释运算](Term/solve.md#部分求值与未解释运算)，w=32 时使用 \(D_{32}\)。\(\land\) 表示两个条件都满足：

\[
\operatorname{decide}(e,u)=
\begin{cases}
\widehat{\bowtie}(a,b),&D_w(\operatorname{solve}_w(u))=a\ \land\ D_w(\operatorname{solve}_w(t_w))=b,\\
\bot,&D_w(\operatorname{solve}_w(u))=\bot\ \lor\ D_w(\operatorname{solve}_w(t_w))=\bot.
\end{cases}
\]

源项缺失属于[前提检查失败](../NodeInference/step.md)。无变元不保证可求值：含未解释包输入或外部结果的闭项仍可为未知。即使未知两源结构相同，判定也不以化简结果代替数值：化简把带变元的项化成更简的等价形，但判定要求两端取得确定数值，未取得数值时返回未知。

### 位宽与补关系

比较宽度 q 满足 \(1\le q\le w\)；\(\bowtie^{[q]}\) 的定义与 q=w 时的记号约定见[关系符定义](#关系符定义)。eBPF JMP32 可以在 Real64 左值与 Term64 右值之间使用带 \([32]\) 的关系，无需创建 Real32 身份。

补关系 \(\overline{\bowtie}\) 及 BITSNZ、BITSZ 的定义见[关系符定义](#关系符定义)，例如 \(\overline{<_s^{[q]}}=\ge_s^{[q]}\)。

**命题（互补方向）。** 对同一状态的左值 r、右值项 t 及固定的 \((\rho,\nu,\theta)\)，\(r\bowtie t\) 与 \(r\overline{\bowtie}t\) 恰有一个为真。

**证明。** 两源在该解释下有确定的同位宽值，原条件及补条件的真值为 \(\beta\)、\(\neg\beta\)；\(\neg\) 是布尔否定，二者恰有一个成立。\(\square\)

该命题不证明完整路径可行，也不证明后继位置有效。不同状态的左值可能已经改变，不能仅凭关系符互补就断言两次条件矛盾。

比较的指令侧处理见 [NodeInference/Jump/待处理](../NodeInference/Jump/待处理.md#比较指令处理)。


## 关系集合按键覆写

### 唯一性与新增比较

比较约束不按 \((r,\bowtie)\) 强制右值唯一。\(r=a\) 的值绑定和 \(r=10\) 的约束可以并存。\(r<10\) 与 \(r<20\) 两个约束也可以并存。

结构并集不承担可满足性求解。

### 赋值覆盖全部旧关系

设输入为 \(\mathcal E=(\mathcal V,\mathcal C)\)，指令的结果为 \(\sigma_i=(E_i,P_i)\)，其中 \(E_i=(\mathcal V_i,\mathcal C_i)\) 是 Expr 分量，\(P_i\) 是谓词分量。\(\mathcal V_i\) 与 \(\mathcal C_i\) 分别是新赋值与新比较约束。\(W_i=\{r:(r,=,t)\in\mathcal V_i\}\) 是本次写入的寄存器集合；\(\operatorname{lhs}(e)\) 是 Expr 左值，\(\times\) 是表达式更新操作，\(\mathcal V',\mathcal C'\) 是更新后的两个分量：

\[
\begin{aligned}
\mathcal V'&=\{e\in\mathcal V:\operatorname{lhs}(e)\notin W_i\}\cup\mathcal V_i,\\
\mathcal C'&=\{e\in\mathcal C:\operatorname{lhs}(e)\notin W_i\}\cup\mathcal C_i,\\
\operatorname{updateExpr}(\mathcal E,E_i)
&=\mathcal E\times E_i=(\mathcal V',\mathcal C').
\end{aligned}
\]

既有完整值与比较约束都在对应左值被赋值时删除。未写入的其他寄存器关系保持不变。

例如 \(\mathcal V=\{r_1=a\}\)、\(\mathcal C=\{r_1<10\}\)，执行 \(r_1=20\) 后，\(\mathcal V'=\{r_1=20\}\)、\(\mathcal C'=\varnothing\)。新状态不会继续约束当前值 20 小于 10。

### 结构性质

**命题 9（有效性保持）。** 输入与 \(E_i\) 有限、值绑定键唯一且位宽正确时，更新结果仍满足这些条件。比较约束结构去重。

**证明。** 写入左值的旧关系已全部过滤，新旧值绑定没有共同左值；各部分内部唯一，故并集唯一。有限集合过滤与并集仍有限。关系本身的位宽不变。约束采用结构集合，不要求同关系符右值唯一。\(\square\)

**推论 10（更新代数）。** 对上述有效分量 \(\mathcal E,F,H\)，\(\times\) 表示按键覆写，\((\varnothing,\varnothing)\) 是空效果；有空更新、重复更新与结合性质：

\[
\mathcal E\times(\varnothing,\varnothing)=\mathcal E,
\qquad (\mathcal E\times F)\times F=\mathcal E\times F,
\qquad (\mathcal E\times F)\times H=\mathcal E\times(F\times H).
\]

**证明。** 对每个寄存器分别考察。没有赋值时保留原绑定并合并约束。有赋值时取最右侧赋值，删除它之前的绑定与约束，只保留其后新增约束。空效果、相同效果重复及括号位置均不改变这个选择。\(\square\)

这些结论不证明当前约束可满足。这些结论不证明指令更新可交换。末态约束不能当成整条路径的历史条件。历史条件见[比较指令处理](../NodeInference/Jump/待处理.md)。

## 多目标更新与同一来源

一次 \(\sigma_i\) 可以写多个对象，更新一次性应用。设实际目标为互异的 \(r_1,\ldots,r_m\)，所需旧源项为 \(t_1,\ldots,t_n\)，均从补充输入后的同一写入前关系 \(\overline E_g\) 取得；没有输入补充时 \(\overline E_g=E_g\)。\(f_j^\star\) 是第 j 个输出函数的[符号提升](Term/solve.md#化简规则)，\(E_i\) 是 Expr 分量，\(E_g'\) 是更新后关系：

\[
E_i=\{r_j=f_j^\star(t_1,\ldots,t_n):1\le j\le m\},
\qquad E_g'=E_g\times E_i.
\]

某个 \(f_j\) 只使用其中实际所需的源，不因此增加其他输入要求。目标可以同时包含真实寄存器和虚拟单元。即使真实源同时也是写回目标，其旧项也在更新前固定。顺序计算并立即覆写某个目标，会改变其他输出的取源，不能替代本规则。

[FETCH、XCHG、CMPXCHG 的公式与旧值返回证明](寄存器/原子数值更新与旧值返回.md#原子数值更新与旧值返回)、[包存储的多字节写入](寄存器/包字节.md#包字节读写)、[辅助调用的返回赋值和 Map 关系](../Predicate/Helper谓词.md#生成的-expr)。

局部目标互异不代替右侧的类型检查或访问条件。[键唯一性](#局部值效果的类型与解释保持)、[按键覆写](#关系集合按键覆写)。


## 未记录虚拟寄存器的取源

访问指令涉及尚未记录的虚拟寄存器时，在 step 的[检查源项与访问对象](../NodeInference/step.md#检查源项与访问对象)中判断能否补充其输入关系。补充成功才生成 \(\sigma_i\)，无依据时拒绝。RV32 的 LOAD/STORE 与 eBPF 的 LDX/ST/STX 访问已确定的资源中尚未记录的虚拟寄存器时适用这一规则。

指令首次涉及某个虚拟单元时，可以引入该单元的标记。

- 读取已有绑定的虚拟寄存器，直接使用其当前完整等式。
- 读取尚未记录的虚拟寄存器，只能根据输入契约引入其当前值关系。该关系必须复用同一资源输入，且有依据说明此前写入没有改变它。
- 完整写入新规范单元，可以由源值建立完整等式，无需目标旧值。
- 部分写入新规范单元，若其余位没有当前值依据，不能建立完整结果。

输入补充只增加值绑定：按输入契约引入本次读取所需的有限个完整等式，每个左值在已有值绑定与比较约束中均未出现；比较约束全部保留。补充输入后的关系记作 \(\overline E_g\)。指令效果从该关系计算。仅有比较而缺少完整源值时，不能当成尚未记录的入口输入。未定义的真实源寄存器不适用这一补充规则。

## 指令结果的前提

[真实寄存器读写](寄存器/真实寄存器.md#真实寄存器赋值)、[栈读写](寄存器/虚拟栈.md#虚拟栈读写)、[Map 读写](寄存器/虚拟映射.md#虚拟映射读写)、[包读写](寄存器/包字节.md#包字节读写)。

成功结果须满足以下前提：

- 指令参数合法。
- 必需源等式唯一且存在。
- 指令操作数与访问规则唯一确定所访问的资源单元。
- 访问有效。

无法确定来源或单元的访问无定义，不能以空 Expr 或新变元代替缺失语义。

真实源值可由已有完整等式取得，或由架构固定值取得，例如 RV32 的 \(x_0\) 恒为零。这个例外不允许为其他缺失源补任意值。

### 局部 Expr 的共同形状

每个实际写入对象在值绑定分量产生一个完整等式，其中的右侧项是该对象的新完整值项；写入效果不含比较约束。

\(E_i\) 依[多目标取源规则](#多目标更新与同一来源)从[补充输入后的关系](#未记录虚拟寄存器的取源)计算；\(E_g'\) 是最终关系，\(\times\) 是[完整值按键覆写](#赋值覆盖全部旧关系)：

\[
E_g'=\overline E_g\times E_i.
\]

读取对象与写入对象可以重叠，例如二元原地算术和原子交换。

### 来源与结构性质

**引理 M1（分类由来源决定）。** 同一访问在指令操作数与访问规则唯一确定资源单元时，确定唯一虚拟类别。同一资源单元的别名访问使用相同标记。不同类别的标记不相等。

**证明。** 第一项使用访问对象的唯一性；后两项由[寄存器定义](../寄存器定义.md)的别名标记要求与寄存器三元组的类别分量不同得到。\(\square\)

指令操作数所确定的访问对象与实际访问对象的一致性、跨规范单元的一致性、访问有效性的证明仍需独立论证。

### Expr 与 Predicate 的效果组合

设某个指令实例产生 \(\sigma_i\)。可区分：

- 仅产生 Expr：寄存器赋值、算术结果或链接值。
- Expr 仅增加比较约束、Predicate 产生 Branch：分支两侧的关系不替换完整值；每个保留候选另按[Branch 的生成条件](../Predicate/Branch谓词.md#生成条件)生成谓词。
- 同时产生二者：值关系与调用观察共同发生；Map 元素内写入按[MapWrite 生成条件](../Predicate/MapWrite谓词.md#生成条件)生成观察，包实际存储按[PacketWrite 生成条件](../Predicate/PacketWrite谓词.md#生成条件)生成观察。
- 仅产生 Return：不带链接值的最外层正常返回，其 Expr 分量为空；正常返回仍须[检查返回寄存器的完整等式](../NodeInference/step.md)，并在已识别为最外层正常返回的步骤按[Return 的生成条件](../Predicate/Return谓词.md#生成条件)生成谓词。
- 二者均为空：只改变后继位置的无条件跳转或观察范围外的操作。
- 局部规则无定义：不产生成功候选。

分类由指令实例及选定观察范围共同决定。带链接值的跳转与无链接跳转不同。普通间接跳转与已绑定的最外层返回也不同。

后继位置不作为额外语义状态。若某实例明确产生 PC 等式，就按实际局部关系分类。Map 元素内写入与包写入的观察由各类谓词维护；栈访问及其余资源访问的观察形式仍须规定。数值传值公式不能代替这些观察。

未选取观察的算术赋值、普通传值及未被识别为最外层正常返回的无条件跳转可以取 \(P_i=\varnothing\)。空局部观察仅表示所用规则未增加观察。它不证明没有副作用。它不证明访问或调用满足全部有效性条件。局部观察集合的元素域为[五类谓词域](../Predicate/谓词定义.md#类型与结构相等)，构造分别见[Helper谓词](../Predicate/Helper谓词.md#生成条件)、[Branch谓词](../Predicate/Branch谓词.md#生成条件)、[Return谓词](../Predicate/Return谓词.md#生成条件)、[MapWrite谓词](../Predicate/MapWrite谓词.md#生成条件)与[PacketWrite谓词](../Predicate/PacketWrite谓词.md#生成条件)。Branch、Return、MapWrite、PacketWrite 及混合观察集合接入 step 的累积规则见[观察累积义务](../Predicate/谓词定义.md#观察集合累积与可满足性)。已绑定 helper 的值关系见[Helper 生成的 Expr](../Predicate/Helper谓词.md#生成的-expr)。

### 部分值函数与符号提升

值效果由所选规则在给定执行前关系上确定。

[局部关系与完整值的区别](#低位约束不确定完整值)。普通赋值不要求目标旧值。原地算术和部分单元覆盖按实际规则读取。虚拟运算还依赖绑定单元位宽 w，严格记作 \(f_{i,w}\)。不同 w 可有不同签名和元数。目标身份不是数值函数的额外输入。

[纯数值规则的符号提升、闭项折叠及未解释结果的处理](Term/solve.md#solve-的化简与求值)、[局部结果的类型与解释一致性](#局部值效果的类型与解释保持)。

## 局部值效果的类型与解释保持

输入键唯一、源项类型正确且齐备，以及[指令参数、访问对象与访问前提](#指令结果的前提)均作为前提。数值运算的解释必须遵循所给签名。未解释外部结果不套用纯数值全函数假设。

**命题。** 对成功的 \(E_i\)：

1. \(E_i\) 是有限 Expr 集合，每个关系左右两侧位宽一致。
2. 对任一类型正确、完整应用项属于纯数值子域的规则，在其解释域内有以下等式。\(t_1,\ldots,t_n\) 是源项，\(f_i^\star\) 是规则的符号提升，\(\widehat f_i\) 是其数值解释；\(\nu\) 是变元赋值，\(\theta\) 是[未解释运算的解释补全](Term/Term.md#未解释运算的解释补全)，双括号表示项解释：

\[
\left[\!\left[f_i^\star(t_1,\ldots,t_n)\right]\!\right]_{\nu,\theta}
=\widehat f_i(\left[\!\left[t_1\right]\!\right]_{\nu,\theta},\ldots,
\left[\!\left[t_n\right]\!\right]_{\nu,\theta}).
\]

3. 局部关系键唯一，整体按键覆写保持键唯一。

**证明。** 算术、常元、链接与读取规则产生匹配真实目标宽度的项。32 位运算写 Real64 时明确零扩展。虚拟单元写入由[字段覆盖性质](寄存器/单元字段读写.md#字段覆盖性质)保持目标宽度。[包字节规则](寄存器/包字节.md#包字节读写)同时满足 32 位项与 \(\mathbb B_8\) 取值。原子数值结果按单元宽度取模。普通规则写一个目标，包写入写有限个不同字节，原子多目标分别写虚拟与真实身份，故目标有限且键互异。

符号提升是应用项的 solve。由[解释保持性](Term/solve.md#解释保持性)，solve 不改变应用项的解释。再用应用项定义得到第二项。最后应用[按键覆写性质](#关系集合按键覆写)。\(\square\)

第二项的纯数值前提约束整个应用项，包括其全部子项。若源项含外部事件或包字节等未解释运算，固定解释补全仍可定义数值运算的解释。其 solve 保持性需要另外的部分求值保持性论证。

[固定与只读寄存器的保持](寄存器/真实寄存器.md#真实寄存器赋值)、[高位清零](寄存器/真实寄存器.md#真实寄存器低位视图与写回)、[字段覆盖](寄存器/单元字段读写.md#字段覆盖性质)、[旧值返回](寄存器/原子数值更新与旧值返回.md#原子数值更新与旧值返回)。访问对象与实际指令操作数的一致性、完整调用与访问观察、并发语义仍需独立论证。不将数学推导视为 ISA 语义正确性的完整证明。

