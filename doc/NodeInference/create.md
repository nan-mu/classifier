# create

create 根据已给定的入口项与假设，在调用环境已经建立、目标程序尚未执行时构造初始语义状态 \(\sigma_0=(\mathcal E_0,\mathcal P_0)\)。相邻推理接口见 [step](step.md)。

## RV32

XDP 入口的符号关系集合为 \(\mathcal E_0\)，具有有限性、位宽一致性与关系键唯一性。Reg 采用[寄存器文档](../寄存器定义.md)的定义。Term 采用 [Term](../Expr/Term/Term.md#term)的定义。符号提升采用[solve 的化简与求值](../Expr/Term/solve.md#solve-的化简与求值)的定义。覆写采用[按键覆写](../Expr/Expr.md#关系集合按键覆写)的定义。

入口关系以调用环境已经建立、目标程序尚未执行为时刻。调用环境的赋值与资源有效性是前提，不从一般机器状态推导这些前提。输入包与 Map 的后续行为也不由初态关系单独确定。

### 入口项与假设

给定以下 \(\mathrm{Term}_{32}\) 中的项：

- \(t_{\mathrm{ctx}}\)：上下文对象起始地址。
- \(t_{\mathrm{data}}\)、\(t_{\mathrm{len}}\)：输入包起始地址与字节长度。
- \(t_{\mathrm{sp}}\)：入口栈指针。
- \(t_{\mathrm{return}}\)：外层正常返回位置。
- \(t_{\mathrm{frame}}\)：调用环境保存区起始地址。
- \(t_{\mathrm{entry}}\)：目标程序入口位置 \(j_0\in\mathrm{Pos}_{\mathbf I}\) 的机器地址项；\(j_0\) 是从 1 开始的指令序号，见[程序位置](路径.md#程序位置)。

确定输入可取常元，符号输入可取固定名称变元。同一来源复用同一项；这些项不引用随后会变化的寄存器。

**假设 I。** 入口项位宽正确；调用环境满足其对齐、资源与调用有效性条件；规定的寄存器赋值就是入口时的赋值。资源条件的完整形式保留为模型参数。

定义包结束地址项

\[
t_{\mathrm{end}}
:=\mathrm{ADD}_{32}^{\star}(t_{\mathrm{data}},t_{\mathrm{len}}).
\]

给定 \(\iota_{\mathrm{wifi}}\in\mathbb B_{32}\) 作为接口编号常量。模加法只确定 32 位地址模式；若要解释为不回绕的地址区间，还须加入对实际地址与长度的有效性条件。

### 真实寄存器关系

#### 基础赋值

寄存器别名采用同一标记，例如 \(\mathrm{sp}=x_2\)、\(\mathrm{ra}=x_1\)。令

\[
R_s=\{\mathrm{s0},\ldots,\mathrm{s11}\}
=\{x_8,x_9,x_{18},x_{19},x_{20},x_{21},x_{22},x_{23},x_{24},x_{25},x_{26},x_{27}\}.
\]

基础赋值包含七个真实寄存器；保存寄存器的入口位置绑定由承载集合给定。

定义基础关系集合

\[
\begin{aligned}
\mathcal V_{\mathrm{base}}={}&
\{\mathrm{Real}_{32}(\mathrm{zero})=C_{32}(0),\
\mathrm{Real}_{32}(\mathrm{ra})=t_{\mathrm{return}},\
\mathrm{Real}_{32}(\mathrm{sp})=t_{\mathrm{sp}},\\
&\mathrm{Real}_{32}(\mathrm{t0})=t_{\mathrm{sp}},\
\mathrm{Real}_{32}(\mathrm{t1})=t_{\mathrm{return}},\
\mathrm{Real}_{32}(\mathrm{t2})=t_{\mathrm{frame}},\
\mathrm{Real}_{32}(\mathrm{a0})=t_{\mathrm{ctx}}\}.
\end{aligned}
\]

\(\mathrm{t0}\) 与 SP 具有相同入口值，\(\mathrm{t1}\) 与 RA 具有相同返回值项。这些是入口关系，不表示两个不同寄存器具有相同身份。

#### 承载入口位置的寄存器

令 \(R_{\mathrm{entry}}\) 为调用建立前承载入口位置项的真实寄存器标识集合，并满足既定入口假设。其允许范围为

\[
R_{\mathrm{entry}}\subseteq
\{\mathrm{ra}\}\cup R_s\cup\{\mathrm{a1},\ldots,\mathrm{a7}\}
\cup\{\mathrm{t3},\ldots,\mathrm{t6}\}.
\]

调用建立返回地址后，RA 的旧入口位置值被返回地址覆盖；集合中的其他标识仍保留 \(t_{\mathrm{entry}}\)。定义

\[
\mathcal V_{\mathrm{real},0}=
\mathcal V_{\mathrm{base}}\cup
\{\mathrm{Real}_{32}(r)=t_{\mathrm{entry}}:
r\in R_{\mathrm{entry}}\setminus\{\mathrm{ra}\}\}.
\]

合法的 \(R_{\mathrm{entry}}\setminus\{\mathrm{ra}\}\) 中每个标识与七个基础真实键均不相同，因此各增加一个新键。Lean 的 `rEntries : List Reg` 表示该集合，要求所有元素为上述范围内的 32 位真实寄存器且列表无重复；列表顺序只影响关系的存储排列，不影响关系集合或取值。

**wrapper 调用约定假设。** 调用环境在调用建立前将保存寄存器绑定到已给定的入口位置项，调用建立后这些寄存器仍保留该项。产品适配器据此取 \(R_{\mathrm{entry}}=R_s\)。该赋值是 wrapper 的入口前提，不由一般的 callee-saved 保持规则单独推出。

### 上下文六槽关系

标准 \(\mathrm{xdp\_md}\) 上下文包含六个连续 32 位字段：data、data_end、data_meta、ingress_ifindex、rx_queue_index、egress_ifindex。第 \(j\) 个字段的字节偏移为 \(4j\)。其初值向量为

\[
(u_0,u_1,u_2,u_3,u_4,u_5)
=(t_{\mathrm{data}},t_{\mathrm{end}},C_{32}(0),
C_{32}(\iota_{\mathrm{wifi}}),C_{32}(0),C_{32}(0)).
\]

这些初值属于本入口模型的假设；字段布局本身不确定这些值。

给定上下文规范单元的标识起点 \(\alpha_{\mathrm{ctx}}\in\mathbb N\)，六个字段的单元标识依次为 \(\alpha_{\mathrm{ctx}}+j\)，其中 \(0\le j<6\)。

**假设 II（上下文字段访问）。** 对 \(0\le j<6\)，地址项

\[
\mathrm{ADD}_{32}^{\star}(t_{\mathrm{ctx}},C_{32}(4j))
\]

唯一确定所访问的字段单元为 \(\mathrm{Ctx}_{32}(\alpha_{\mathrm{ctx}}+j)\)，且访问有效。字段地址与单元的对应由指令集侧的入口绑定给定，资源观察的完整语义需另外给定；Expr 本身只记录值关系。

定义

\[
\boxed{
\mathcal V_{\mathrm{ctx},0}
:=\{\mathrm{Ctx}_{32}(\alpha_{\mathrm{ctx}}+j)=u_j:0\le j<6\}.
}
\]

\(u_j\) 只是右侧项的记法。后续若有合法字段更新，应覆写相应值关系；入口项仍表示原始输入。初态构造不保证任意后续字段写入都有定义。

### 初态及其性质

给定有限入口谓词集合 \(\mathcal P_0\)，定义

\[
\boxed{
\mathcal V_0=\mathcal V_{\mathrm{real},0}\cup\mathcal V_{\mathrm{ctx},0},
\qquad\mathcal E_0=(\mathcal V_0,\varnothing),
\qquad\sigma_0=(\mathcal E_0,\mathcal P_0).
}
\]

\(\mathcal P_0\) 的观察类型与解释采用[Predicate 文档](../Predicate/谓词定义.md)的定义；若无额外入口观察，可取 \(\mathcal P_0=\varnothing\)。本构造不凭空添加观察，扩展入口假设时须另行规定其含义。

**命题 I1（有限性与位宽）。** 假设 I、II 成立时，\(\mathcal E_0\in\mathscr F(\mathrm{Expr})\)，每个关系均为完整的 32 位等式；其中 \(\mathscr F(\mathrm{Expr})\) 为有限 Expr 关系集合的类型，\(\mathcal E_0\) 为该类型的初始关系集合。

**证明。** 基础赋值包含七个真实标识，入口位置绑定为 \(R_{\mathrm{entry}}\setminus\{\mathrm{ra}\}\) 的每个元素添加一个真实目标；该集合是有限允许集合的子集。上下文有六个 Context 标识。所有入口项为 32 位，模加法与常元也为 32 位。Real 与 Context 均允许 32 位标记，故两部分的每个等式类型正确且总集合有限。\(\square\)

**命题 I2（键唯一性）。** \(\mathcal V_0\) 满足同左值关系唯一。

**证明。** 基础赋值中的真实寄存器身份互异，别名不重复加入。承载集合中的标识互异，除 RA 外均与基础键不交；RA 保留基础返回地址绑定，因此真实部分键唯一。上下文六个连续标识 \(\alpha_{\mathrm{ctx}}+j\) 互异，故 Context 部分内部键唯一。Real 与 Context 是不交类别，两部分没有公共键，因此它们的并集仍有效。\(\square\)

**命题 I3（基数）。**

\[
|\mathcal V_{\mathrm{real},0}|=7+|R_{\mathrm{entry}}\setminus\{\mathrm{ra}\}|.
\]

上下文六个键与真实键不交，因此初态值绑定总数为

\[
|\mathcal V_0|=13+|R_{\mathrm{entry}}\setminus\{\mathrm{ra}\}|.
\]

**证明。** \(\mathcal V_{\mathrm{base}}\) 的七个真实键编号为 \(\{0,1,2,5,6,7,10\}\)。RA 不增加键；其他合法承载标识的编号属于 \(\{8,9,11,\ldots,31\}\)，与七个基础键均不相同，故恰增加 \(|R_{\mathrm{entry}}\setminus\{\mathrm{ra}\}|\) 个真实键。六个 Context 键彼此互异且与真实键不交，再增加六个键，得到两式。产品的 \(R_{\mathrm{entry}}=R_s\) 含十二个非 RA 标识，因而有十九个真实绑定与二十五个初态绑定。\(\square\)

**命题 I4（入口关系可满足）。** 对每个变元赋值 \(\nu\)，存在寄存器赋值 \(\rho\) 使 \(\mathcal V_0\) 的全部等式成立。

**证明。** 对每个已定义标记，将 \(\rho\) 指定为其唯一右侧项在 \(\nu\) 下的解释。命题 I2 保证没有冲突。其余寄存器任选满足其位宽与类别值域的值即可；未出现的包标记可取零。\(\square\)

该命题只证明 Expr 的代数相容性，不证明入口谓词可满足、资源有效或调用环境真实存在。

### 适用边界与依据

未初始化局部栈槽不补零。真实寄存器只有基础赋值及 \(R_{\mathrm{entry}}\setminus\{\mathrm{ra}\}\) 中的入口位置绑定；读取其余保存寄存器、\(\mathrm{gp}\)、\(\mathrm{tp}\) 或其他缺失真实值无定义，不补任意变元。产品的保存寄存器绑定均复用 \(t_{\mathrm{entry}}\)，不为 \(R_s\)、\(\mathrm{gp}\) 或 \(\mathrm{tp}\) 发明自由变元。\(\mathcal E_0\) 不含包字节关系，其基数结论不计入后续引入的包标记。未记录虚拟寄存器的取源见[未记录虚拟寄存器的取源](../Expr/Expr.md#未记录虚拟寄存器的取源)。五类读写规则见 [Expr 索引](../Expr/Expr.md#索引)。初态本身不定义 Map 访问或外部调用。

上下文字段布局见 [Linux UAPI 的 xdp_md 定义](https://github.com/torvalds/linux/blob/master/include/uapi/linux/bpf.h)。真实寄存器入口赋值、接口编号与字段初值由入口项与假设给定。

RV32 初态等式全部属于值绑定分量 \(\mathcal V_0\)，比较约束初始为空。

## eBPF

### 入口项与位宽条件

给定入口参数

\[
p=(t_{\mathrm{ctx}},t_{\mathrm{sp}},t_{\mathrm{data}},
n,\alpha_{\mathrm{ctx}},\kappa_{\mathrm{packet}},\phi_{\mathrm{stack}}).
\]

\(t_{\mathrm{ctx}}\)、\(t_{\mathrm{sp}}\) 分别是上下文起始地址与只读帧指针的 64 位项；\(t_{\mathrm{data}}\) 是包起始地址的 32 位项。三个项均为[常元或固定名称输入变元](../Expr/Term/Term.md#叶子与运算符)，常元的值须在对应位宽的值域内。应用项与随当前寄存器变化的引用不属于入口项的允许形式。

\(n\in\mathbb N\) 是包字节长度，满足 \(n<2^{32}\)。\(\alpha_{\mathrm{ctx}},\kappa_{\mathrm{packet}},\phi_{\mathrm{stack}}\in\mathbb N\) 分别给定上下文单元标识起点、包资源身份和栈资源身份。寄存器身份与类别采用[寄存器定义](../寄存器定义.md)。

包结束地址项采用[32 位模加法及其符号提升](../Expr/Term/数值函数.md#算术)：

\[
t_{\mathrm{end}}
:=\mathrm{ADD}_{32}^{\star}(t_{\mathrm{data}},C_{32}(n)).
\]

位宽与常元范围不满足上述条件时，入口构造无定义。

### 入口值绑定

真实寄存器的入口关系为

\[
\mathcal V_{\mathrm{real},0}
:=\{\mathrm{Real}_{64}(1)=t_{\mathrm{ctx}},
\mathrm{Real}_{64}(10)=t_{\mathrm{sp}}\}.
\]

\(r_1\) 承载上下文地址，\(r_{10}\) 承载帧指针。\(r_{10}\) 的只读限制及成功更新对它的保持采用[真实寄存器赋值规则](../Expr/寄存器/真实寄存器.md#ebpf真实寄存器赋值)；向虚拟栈单元写入仍可成功。

上下文入口关系为

\[
\mathcal V_{\mathrm{ctx},0}
:=\{\mathrm{Ctx}_{32}(\alpha_{\mathrm{ctx}})=t_{\mathrm{data}},
\mathrm{Ctx}_{32}(\alpha_{\mathrm{ctx}}+1)=t_{\mathrm{end}}\}.
\]

相对 \(t_{\mathrm{ctx}}\) 的字节位移 0 与 4 分别确定 data 与 data_end 单元，只接受完整四字节访问。其他上下文字节位移或访问宽度无定义。单元内容读写采用[单元字段读写](../Expr/寄存器/单元字段读写.md#ebpf)，读出的地址内容写到 64 位真实目标时采用[零扩展读取](../Expr/寄存器/资源读取与位置赋值.md#ebpf-内容读取)。

### 资源入口绑定

包资源 \(\kappa_{\mathrm{packet}}\) 的 64 位根地址项取自当前执行前关系 \(E_g\) 中 data 单元的完整等式。设该等式为 \(\mathrm{Ctx}_{32}(\alpha_{\mathrm{ctx}})=t_{\mathrm{data},g}\)，采用[共同无符号字段读取](../Expr/寄存器/单元字段读写.md#单元字段读写)的参数 \(w=32,\ell=0,q=32,v=64\)：

\[
t_{\mathrm{packet}}(E_g)
:=R_Z^\star(t_{\mathrm{data},g}).
\]

该项的数值解释是完整 32 位 data 值向 64 位的零扩展；入口时 \(t_{\mathrm{data},0}=t_{\mathrm{data}}\)。地址分类与 LDX W 的读取结果复用同一字段读取路径构造的根项。data 的完整等式缺失时，没有 Packet 分类候选。其实现对应为 [EBPF/Memory.lean](../../EBPF/Memory.lean) 的 `packetRoot` 与 [CellAccess.read](../../Core/Virtual.lean)。

对字节数 \(b\in\{1,2,4,8\}\)，相对该根地址的自然数字节偏移 \(o\) 必须满足

\[
o+b\le n.
\]

包身份与偏移共同确定所访问的包字节标记；多字节拼接、拆分与重叠采用[包字节读写](../Expr/寄存器/包字节.md#读取拼接与写入拆分)。未写入包字节的首次读取可按已绑定输入资源补充其输入等式，采用[未记录虚拟寄存器的取源](../Expr/Expr.md#未记录虚拟寄存器的取源)；这些等式不属于入口值绑定。输入补充使用固定的 32 位入口项 \(t_{\mathrm{data}}\) 作为包输入基项，与用于地址分类的 64 位字段读取根项分别保留其位宽与用途。

栈资源 \(\phi_{\mathrm{stack}}\) 以 \(t_{\mathrm{sp}}\) 为上端点，覆盖其下方固定 512 字节，并分为 128 个四字节规范单元。区间、单元编号、单射身份编码与访问条件采用[eBPF 的栈读写](../Expr/寄存器/虚拟栈.md#ebpf-的栈读写)。

资源分类使用执行前真实基址寄存器的完整项和指令字节偏移。根项本身、恒等包装及加闭合常量得到的根相对别名可以确定整数位移；常元根与常元地址还可按 64 位差确定有符号位移。所有满足范围条件的 Context、Stack、Packet 候选中必须恰有一个候选，否则访问无定义。该入口没有 Map 对象、条目身份或 Map 地址绑定；Map 内容和位置绑定的前提见[资源读取与位置赋值](../Expr/寄存器/资源读取与位置赋值.md#ebpf-位置赋值)。

### 外部假设与初态边界

将入口绑定解释为真实执行环境时，还须给定以下外部假设：

- data 与 data_end 的 32 位地址运算、包根的 64 位访问区间、上下文字段区间及帧指针下方的栈区间均不回绕；模加法本身只确定位模式。
- 上下文、包与栈资源有效，实际读取或写入具有相应可读性或可写性；有效范围内的地址分类与真实对象一致。
- 执行环境的字节序与这些普通内存访问的小端规则一致。
- 访问满足执行环境要求的对齐、权限及其他访问条件；范围检查与数值字段函数不证明这些条件。
- 若长度依赖符号输入，须另外给出其取值范围、与 data_end 的关系及访问界限的依据。当前参数 \(n\) 是给定自然数，入口构造不接受符号长度项。

初态的比较约束与入口观察均为空。谓词集合及其解释采用[谓词定义](../Predicate/谓词定义.md#类型与结构相等)。其列表表示为 `[]`：

\[
\mathcal P_0:=\varnothing.
\]

空 \(\mathcal P_0\) 仅表示入口没有记录观察，不证明上述资源假设、访问有效性或真实调用环境的存在。

入口仅绑定两个真实寄存器与两个上下文单元。其余四个 xdp_md 字段、其他真实寄存器、包字节和栈单元内容均没有入口等式；未初始化的栈内容不补零，也不补任意输入值。入口不产生 helper、Map 或其他资源的附加绑定。

### eBPF 初态及其性质

入口值绑定集合为

\[
\mathcal V_0
:=\mathcal V_{\mathrm{real},0}\cup\mathcal V_{\mathrm{ctx},0}.
\]

Expr 的值绑定与比较约束分量分别为

\[
\mathcal E_0:=(\mathcal V_0,\varnothing).
\]

初始语义状态为

\[
\sigma_0:=(\mathcal E_0,\mathcal P_0).
\]

**命题 E1（有限性与位宽）。** 对满足入口位宽条件的参数 \(p\)，\(\mathcal E_0\) 有限；两个真实关系是完整 64 位等式，两个上下文关系是完整 32 位等式。

**证明。** 两个关系集合各列出两个等式。真实目标与对应叶子项均为 64 位；上下文目标与 \(t_{\mathrm{data}}\)、\(t_{\mathrm{end}}\) 均为 32 位，32 位加法保持位宽。因此四个等式类型正确且集合有限。\(\square\)

**命题 E2（键唯一性）。** \(\mathcal V_0\) 的每个左值恰有一个完整等式。

**证明。** 真实编号 1 与 10 互异；自然数 \(\alpha_{\mathrm{ctx}}\) 与 \(\alpha_{\mathrm{ctx}}+1\) 互异。Real 与 Context 类别不交，故四个左值两两不同。\(\square\)

**命题 E3（基数）。**

\[
|\mathcal V_0|=4.
\]

**证明。** 真实部分与上下文部分各有两个成员，命题 E2 保证它们没有公共键，也没有重复成员，故并集有四个成员。\(\square\)

**命题 E4（入口关系可满足）。** 对每个入口变元赋值 \(\nu\)，存在寄存器赋值 \(\rho\) 使 \(\mathcal V_0\) 的全部等式成立。

**证明。** 将每个已绑定左值的 \(\rho\) 值指定为其右侧项在 \(\nu\) 下的解释。命题 E1 保证这些值属于相应位宽，命题 E2 保证各指定没有冲突。其余标记可取各自值域内的零值，包括合法的零包字节。因此全部入口等式同时成立。\(\square\)

命题 E4 只证明值等式的代数相容性；真实资源与访问条件仍取决于[外部假设](#外部假设与初态边界)。入口构造及有限内存规则的实现对应见[工程模块与迁移](路径合并FFI.md#工程模块与迁移)。
