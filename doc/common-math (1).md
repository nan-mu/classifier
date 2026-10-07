# 分类器共同数学定义

本文合并输入、输出历史结构、寄存器与符号运算定义，以及已约定的指令分类。具体指令的值函数分别见 [RV32IMC 值函数](rv32imc-expr-value-functions.md) 和 [eBPF 值函数](ebpf-expr-value-functions.md)。本文使用数学集合、有限序列与函数，不采用证明语言的数据类型或代码记法。

## 1. 记号与基本对象

### 1.1 集合与序列记号

对集合 \(A\)，定义其有限序列集合与有限子集集合：

\[
A^\ast=\bigcup_{m\in\mathbb N}A^m,
\qquad
\mathscr F(A)=\{B\subseteq A:\lvert B\rvert<\infty\}.
\]

这里 \(\mathbb N=\{0,1,2,\ldots\}\)，\(A^0\) 包含空序列。\(\times\) 表示笛卡尔积，\(\bigsqcup\) 表示保留类型标签的不交并。

### 1.2 统一名称

| 记号 | 含义 |
|---|---|
| \(\mathrm{Insn}\) | 原始指令集合 |
| \(\mathrm{Predicate}\) | 谓词集合，具体元素与解释待定 |
| \(\mathrm{Expr}\) | 寄存器关系标记集合 |
| \(\mathrm{Inst}_{\mathrm{next}}\) | 后继指令信息集合，具体内部结构待定 |
| \(\mathrm{Reg}_{k,w}\)、\(\mathrm{Reg}_w\) | 指定类型、位宽的寄存器集合；指定宽度的全部寄存器集合 |
| \(\mathrm{Const}_w\) | w 位常元集合 |
| \(\mathrm{Var}_w\) | w 位变元集合 |
| \(\mathrm{Term}_w\) | w 位符号项集合 |
| \(\mathrm{Op}_{(w_1,\ldots,w_n)\to w}\) | 指定输入、输出位宽的形式运算符集合 |
| \(\mathrm{Rel}_w\) | w 位值上的二元关系符号集合 |

这些名称分别在后文定义。全文不另用其他名称指代同一集合。

### 1.3 元素与参数记号

| 记号 | 含义与取值 |
|---|---|
| \(i\in\mathrm{Insn}\) | 一条指令，i 不作为数字索引或立即数 |
| \(p\in\mathrm{Predicate}\) | 一个谓词，p 不表示 PC 值 |
| \(e\in\mathrm{Expr}\) | 一个寄存器关系标记 |
| \(r_w\in\mathrm{Reg}_w\) | 一个 w 位寄存器标记 |
| \(t_w\in\mathrm{Term}_w\) | 一个 w 位符号项 |
| \(w\in W=\{32,64\}\) | 寄存器与符号项的位宽 |
| \(v,q\in\mathbb N_{>0}\) | 数值辅助函数的输入位宽、选定运算或截取位宽 |
| \(a,b,c\) | 位向量的数值；每个公式另行给出所属的 \(\mathbb B_q\) |
| \(\alpha\) | 寄存器标识，属于对应类型的 \(\mathcal I_k\) |
| \(\xi\) | 变元名称，属于对应位宽的 \(\Xi_w\) |
| \(f\) | 形式运算符 |
| \(\widehat f\) | f 对应的数值函数 |
| \(f^\star\) | f 对符号项的求解后应用 |
| \(G\)、\(G^\star\) | 已命名数值函数及其符号提升，如 ADD、Z |
| \(\bowtie\in\mathrm{Rel}_w\) | 一个关系符号 |
| \(\widehat{\bowtie}\) | 关系符号的数值解释 |
| \(j\) | 序列、函数参数或位位置的数字索引 |
| \(n\ge1\) | 运算符的参数个数 |
| \(m\in\mathbb N\) | 有限序列长度 |
| \(\varphi\) | 一个数学命题，用于指示函数 \(\mathbf1[\varphi]\) |

PC、SP 是寄存器标识。书写 w 位 PC 的数值与符号项时，分别使用 \(\pi\in\mathbb B_w\) 与 \(t_\pi\in\mathrm{Term}_w\)。具体指令中的已解码立即数、偏移使用 \(\iota,\delta\)，不占用 i。

## 2. 输入、输出与执行历史

### 2.1 原始指令

令指令编码宽度集合为

\[
W_{\mathrm{Insn}}=\{16,32,64\}.
\]

对正整数 q，令

\[
\mathbb B_q=\{0,1,\ldots,2^q-1\}.
\]

定义

\[
\mathrm{Insn}=
\bigsqcup_{w\in W_{\mathrm{Insn}}}
\bigl(\{w\}\times\mathbb B_w\bigr).
\]

一条指令携带编码位宽与对应位模式。这里的 \(W_{\mathrm{Insn}}\) 与寄存器位宽集合 W 是两个不同集合。

输入是原始指令的有限序列：

\[
\mathbf I=(i_0,\ldots,i_{m-1})\in\mathrm{Insn}^\ast.
\]

每个 \(i_j\) 是一条指令，j 才是序列位置。

### 2.2 历史项与输出集合

一项历史记录写作

\[
(i,\mathcal P,\mathcal E,\mathcal N)
\in
\mathrm{Insn}
\times\mathscr F(\mathrm{Predicate})
\times\mathscr F(\mathrm{Expr})
\times\mathscr F(\mathrm{Inst}_{\mathrm{next}}).
\]

其中 \(\mathcal P\) 是该项的谓词有限集合，\(\mathcal E\) 是 Expr 有限集合，\(\mathcal N\) 是后继信息有限集合。

一条执行历史 h 是这些历史项组成的有限序列。成功输出是多条历史组成的有限集合：

\[
\boxed{
\mathcal H\in
\mathscr F\!\left(
\left(
\mathrm{Insn}
\times\mathscr F(\mathrm{Predicate})
\times\mathscr F(\mathrm{Expr})
\times\mathscr F(\mathrm{Inst}_{\mathrm{next}})
\right)^\ast
\right).
}
\]

历史内部保留执行顺序；各项中的三个集合及多条历史组成的输出集合使用集合语义。后继信息采用弱链表形式，是历史项携带状态的一部分，不要求每项包含完整机器状态。

Predicate 承载最终语义一致比较所选取的谓词信息。Expr 记录中间寄存器关系；不同架构的这些中间标记允许不一致。具体谓词及最终选取范围继续待定。

## 3. 三类寄存器、六种变体

令

\[
K=\{\mathrm{Real},\mathrm{Stack},\mathrm{Map}\},
\qquad W=\{32,64\}.
\]

Real、Stack、Map 分别表示真实寄存器、虚拟栈寄存器、虚拟 Map 寄存器。给定各自的标识集合 \(\mathcal I_k\)，定义

\[
\mathrm{Reg}_{k,w}
=
\{(k,w,\alpha):\alpha\in\mathcal I_k\},
\qquad
\mathrm{Reg}_w=
\bigsqcup_{k\in K}\mathrm{Reg}_{k,w}.
\]

以下构造名称是这些三元组的统一书写形式：

| 类型 | 32 位标记 | 64 位标记 |
|---|---|---|
| 真实寄存器 | \(\mathrm{Real}_{32}(\alpha)\) | \(\mathrm{Real}_{64}(\alpha)\) |
| 虚拟栈寄存器 | \(\mathrm{SW}(\alpha)\) | \(\mathrm{SR}(\alpha)\) |
| 虚拟 Map 寄存器 | \(\mathrm{Map}_{32}(\alpha)\) | \(\mathrm{Map}_{64}(\alpha)\) |

例如，\(\mathrm{SW}(\alpha)\) 就是 \((\mathrm{Stack},32,\alpha)\)，\(\mathrm{SR}(\alpha)\) 就是 \((\mathrm{Stack},64,\alpha)\)。

PC、SP 和通用寄存器名称均属于 \(\mathcal I_{\mathrm{Real}}\)。这里不区分 RV32 与 eBPF，也不增加架构寄存器类别。具体指令中的寄存器编号及别名由对应指令定义解释。

## 4. 常元、变元与符号项

### 4.1 常元与变元

对 \(w\in W\)，给定位宽对应的变元名称集合 \(\Xi_w\)，定义

\[
\mathrm{Const}_w=\{C_w(c):c\in\mathbb B_w\},
\qquad
\mathrm{Var}_w=\{V_w(\xi):\xi\in\Xi_w\}.
\]

\(C_w(c)\) 表示确定的 w 位值。\(V_w(\xi)\) 表示一个固定的符号值名称，不是对可变寄存器的引用。同名但位宽不同的变元仍是不同元素。

没有定义的寄存器不记录为某个特殊变元或常元。指令所需源项没有定义时，解析拒绝。

### 4.2 运算符与值函数

对 \(w_1,\ldots,w_n,w\in W\)，给定

\[
f\in\mathrm{Op}_{(w_1,\ldots,w_n)\to w},
\qquad
\widehat f:
\prod_{j=1}^{n}\mathbb B_{w_j}\longrightarrow\mathbb B_w.
\]

f 是形式符号；\(\widehat f\) 是确定且全定义的数值函数。已解码立即数、操作宽度及已明确的字节序可以作为运算符的固定参数。

已经命名的数值函数 G，对应形式符号记作 \(f_G\)，满足 \(\widehat{f_G}=G\)。这里不会因为外部调用的参数都是常元，就假定其返回值是可由这些参数决定的纯数值函数。

### 4.3 符号项

定义 \(\mathrm{Term}_w\) 为下列有限构造项的集合：

\[
t_w::=
C_w(c)
\mid V_w(\xi)
\mid f(t_{w_1},\ldots,t_{w_n}).
\]

每个子项的宽度与 f 的输入签名一致。常元、变元是两类叶子，函数应用保存它们之间的运算结构。

辅助数值函数可处理 8、16 位等数值；这不增加 Reg 或 Term 的位宽种类。只有输入、输出签名均落在 W 内的函数才直接提升为 Term 运算符；涉及其他宽度的数值步骤可组成输出为 32/64 位的指令值函数。

## 5. 求值与 solve

### 5.1 变元出现集合

令全部变元的集合为

\[
\mathrm{Var}=\bigsqcup_{w\in W}\mathrm{Var}_w.
\]

定义变元出现集合函数

\[
FV:\bigsqcup_{w\in W}\mathrm{Term}_w
\longrightarrow\mathscr F(\mathrm{Var})
\]

及其递归规则：

\[
FV(C_w(c))=\varnothing,
\qquad
FV(V_w(\xi))=\{V_w(\xi)\},
\]

\[
FV(f(t_1,\ldots,t_n))=\bigcup_{j=1}^{n}FV(t_j).
\]

### 5.2 无变元项的求值

对 \(w\in W\)，定义

\[
\operatorname{eval}_w:
\{t\in\mathrm{Term}_w:FV(t)=\varnothing\}
\longrightarrow\mathbb B_w,
\]

\[
\operatorname{eval}_w(C_w(c))=c,
\]

\[
\operatorname{eval}_w(f(t_1,\ldots,t_n))
=
\widehat f\bigl(
\operatorname{eval}_{w_1}(t_1),\ldots,
\operatorname{eval}_{w_n}(t_n)
\bigr).
\]

### 5.3 solve 与符号提升

\[
\operatorname{solve}_w:\mathrm{Term}_w\longrightarrow\mathrm{Term}_w,
\]

\[
\boxed{
\operatorname{solve}_w(t)=
\begin{cases}
C_w(\operatorname{eval}_w(t))&FV(t)=\varnothing,\\
t&FV(t)\ne\varnothing.
\end{cases}}
\]

定义

\[
f^\star(t_1,\ldots,t_n)
=
\operatorname{solve}_w(f(t_1,\ldots,t_n)).
\]

对已命名数值函数 G，统一记

\[
G^\star=f_G^\star.
\]

因此 ADD、Z 等名称用于数值函数；\(\mathrm{ADD}^\star\)、\(Z^\star\) 表示对应符号项的构造与 solve。输入、输出宽度由函数签名确定。

含有任何变元时，整个项保持原样，不进行局部常元折叠。例如含变元的 \(f(t_1,t_2)\) 即使某个子项不含变元，solve 仍直接返回整个原项，也不应用相消等代数恒等式。

所有源项表示指令发生前的值。多目标指令的输出使用同一组源项，目标寄存器随后更新不会改变已有项。

## 6. Expr 与关系符号

### 6.1 Expr 的结构

令 \(\mathbb T=\{\mathsf{true},\mathsf{false}\}\)。每个关系符号 \(\bowtie\in\mathrm{Rel}_w\) 有解释

\[
\widehat{\bowtie}:\mathbb B_w\times\mathbb B_w\longrightarrow\mathbb T.
\]

定义

\[
\boxed{
\mathrm{Expr}
=
\bigsqcup_{w\in W}
\left(\mathrm{Reg}_w\times\mathrm{Rel}_w\times\mathrm{Term}_w\right).
}
\]

元素记作

\[
e=(r_w,\bowtie,t_w),
\qquad
\text{通常书写为 }r_w\bowtie t_w.
\]

左侧始终是寄存器标记，右侧始终是同位宽符号项。普通等式 \(r_w=t_w\) 可用于寄存器定义，其他关系用于条件或约束；关系标记本身不自动成为 Predicate。

### 6.2 等式与有符号、无符号比较

对正整数 q 和整数 z，定义

\[
M_q(z)=z\bmod2^q,
\]

其中余数取 \(\mathbb B_q\) 中的非负代表。对 \(a\in\mathbb B_q\)，定义

\[
u_q(a)=a,
\qquad
s_q(a)=
\begin{cases}
a&a<2^{q-1},\\
a-2^q&a\ge2^{q-1}.
\end{cases}
\]

关系符号包括

\[
=,\ne,<_{u},\le_u,>_u,\ge_u,<_{s},\le_s,>_s,\ge_s.
\]

令 \(\diamond\in\{=,\ne,<,\le,>,\ge\}\) 表示通常整数关系。对 \(a,b\in\mathbb B_w\)，有

\[
\widehat{\diamond_u}(a,b)
\iff u_w(a)\diamond u_w(b),
\qquad
\widehat{\diamond_s}(a,b)
\iff s_w(a)\diamond s_w(b).
\]

等式与不等式的 u/s 解释相同，省略该下标。

### 6.3 选定位宽的比较与位测试

对 \(1\le q\le w\)，定义

\[
\widehat{\diamond_u^{[q]}}(a,b)
\iff M_q(a)\diamond M_q(b),
\]

\[
\widehat{\diamond_s^{[q]}}(a,b)
\iff s_q(M_q(a))\diamond s_q(M_q(b)).
\]

q=w 时可以省略上标。等式、非等式仍省略 u/s，写作 \(=^{[q]}\)、\(\ne^{[q]}\)。这样可以在同一个 64 位 Reg 标记上表达低 32 位比较。

位与函数 AND 的数值定义见第 7 节。定义

\[
\widehat{\mathrm{BITSNZ}^{[q]}}(a,b)
\iff \mathrm{AND}_q(M_q(a),M_q(b))\ne0.
\]

BITSZ 是其补关系。一般关系的补符号记作 \(\overline{\bowtie}\)，其解释为

\[
\widehat{\overline{\bowtie}}(a,b)
=
\neg\widehat{\bowtie}(a,b).
\]

例如 \(\overline{<_s}=\ge_s\)。这里 \(\neg\) 表示布尔否定。

### 6.4 Expr 的 solve

定义

\[
\operatorname{solve}_{\mathrm{Expr}}:
\mathrm{Expr}\longrightarrow\mathrm{Expr},
\]

\[
\operatorname{solve}_{\mathrm{Expr}}(r_w,\bowtie,t_w)
=
(r_w,\bowtie,\operatorname{solve}_w(t_w)).
\]

它仅处理右侧项，不通过左侧 Reg 标记自行判定关系真假。

## 7. 共同数值函数

本节命名的函数均为数值函数 G；其符号提升 \(G^\star\) 按第 5 节定义。凡未另行说明，下列 a、b 属于 \(\mathbb B_w\)，w 属于 W。

### 7.1 算术

ADD、SUB、MULLO 的签名为 \(\mathbb B_w^2\to\mathbb B_w\)；NEG、ID 的签名为 \(\mathbb B_w\to\mathbb B_w\)。

\[
\mathrm{ADD}_w(a,b)=M_w(a+b),
\qquad
\mathrm{SUB}_w(a,b)=M_w(a-b),
\]

\[
\mathrm{MULLO}_w(a,b)=M_w(ab),
\qquad
\mathrm{NEG}_w(a)=M_w(-a),
\qquad
\mathrm{ID}_w(a)=a.
\]

### 7.2 按位逻辑

对 \(a\in\mathbb B_q\) 与 \(0\le j<q\)，定义第 j 位：

\[
\beta_j(a)=\left\lfloor a/2^j\right\rfloor\bmod2.
\]

AND、OR、XOR 的签名为 \(\mathbb B_q^2\to\mathbb B_q\)，其中 q 可为正整数辅助位宽：

\[
\mathrm{AND}_q(a,b)=
\sum_{j=0}^{q-1}\beta_j(a)\beta_j(b)2^j,
\]

\[
\mathrm{OR}_q(a,b)=
\sum_{j=0}^{q-1}\max(\beta_j(a),\beta_j(b))2^j,
\]

\[
\mathrm{XOR}_q(a,b)=
\sum_{j=0}^{q-1}((\beta_j(a)+\beta_j(b))\bmod2)2^j.
\]

\(\lfloor x\rfloor\) 是向下取整，max 取两个数中的较大者。

### 7.3 移位

对 \(w\in W\)，定义

\[
k_w(b)=b\bmod w,
\qquad a,b\in\mathbb B_w.
\]

SHL、LSHR、ASHR 的签名均为 \(\mathbb B_w^2\to\mathbb B_w\)：

\[
\mathrm{SHL}_w(a,b)=M_w(a2^{k_w(b)}),
\]

\[
\mathrm{LSHR}_w(a,b)=
\left\lfloor a/2^{k_w(b)}\right\rfloor,
\]

\[
\mathrm{ASHR}_w(a,b)=
M_w\left(\left\lfloor s_w(a)/2^{k_w(b)}\right\rfloor\right).
\]

算术右移使用向下取整；有符号除法的向零商另见第 7.6 节。

### 7.4 比较结果

对任意数学命题 \(\varphi\)，定义

\[
\mathbf1[\varphi]=
\begin{cases}1&\varphi\text{ 成立},\\0&\varphi\text{ 不成立}.\end{cases}
\]

LTU、LTS 的签名为 \(\mathbb B_w^2\to\mathbb B_w\)：

\[
\mathrm{LTU}_w(a,b)=\mathbf1[a<b],
\qquad
\mathrm{LTS}_w(a,b)=\mathbf1[s_w(a)<s_w(b)].
\]

### 7.5 截取与扩展

设输入位宽 v 为正整数，\(a\in\mathbb B_v\)。

对 \(1\le q\le v\)，定义

\[
\mathrm{LOW}_q^{(v)}:\mathbb B_v\to\mathbb B_q,
\qquad
\mathrm{LOW}_q^{(v)}(a)=M_q(a).
\]

对位起点 \(o\ge0\)、位段长度 \(\ell\ge1\)，满足 \(o+\ell\le v\)，定义

\[
\mathrm{EXTRACT}_{o,\ell}^{(v)}:
\mathbb B_v\to\mathbb B_\ell,
\qquad
\mathrm{EXTRACT}_{o,\ell}^{(v)}(a)=
M_\ell\left(\left\lfloor a/2^o\right\rfloor\right).
\]

对输出位宽 w 与截取宽度 q，满足 \(q\le\min(v,w)\)，定义

\[
Z_{q\to w}^{(v)},S_{q\to w}^{(v)}:
\mathbb B_v\longrightarrow\mathbb B_w,
\]

\[
Z_{q\to w}^{(v)}(a)=M_q(a),
\qquad
S_{q\to w}^{(v)}(a)=M_w(s_q(M_q(a))).
\]

Z 表示低 q 位的零扩展，S 表示低 q 位的符号扩展。输入位宽已经明确时，可省略上标 (v)。v 始终是数值位宽，不是虚拟寄存器名称。

### 7.6 向零商与余数

对整数 x，定义

\[
\operatorname{sgn}(x)=
\begin{cases}-1&x<0,\\0&x=0,\\1&x>0.\end{cases}
\]

TQ、TR 的签名为 \(\mathbb Z\times(\mathbb Z\setminus\{0\})\to\mathbb Z\)。对整数 x、y 且 y≠0：

\[
\mathrm{TQ}(x,y)=
\operatorname{sgn}(x)\operatorname{sgn}(y)
\left\lfloor\frac{|x|}{|y|}\right\rfloor,
\]

\[
\mathrm{TR}(x,y)=x-y\,\mathrm{TQ}(x,y).
\]

TQ 是向零截断的商，TR 是对应余数。\(|x|\) 表示绝对值。除零和溢出结果分别由具体指令值函数规定。

### 7.7 字节反转

对 \(q\in\{16,32,64\}\)、输入位宽 \(v\ge q\)，定义

\[
\mathrm{BSWAP}_q^{(v)}:\mathbb B_v\to\mathbb B_q,
\]

\[
\mathrm{BSWAP}_q^{(v)}(a)=
\sum_{j=0}^{q/8-1}
\mathrm{EXTRACT}_{8j,8}^{(v)}(a)
2^{8(q/8-1-j)}.
\]

这里只使用低 q 位，按 8 位字节反转其顺序。输入位宽明确时，可省略上标 (v)；写回目标宽度所需的扩展由具体指令值函数给出。

## 8. 虚拟寄存器关系直接写入 Expr

本节直接使用第 3 节的六种 Reg 标记，不增加虚拟传值函数或布局描述。

### 8.1 同位宽关系

下表每行的 t 属于对应的 \(\mathrm{Term}_w\)。\(\alpha\) 属于该虚拟寄存器的标识集合；\(\gamma\in\mathcal I_{\mathrm{Real}}\) 是真实寄存器标识。

| 位宽 | 已有虚拟寄存器 Expr | 真实寄存器读取时生成的 Expr |
|---|---|---|
| 32 | \(\mathrm{SW}(\alpha)=t_{32}\) | \(\mathrm{Real}_{32}(\gamma)=t_{32}\) |
| 32 | \(\mathrm{Map}_{32}(\alpha)=t_{32}\) | \(\mathrm{Real}_{32}(\gamma)=t_{32}\) |
| 64 | \(\mathrm{SR}(\alpha)=t_{64}\) | \(\mathrm{Real}_{64}(\gamma)=t_{64}\) |
| 64 | \(\mathrm{Map}_{64}(\alpha)=t_{64}\) | \(\mathrm{Real}_{64}(\gamma)=t_{64}\) |

反向写入时，已有真实寄存器 Expr 的右侧项直接用于对应虚拟 Reg 标记：

| 位宽 | 已有真实寄存器 Expr | 写入时生成的虚拟寄存器 Expr |
|---|---|---|
| 32 | \(\mathrm{Real}_{32}(\gamma)=t_{32}\) | \(\mathrm{SW}(\alpha)=t_{32}\) 或 \(\mathrm{Map}_{32}(\alpha)=t_{32}\) |
| 64 | \(\mathrm{Real}_{64}(\gamma)=t_{64}\) | \(\mathrm{SR}(\alpha)=t_{64}\) 或 \(\mathrm{Map}_{64}(\alpha)=t_{64}\) |

“或”表示采用该指令实际对应的虚拟 Reg 标记，不同时向两个不同目标添加标记。右侧是发生前已经存在的符号项，不是对随后可被修改的寄存器名称进行引用。

### 8.2 宽度运算与局部关系

若指令需要扩展，使用第 7 节的数值函数提升。例如已有 \(\mathrm{SW}(\alpha)=t_{32}\) 时，可按指令要求记录

\[
\mathrm{Real}_{64}(\gamma)
=
Z_{32\to64}^{(32),\star}(t_{32}).
\]

只约束低 q 位时，使用第 6 节的关系。例如 \(t_{32}\in\mathrm{Term}_{32}\)：

\[
\mathrm{SW}(\alpha)=^{[8]}t_{32}.
\]

这只约束对应的低 8 位，不是 SW 整个 32 位值的定义。本文不从局部关系自动补出其余位的值。

栈或 Map 操作的 Expr 记录寄存器关系；其 Predicate 记录该操作对应的可观察语义，具体形式待定。这里没有额外的 READ、LOAD、STORE 传值层。

## 9. RV32 指令实例的分类

分类轴是 Expr、Predicate 的标记效果。后继指令的排列由 \(\mathrm{Inst}_{\mathrm{next}}\) 承载。

| 类别 | Expr 效果 | Predicate 效果 | 典型情况 |
|---|---|---|---|
| 仅更新 Expr | 添加或替换寄存器定义 | 无新增 p | 中间 ALU 运算、常元赋值、链接寄存器赋值 |
| 仅产生 Predicate | 无新增寄存器定义 | 添加条件或观察 p | 条件分支、程序返回时观察已有返回项 |
| Expr 与 Predicate | 更新真实或虚拟 Reg 的关系 | 同时描述对应语义 | 栈或 Map 读写；具有返回值或寄存器更新的外部调用 |
| 两者均无新增 | 无新增 e | 无新增 p | 不写链接寄存器的直接跳转；通常后继推进之外的 NOP、当前观察范围内的 FENCE |
| 拒绝处理 | 无成功输出 | 无成功输出 | 未定义输入、异常、非法编码、不支持的行为 |

表中的分类保留附件所采用的数据与观察标记口径，通常后继推进本身不作为分类轴。PC 仍是第 3 节定义的真实 Reg 标记；若某指令实例明确记录一个 PC 值 Expr，则按该实例实际增加的 Expr 归类。

第三类的职责分别为：

| 操作 | Expr 的职责 | Predicate 的职责 |
|---|---|---|
| 读取 SW、SR 或 Map | 为目标 Real 建立相应关系标记 | 表达本次虚拟寄存器读取的语义 |
| 写入 SW、SR 或 Map | 更新对应虚拟 Reg 的关系标记 | 表达本次虚拟寄存器写入的语义 |

因此，栈或 Map 读写归入 Expr 与 Predicate 类别。它们的数值关系直接写入 Expr，具体观察谓词仍待定。

分类按指令实例及已经识别的语义确定。例如：

- 写入链接值的内部 JAL，归入仅更新 Expr。
- 不写入链接值的直接 JAL，归入两者均无新增。
- 被识别为最外层返回的 JALR，需要产生返回 p。
- 若某个实例明确额外记录条件或 PC 的 Expr，则据其实际 Expr、Predicate 效果确定类别。

## 10. solve 的性质与解释

### 10.1 幂等性

对任意 \(w\in W\)、\(t\in\mathrm{Term}_w\)：

\[
\operatorname{solve}_w(\operatorname{solve}_w(t))
=
\operatorname{solve}_w(t).
\]

证明：若 \(FV(t)=\varnothing\)，第一次求解得到常元，第二次得到同一常元；若 \(FV(t)\ne\varnothing\)，两次均返回原项。

### 10.2 变元解释与项解释

给定变元赋值解释族

\[
\nu=(\nu_w)_{w\in W},
\qquad
\nu_w:\mathrm{Var}_w\longrightarrow\mathbb B_w.
\]

定义

\[
\llbracket C_w(c)\rrbracket_\nu=c,
\qquad
\llbracket V_w(\xi)\rrbracket_\nu=\nu_w(V_w(\xi)),
\]

\[
\llbracket f(t_1,\ldots,t_n)\rrbracket_\nu
=
\widehat f\bigl(
\llbracket t_1\rrbracket_\nu,\ldots,
\llbracket t_n\rrbracket_\nu
\bigr).
\]

于是对任意 t，有

\[
\llbracket\operatorname{solve}_w(t)\rrbracket_\nu
=
\llbracket t\rrbracket_\nu.
\]

证明：无变元时，eval 的递归规则与此解释相同；有变元时，solve 返回原项。

### 10.3 Expr 解释与保持性

给定寄存器值解释族

\[
\rho=(\rho_w)_{w\in W},
\qquad
\rho_w:\mathrm{Reg}_w\longrightarrow\mathbb B_w.
\]

对 \(e=(r_w,\bowtie,t_w)\)，定义其关系解释：

\[
\llbracket e\rrbracket_{\rho,\nu}
=
\widehat{\bowtie}\bigl(\rho_w(r_w),\llbracket t_w\rrbracket_\nu\bigr).
\]

由第 10.2 节得到

\[
\llbracket\operatorname{solve}_{\mathrm{Expr}}(e)\rrbracket_{\rho,\nu}
=
\llbracket e\rrbracket_{\rho,\nu}.
\]

\(\rho\) 与 \(\nu\) 是说明关系含义的数学赋值解释，不是本文件另建的执行状态或状态转移模型。这里保持的是单个 Expr 的关系解释，不是要求两个架构的全部中间 Expr 集合相同。

## 11. 约定边界

指令需要的源项未定义时，解析拒绝；不新增未定义 Reg、Var 或 Term。异常、非法指令和不支持的行为不生成成功结果。

外部调用结果、Map 或程序位置绑定、返回继续位置，由已确定的相应谓词或绑定提供符号项；本文件不从常元实参推导外部资源的返回值。

Predicate 的具体定义、寄存器初态、历史展开及控制流遍历仍待后续确定。本文件固定共同数学对象与符号运算规则。
