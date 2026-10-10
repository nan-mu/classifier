# 共同数学基础：符号值、关系与有限执行历史

本文建立指令分析所需的共同数学对象，并证明符号求解、关系更新及有预算展开的基本性质。具体指令的数值函数见 [RV32IMC 值函数](rv32imc-expr-value-functions.md)和 [eBPF 值函数](ebpf-expr-value-functions.md)；入口赋值见 [RV32 初态](rv32-initial-expr.zh.md)。

全文区分三种陈述：定义规定模型对象；命题给出从定义推出的结论；假设说明结论成立所需的外部条件。Predicate 的完整观察语义、资源绑定的可靠性和跨指令集行为等价性尚未确定，不能由本文的局部性质直接推出。

## 1. 记号与位向量

令 \(\mathbb N=\{0,1,2,\ldots\}\)。对集合 \(A\)，定义

\[
A^\ast=\bigcup_{m\in\mathbb N}A^m,
\qquad
\mathscr F(A)=\{B\subseteq A:|B|<\infty\}.
\]

\(A^\ast\) 是有限序列集合，\(\mathscr F(A)\) 是有限子集集合；空序列记为 \(\varepsilon\)。\(\bigsqcup\) 表示保留类型标签的不交并。

对正整数 \(q\)，定义位向量的非负整数表示：

\[
\mathbb B_q=\{0,1,\ldots,2^q-1\},
\qquad
M_q(z)=z\bmod 2^q\quad(z\in\mathbb Z).
\]

余数总取 \(\mathbb B_q\) 中的代表。有符号与无符号解释分别为

\[
u_q(a)=a,
\qquad
s_q(a)=
\begin{cases}
a,&a<2^{q-1},\\
a-2^q,&a\ge 2^{q-1}.
\end{cases}
\]

寄存器与符号项的位宽集合为 \(W=\{32,64\}\)。辅助数值函数可使用其他正整数位宽，但不因此增加寄存器或符号项的类别。

全文以 \(i\) 表示指令，\(p\) 表示谓词，\(e\) 表示寄存器关系，\(r\) 表示寄存器标记，\(t\) 表示符号项。\(j\) 表示位置或序列索引，\(\iota,\delta\) 表示立即数或偏移，\(\pi,t_\pi\) 分别表示程序计数器的数值与符号项。

**引理 1（模归一化）。** 对任意整数 \(z,k\)，有

\[
M_q(M_q(z))=M_q(z),
\qquad M_q(z+k2^q)=M_q(z).
\]

**证明。** 两个等式的左右两侧属于同一模 \(2^q\) 的剩余类，且都取该类唯一的非负代表。\(\square\)

## 2. 原始指令与执行历史

### 2.1 输入

令原始指令编码宽度集合为 \(W_{\mathrm{Insn}}=\{16,32,64\}\)，定义

\[
\mathrm{Insn}
=\bigsqcup_{w\in W_{\mathrm{Insn}}}
\bigl(\{w\}\times\mathbb B_w\bigr),
\qquad
\mathbf I=(i_0,\ldots,i_{m-1})\in\mathrm{Insn}^\ast.
\]

原始指令携带编码位宽及位模式。其语义解释可使用已解码指令对象；二者不能与序列位置混同。指令编码宽度与寄存器位宽是不同的概念。

### 2.2 历史与观察

设 \(\mathrm{Predicate}\) 为观察域。比较、返回与 helper 调用观察的类型、解释和累积规则集中定义于[Predicate 文档](predicates.md)；访问与完整外部调用契约仍待定义。在比较两种架构的行为前，还需指定观察的选取与对应。

一项历史记录属于

\[
\mathrm{Insn}\times\mathscr F(\mathrm{Predicate})
\times\mathscr F(\mathrm{Expr})
\times\mathscr F(\mathrm{Inst}_{\mathrm{next}}).
\]

四个分量依次为原始指令、谓词集合、寄存器关系集合和后继信息集合。后继信息在第 13 节定义。

一条历史是这些记录组成的有限序列，成功输出为有限历史集合：

\[
\boxed{
\mathcal H\in\mathscr F\!\left(
\left(\mathrm{Insn}\times\mathscr F(\mathrm{Predicate})
\times\mathscr F(\mathrm{Expr})
\times\mathscr F(\mathrm{Inst}_{\mathrm{next}})\right)^\ast
\right).
}
\]

序列保留执行顺序，集合不引入顺序。第 17 节的投影采用每条指令执行后的关系与谓词，因而保留最后一次返回观察；第 13 节的普通执行节点采用执行前快照。

Expr 描述中间寄存器关系。不同架构可以产生不同 Expr；这些中间关系的相等不是跨架构行为等价性的定义。

## 3. 寄存器标记

寄存器类别、标识集合、位宽组合及别名规则统一在[寄存器抽象与 Expr 分类规则](registers.md)第 1 节定义。本文采用其中的 \(\mathrm{Reg}_{k,w}\) 与 \(\mathrm{Reg}_w\)，并保持项位宽集合 \(W=\{32,64\}\)。

Real、Stack、Map、Packet 是四个不交类别。虚拟包寄存器以 32 位项承载一个字节，其合法值域为 \(\mathbb B_8\)。指令分类与源项要求见该文第 2 节，四类 Expr 规则见第 3—6 节；单凭地址表达式不能推出资源绑定存在、唯一或访问有效。

## 4. 常元、变元与符号项

### 4.1 叶子与运算符

对 \(w\in W\)，给定变元名称集合 \(\Xi_w\)，定义

\[
\mathrm{Const}_w=\{C_w(c):c\in\mathbb B_w\},
\qquad
\mathrm{Var}_w=\{V_w(\xi):\xi\in\Xi_w\}
\sqcup\{R_w^{\varepsilon}(r):r\in\mathrm{Reg}_{\mathrm{Real},w},\ \varepsilon\in\mathcal I_{\mathrm{call}}\}.
\]

常元表示确定值，\(V_w(\xi)\) 表示固定的符号输入；\(R_w^{\varepsilon}(r)\) 表示指定调用返回时刻由真实寄存器承载的值，见[lookup 关联规则](registers.md#52-map-lookup-的返回位置与虚拟寄存器)。两类变元不交，后者的身份包括事件及完整寄存器标记。同名但位宽不同的变元是不同元素。变元不查询后续可变的寄存器；未定义寄存器也不自动对应一个新变元。

对 \(n\in\mathbb N_{>0}\) 及 \(w_1,\ldots,w_n,w\in W\)，形式运算符及其数值解释满足

\[
f\in\mathrm{Op}_{(w_1,\ldots,w_n)\to w},
\qquad
\widehat f:\prod_{j=1}^{n}\mathbb B_{w_j}\to\mathbb B_w.
\]

**假设 A（纯数值解释）。** 本文讨论的每个 \(\widehat f\) 都是确定的全函数。指令立即数、运算宽度或固定字节序可作为运算符参数。未给定的外部资源或调用结果不满足这一假设，不能仅凭常元实参被解释成确定返回值。

### 4.2 有限项与类型

\(\mathrm{Term}_w\) 是由以下规则生成的有限项集合：

\[
t_w::=C_w(c)\mid V_w(\xi)\mid R_w^{\varepsilon}(r)\mid f(t_{w_1},\ldots,t_{w_n}).
\]

函数应用必须与输入、输出位宽签名一致。常元、变元是叶子，应用记录运算结构。8 位或 16 位的辅助数值步骤可合成为输出为 32 位或 64 位的运算符，无需引入新的 Term 位宽。

## 5. 求值与 solve

### 5.1 变元出现集合

令 \(\mathrm{Var}=\bigsqcup_{w\in W}\mathrm{Var}_w\)，定义

\[
FV(C_w(c))=\varnothing,
\qquad FV(V_w(\xi))=\{V_w(\xi)\},
\qquad
FV(f(t_1,\ldots,t_n))=\bigcup_{j=1}^{n}FV(t_j).
\]

真实寄存器变元同样满足 \(FV(R_w^{\varepsilon}(r))=\{R_w^{\varepsilon}(r)\}\)，其解释为 \(\nu_w(R_w^{\varepsilon}(r))\)，由相应调用结果契约约束，而不是取后续寄存器赋值 \(\rho_w(r)\)。

**引理 2（有限性）。** 每个项的 \(FV\) 都是有限集合。

**证明。** 对项结构归纳。常元对应空集，变元对应单元素集合；有限个子项的有限集合之并仍有限。\(\square\)

### 5.2 闭项求值

项 \(t\) 满足 \(FV(t)=\varnothing\) 时称为闭项。定义

\[
\operatorname{eval}_w:
\{t\in\mathrm{Term}_w:FV(t)=\varnothing\}\to\mathbb B_w,
\]

\[
\operatorname{eval}_w(C_w(c))=c,
\]

\[
\operatorname{eval}_w(f(t_1,\ldots,t_n))
=\widehat f\bigl(\operatorname{eval}_{w_1}(t_1),\ldots,
\operatorname{eval}_{w_n}(t_n)\bigr).
\]

**命题 3（闭项求值良定义）。** 在假设 A 下，每个闭项具有唯一的同位宽求值结果。

**证明。** 闭项中不出现变元，故其叶子均为常元。对项结构归纳，子项的结果唯一且满足输入位宽；\(\widehat f\) 的确定性、全定义性与输出签名给出唯一的同位宽结果。项结构有限，递归求值结束。\(\square\)

本节的全求值只适用于假设 A 的纯数值子域。含未解释资源或调用运算的项采用部分求值；其闭项未必具有确定数值，相应的 solve 扩展见[Predicate 文档第 2.3 节](predicates.md#23-可判定与未知)。

### 5.3 整项求解

定义

\[
\boxed{
\operatorname{solve}_w(t)=
\begin{cases}
C_w(\operatorname{eval}_w(t)),&FV(t)=\varnothing,\\
t,&FV(t)\ne\varnothing.
\end{cases}}
\]

符号提升为

\[
f^\star(t_1,\ldots,t_n)
=\operatorname{solve}_w(f(t_1,\ldots,t_n)).
\]

已命名数值函数 \(G\) 的形式运算符记为 \(f_G\)，令 \(G^\star=f_G^\star\)。数值函数与符号提升因而分别记作 ADD、\(\mathrm{ADD}^\star\) 等。

solve 只折叠整个闭项。有变元时不折叠其中的闭子项，也不使用相消等代数恒等式。所有源项表示执行前的值；多目标更新使用同一组源项，随后覆写寄存器不改变已经构成的项。

## 6. Expr 与关系解释

### 6.1 同位宽关系

令 \(\mathbb T=\{\mathsf{true},\mathsf{false}\}\)。每个 \(\bowtie\in\mathrm{Rel}_w\) 具有解释

\[
\widehat{\bowtie}:\mathbb B_w\times\mathbb B_w\to\mathbb T.
\]

定义

\[
\boxed{
\mathrm{Expr}=\bigsqcup_{w\in W}
\bigl(\mathrm{Reg}_w\times\mathrm{Rel}_w\times\mathrm{Term}_w\bigr).
}
\]

\(e=(r_w,\bowtie,t_w)\) 简写为 \(r_w\bowtie t_w\)。普通等式给出完整值定义；其他关系给出约束。Expr 的关系标记不自动成为 Predicate。

### 6.2 比较与截取比较

关系符号包括

\[
=,\ne,<_{u},\le_u,>_u,\ge_u,<_{s},\le_s,>_s,\ge_s.
\]

对整数关系 \(\diamond\in\{=,\ne,<,\le,>,\ge\}\)，规定

\[
\widehat{\diamond_u}(a,b)\iff u_w(a)\diamond u_w(b),
\qquad
\widehat{\diamond_s}(a,b)\iff s_w(a)\diamond s_w(b).
\]

等式与非等式无需区分有符号、无符号解释。对 \(1\le q\le w\)，低 \(q\) 位比较定义为

\[
\widehat{\diamond_u^{[q]}}(a,b)
\iff M_q(a)\diamond M_q(b),
\qquad
\widehat{\diamond_s^{[q]}}(a,b)
\iff s_q(M_q(a))\diamond s_q(M_q(b)).
\]

\(q=w\) 时省略上标；低位等式记作 \(=^{[q]}\)、\(\ne^{[q]}\)。

位测试与补关系定义为

\[
\widehat{\mathrm{BITSNZ}^{[q]}}(a,b)
\iff\mathrm{AND}_q(M_q(a),M_q(b))\ne0,
\]

\[
\widehat{\mathrm{BITSZ}^{[q]}}(a,b)
\iff\mathrm{AND}_q(M_q(a),M_q(b))=0,
\qquad
\widehat{\overline{\bowtie}}(a,b)
=\neg\widehat{\bowtie}(a,b).
\]

例如 \(\overline{<_s}=\ge_s\)。对确定的 \(a,b\)，某关系与其补关系恰有一个成立。

### 6.3 关系的求解

\[
\operatorname{solve}_{\mathrm{Expr}}(r_w,\bowtie,t_w)
=(r_w,\bowtie,\operatorname{solve}_w(t_w)).
\]

这个操作只求解右侧项。没有寄存器值解释时，不能仅凭左侧标记判定关系真假。

## 7. 共同数值函数

本节给出纯数值函数的定义。其符号提升 \(G^\star\) 按第 5 节定义。未另行说明时，数值参数 a、b 属于 \(\mathbb B_w\)，w 属于 W。

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

对位起点 \(o\in\mathbb N\)、位段长度 \(\ell\in\mathbb N_{>0}\)，满足 \(o+\ell\le v\)，定义

\[
\mathrm{EXTRACT}_{o,\ell}^{(v)}:
\mathbb B_v\to\mathbb B_\ell,
\qquad
\mathrm{EXTRACT}_{o,\ell}^{(v)}(a)=
M_\ell\left(\left\lfloor a/2^o\right\rfloor\right).
\]

对 \(v,q\in\mathbb N_{>0}\)、\(w\in W\)，满足 \(q\le\min(v,w)\)，定义

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

## 8. 虚拟单元与真实寄存器的关系

### 8.1 同位宽传值

若虚拟单元 \(r_v\in\mathrm{Reg}_w\) 已有完整等式 \(r_v=t\)，读取该单元到真实寄存器 \(r_d\) 的局部关系为 \(r_d=t\)。反向写入则使用源真实寄存器的旧项，产生 \(r_v=t_s\)。

目标必须是实际绑定的一个单元，且源值满足目标类别的值域约束。不同类别标记不因公式相同而成为同一目标；源项也不是对随后可变寄存器的引用。Stack/Map 字段与 Packet 字节的访问分别采用[寄存器分类规则](registers.md)第 4—6 节，不能将整个宽值直接赋给一个包字节。

### 8.2 宽度转换与局部约束

对 \(\mathrm{SW}(\alpha)=t_{32}\)，零扩展读取到 64 位真实寄存器可写为

\[
\mathrm{Real}_{64}(\gamma)=Z_{32\to64}^{(32),\star}(t_{32}).
\]

局部约束 \(\mathrm{SW}(\alpha)=^{[8]}t_{32}\) 只确定低 8 位。

**命题 4（局部关系不确定完整值）。** 固定低 \(q\) 位且 \(q<w\) 时，恰有 \(2^{w-q}\) 个 \(w\) 位值满足该约束。

**证明。** 设固定低位为 \(b\in\mathbb B_q\)。全部解恰为 \(a=b+2^q h\)，其中 \(h\in\mathbb B_{w-q}\)。这些值两两不同，并穷尽所有满足 \(M_q(a)=b\) 的值。\(\square\)

因此，局部等式不能替代完整值等式。局部写入如何保留其他位，须由具体指令的值函数规定。

## 9. 按局部数学效果分类

设某个指令实例产生局部效果 \((\mathcal E_i,\mathcal P_i)\)。可区分：

- 仅产生 Expr：寄存器赋值、算术结果或链接值。
- 仅产生 Predicate：条件观察或对已有返回项的观察。
- 同时产生二者：值关系与访问、调用等观察共同发生。
- 二者均为空：只改变后继位置的跳转或观察范围外的操作。
- 局部规则无定义：不产生成功候选。

分类针对指令实例及选定观察范围。它不由助记符唯一决定：带链接值的跳转与无链接跳转不同；普通间接跳转与已绑定的最外层返回也不同。

后继位置不作为额外语义状态。若某实例明确产生 PC 等式，就按实际局部关系分类。栈和 Map 的访问观察形式尚未完整定义；数值传值公式不能代替这些观察。

## 10. solve 的基本性质

### 10.1 幂等性

**命题 5。** 对所有 \(t\in\mathrm{Term}_w\)，

\[
\operatorname{solve}_w(\operatorname{solve}_w(t))
=\operatorname{solve}_w(t).
\]

**证明。** 若 \(FV(t)=\varnothing\)，第一次得到常元 \(C_w(c)\)，其求值仍为 \(c\)，第二次不变。若 \(FV(t)\ne\varnothing\)，两次都返回 \(t\)。\(\square\)

### 10.2 解释保持性

给定变元赋值族 \(\nu_w:\mathrm{Var}_w\to\mathbb B_w\)，定义

\[
\left[\!\left[ C_w(c)\right]\!\right]_\nu=c,
\qquad
\left[\!\left[ V_w(\xi)\right]\!\right]_\nu=\nu_w(V_w(\xi)),
\]

\[
\left[\!\left[ f(t_1,\ldots,t_n)\right]\!\right]_\nu
=\widehat f(\left[\!\left[ t_1\right]\!\right]_\nu,\ldots,
\left[\!\left[ t_n\right]\!\right]_\nu).
\]

**引理 6。** 若 \(FV(t)=\varnothing\)，则
\(\left[\!\left[ t\right]\!\right]_\nu=\operatorname{eval}_w(t)\)，且结果与 \(\nu\) 无关。

**证明。** 对闭项结构归纳。常元情形直接成立；应用情形对每个子项使用归纳假设，再代入同一个 \(\widehat f\)。\(\square\)

**命题 7。** 对任意项与赋值，

\[
\left[\!\left[\operatorname{solve}_w(t)\right]\!\right]_\nu
=\left[\!\left[ t\right]\!\right]_\nu.
\]

**证明。** 闭项情形由引理 6 与常元解释得到；非闭项情形由 solve 返回原项得到。\(\square\)

### 10.3 Expr 的解释保持性

给定寄存器赋值族 \(\rho_w:\mathrm{Reg}_w\to\mathbb B_w\)，定义

\[
\left[\!\left[(r_w,\bowtie,t_w)\right]\!\right]_{\rho,\nu}
=\widehat{\bowtie}(\rho_w(r_w),\left[\!\left[ t_w\right]\!\right]_\nu).
\]

**推论 8。**

\[
\left[\!\left[\operatorname{solve}_{\mathrm{Expr}}(e)\right]\!\right]_{\rho,\nu}
=\left[\!\left[ e\right]\!\right]_{\rho,\nu}.
\]

**证明。** 左侧寄存器与关系符号不变，右侧解释由命题 7 保持。\(\square\)

\(\rho,\nu\) 是关系的数学解释，不是新增的运行状态。此处证明单个关系的解释保持性，不证明两个架构的中间关系集合相同。

## 11. 定义域与未决假设

指令值规则是部分函数。必需的完整值等式缺失、绑定不唯一、非法指令或模型未包含的行为，均使相应规则无定义。无定义与成功返回空局部集合具有不同含义。

以下问题保留为独立的数学任务：

1. 访问和外部调用应生成哪些 Predicate，以及如何解释和合并。
2. 地址、程序位置与虚拟单元之间的绑定及其唯一性、资源有效性。
3. 外部调用结果、寄存器失效与调用返回配对。
4. 两种架构之间的入口对应、观察对应和最终行为等价性。

后文的结构与终止结论均相对于给定的局部规则成立；它们不消除这些假设。

## 12. 语义状态与按键更新

### 12.1 状态

定义

\[
\boxed{\mathrm{State}
=\mathscr F(\mathrm{Expr})\times\mathscr F(\mathrm{Predicate}),
\qquad \sigma=(\mathcal E,\mathcal P).}
\]

\(\mathcal E\) 是当前关系集合，\(\mathcal P\) 是当前观察集合。位置、节点引用、方向和预算是结构信息。既定路径条件或观察若为后续语义所需，须在这两部分中表达。

Predicate 采用结构相等下的集合语义，不在该分量内部记录重复次数或事件顺序。执行路径及逐次快照保留步骤顺序，但不能仅由观察集合的变化恢复重复事件；需要事件轨迹时还须另行定义，见[Predicate 文档第 5 节](predicates.md#5-示例与历史顺序)。

### 12.2 关系键与覆写

令

\[
\operatorname{key}(r,\bowtie,t)=(r,\bowtie),
\qquad K(E)=\{\operatorname{key}(e):e\in E\}.
\]

关系符号包含低位修饰。集合 \(E\) 有效，当且仅当同键关系唯一：

\[
e,e'\in E\land\operatorname{key}(e)=\operatorname{key}(e')
\Longrightarrow e=e'.
\]

对有效集合定义

\[
\boxed{
\operatorname{updateExpr}(E,F)=E\times F
=\{e\in E:\operatorname{key}(e)\notin K(F)\}\cup F.
}
\]

此处 \(\times\) 表示覆写，其余类型签名中的 \(\times\) 表示笛卡尔积。

**命题 9（键唯一性保持）。** 有效的 \(E,F\) 覆写后仍有效；新集合在 \(K(F)\) 上取 \(F\) 的值，在其余旧键上取 \(E\) 的值。

**证明。** 旧集合中属于 \(K(F)\) 的项全部被移除，因此保留的旧项与新项没有公共键。两部分内部各自键唯一，结论成立。\(\square\)

**推论 10。** 对有效的 \(E,F,H\)，

\[
E\times\varnothing=E,
\qquad (E\times F)\times F=E\times F,
\qquad (E\times F)\times H=E\times(F\times H).
\]

**证明。** 对任一键分别考察是否出现于 \(H\)、\(F\)、\(E\)：存在时总取最右侧集合中的项。空集、重复覆写与括号位置均不改变这一选择。\(\square\)

覆写普通等式不会删除其他关系键。例如旧不等式可以留下，但键唯一性不证明它仍对更新后的寄存器值成立。

### 12.3 Predicate 合并

对[Predicate 文档](predicates.md)定义的比较、返回与 helper 调用观察，合并为结构相等下的集合并集：\(\operatorname{mergePredicate}(\mathcal P,\mathcal P_i)=\mathcal P\cup\mathcal P_i\)。局部状态更新定义为

\[
\sigma'=
\bigl(\operatorname{updateExpr}(\mathcal E,\mathcal E_i),
\operatorname{mergePredicate}(\mathcal P,\mathcal P_i)\bigr).
\]

该合并满足有限性、单位元、幂等、交换与结合性质，证明见[Predicate 文档第 4 节](predicates.md#4-累积与状态更新)。合并不判断路径条件是否可满足；扩展观察的合并规则仍须独立规定。各候选都从同一个输入 \(\sigma\) 更新，互不使用另一候选的结果。

## 13. 位置、节点与后继

### 13.1 位置

对长度为 \(m\) 的输入定义

\[
\mathrm{Pos}_{\mathbf I}=\{j\in\mathbb N:j<m\},
\qquad
\mathrm{Loc}_{\mathbf I}=\mathrm{Pos}_{\mathbf I}\sqcup\{\mathrm{Exit}\}.
\]

Exit 是正常结束标记，不是指令。未知目标、无定义行为和未完成推理均不能用 Exit 代替。机器地址到序列位置的绑定由局部规则给定，尤其不能把变长指令的字节偏移等同于指令索引。

### 13.2 快照节点

定义节点内容

\[
N=(j,\sigma)=(j,(\mathcal E,\mathcal P))
\in\mathrm{Loc}_{\mathbf I}\times\mathrm{State}.
\]

位置投影记为 \(\operatorname{loc}(N)=j\)，状态投影记为 \(\operatorname{st}(N)=\sigma\)。普通位置保存该指令执行前的快照，Exit 保存返回后的最终快照。快照建立后不变。节点引用 \(\mathrm{NodeId}=\mathbb N\) 与节点内容分开；内容相同的两次到达仍可有不同引用。

### 13.3 方向与连接

\[
\mathrm{Direction}=\{\mathrm{Only},\mathrm{Taken},\mathrm{NotTaken}\},
\qquad
\mathrm{Inst}_{\mathrm{next}}=\mathrm{Direction}\times\mathrm{NodeId}.
\]

Only 表示唯一后继；Taken、NotTaken 表示条件成立与不成立的方向。连接为 \((\eta,d,\zeta)\)。即使两侧到达同一程序位置，也保留各自的方向及状态快照。

## 14. 执行路径与展开图

有限展开图为

\[
G=(\mathrm{Nodes},\mathrm{Edges},\mathrm{root}),
\qquad\mathrm{root}=0.
\]

Nodes 是按创建顺序编号的有限节点序列。路径为

\[
h=(\eta_0,d_0,\eta_1,\ldots,d_{n-1},\eta_n),
\qquad
(\eta_k,d_k,\eta_{k+1})\in\mathrm{Edges}.
\]

空路径只包含一个节点。正常结束路径从 root 到 Exit。

本模型每次到达均创建新节点，边总由已有引用指向新引用。它共享已经形成的执行前缀，但不合并分别到达的后缀。程序连接图可以有环，展开图则逐次记录循环到达。

## 15. 局部候选规则

设 \(\operatorname{Step}(\mathbf I,j,\sigma)\) 为给定局部规则，结果为以下二者之一：

\[
\operatorname{Reject}(a)
\quad\text{或}\quad
\operatorname{Candidates}\bigl((d_1,k_1,\mathcal E_1,\mathcal P_1),
\ldots,(d_c,k_c,\mathcal E_c,\mathcal P_c)\bigr).
\]

候选序列有限，\(k_l\in\mathrm{Loc}_{\mathbf I}\)。条件未知时通常保留 Taken、NotTaken 两侧；已确定条件只保留相应侧。正常返回产生 Exit 候选。空候选仅表示已证明没有可行后继。

**假设 B（局部终止与有效性）。** Step 与各局部合并均结束。成功候选的 Expr 键唯一，位宽正确，非 Exit 目标已绑定到输入位置。

**假设 C（语义覆盖）。** 局部规则不遗漏任何可行后继，且成功候选的值与观察正确。只能排除已证明不可行的方向；条件未知、求解失败与绑定失败不能作为不可行证明。

假设 B 用于有限展开与结构性质；假设 C 才能支持行为覆盖性。局部规则无定义时整次展开失败，不把输入末尾自动解释成正常返回。

## 16. 有预算展开与终止证明

### 16.1 展开配置

配置写作

\[
Q=(N,A,U,b),
\]

其中 \(N\) 为节点序列，\(A\) 为边集合，\(U\) 为按先进先出排列的待展开引用序列，\(b\in\mathbb N\) 为剩余预算。

给定 \(j_0\in\mathrm{Pos}_{\mathbf I}\)、入口状态 \(\sigma_0=(\mathcal E_0,\mathcal P_0)\) 和预算 \(B\)，要求 \(\mathcal E_0\) 键唯一。初配置为

\[
Q_0=\bigl([(j_0,\sigma_0)],\varnothing,[0],B\bigr).
\]

无效入口直接产生 \(\operatorname{Fail}(\mathrm{InvalidEntry})\)。

### 16.2 一步展开关系

按以下优先次序定义：

1. \(U=\varepsilon\)：得到 \(\operatorname{Complete}(G)\)。
2. \(U\ne\varepsilon\) 且 \(b=0\)：得到 \(\operatorname{Fail}(\mathrm{LimitExceeded})\)。
3. \(U=\eta\cdot U'\) 且 \(b>0\)：对 \(N[\eta]\) 的位置和状态应用 Step。

第三种情形若被拒绝，或任一候选的合并、目标有效性不成立，则得到 Fail，且不增加节点或边。若全部候选可接受，先从父快照计算各 \(\sigma_l'\)，再令

\[
\zeta_l=|N|+l-1\quad(1\le l\le c),
\]

\[
N'=N\cdot[(k_1,\sigma_1'),\ldots,(k_c,\sigma_c')],
\qquad
A'=A\cup\{(\eta,d_l,\zeta_l):1\le l\le c\},
\]

\[
U''=U'\cdot[\zeta_l:1\le l\le c,\ k_l\ne\mathrm{Exit}],
\qquad
Q'=(N',A',U'',b-1).
\]

Exit 不加入待展开序列。\(c=0\) 时只移除父引用并扣减预算。预算计量 Step 的应用次数，不是节点数，也不限制一次局部求解的内部工作量。

### 16.3 终止与有限性

**定理 11。** 在假设 B 下，有限预算展开至多应用 Step \(B\) 次，随后得到 Complete 或 Fail；产生的图有限。

**证明。** 对剩余预算 \(b\) 归纳。若待展开序列为空，直接结束；若非空且 \(b=0\)，也直接结束。其余情形只有一次局部处理。假设 B 保证该处理及有限候选合并结束；若成功，剩余预算变为 \(b-1\)，使用归纳假设。每次只增加有限个节点和边，至多发生 \(B\) 次，因此图有限。\(\square\)

恰好用完预算且待展开序列为空时仍 Complete。预算耗尽只能说明本次展开未完成，不能证明原程序不终止。

### 16.4 图结构不变量

**定理 12。** 每个成功扩展后的图均满足：根以外的节点恰有一个入边；所有边满足 \(\eta<\zeta\)；每个非 Exit 节点至多展开一次；节点快照不变。因此，图是一棵以 root 为根的有向树，特别地是 DAG。

**证明。** 初图只有根，性质成立。每次添加的目标引用都大于已有引用，每个新目标只由当前父节点连接一次，旧边不变。非 Exit 引用只在创建时入队一次，出队后不再入队；Exit 从不入队。快照仅在创建时给定，后续扩展只追加节点。对扩展次数归纳即得全部性质。若存在有向环，沿环引用严格增加后又回到原引用，矛盾。\(\square\)

结构无环不证明局部语义正确，也不限制原程序只能执行无环控制流。

## 17. 历史投影及其有限性

对 Complete 图定义正常结束引用集合

\[
\mathcal T_G=\{\eta:0\le\eta<|\mathrm{Nodes}|,\
\operatorname{loc}(\mathrm{Nodes}[\eta])=\mathrm{Exit}\}.
\]

设正常结束路径为 \(h=(\eta_0,d_0,\ldots,d_{n-1},\eta_n)\)。第 \(k\) 条边的源位置为 \(j_k\)，目标快照为 \((\mathcal E_{k+1},\mathcal P_{k+1})\)，令

\[
S_k=\bigl(\mathbf I[j_k],\mathcal P_{k+1},\mathcal E_{k+1},
\{(d_k,\eta_{k+1})\}\bigr),
\qquad
\operatorname{hist}(h)=(S_0,\ldots,S_{n-1}).
\]

最后的 Exit 不产生虚构指令项；返回观察已包含在最后一条真实指令的执行后快照中。

**命题 13。**

\[
\mathcal H_G=\{\operatorname{hist}(h):h\text{ 是从 root 到 Exit 的路径}\}
\]

是有限集合。

**证明。** 由定理 11、12，图有限且为树。每个 Exit 节点有唯一的根路径，故正常结束路径数量至多为节点数，各路径长度也有限。投影保持有限性。\(\square\)

节点引用必须在所属图内解释。非 Exit 的不可行叶不属于正常返回历史；Fail 图中的部分历史也不能作为完整输出。

在假设 C 下，可进一步按路径长度归纳：每条可行的正常结束执行均能逐步对应到候选边；若展开 Complete，则其完整路径出现在 \(\mathcal H_G\) 中。反向对应还要求候选不仅覆盖行为，而且每个候选都有相应行为见证。本文不在局部语义未给定时宣称这一等价成立。

## 18. 有界循环例证

取 \(w=32\)，给定入口等式 \(r=C_w(0)\)，考虑四个位置：位置 0 判断 \(r\ge_u C_w(3)\)，成立时到 3，否则到 1；位置 1 令 \(r\leftarrow\mathrm{ADD}_w^\star(r,C_w(1))\) 后到 2；位置 2 到 0；位置 3 正常返回并观察 \(r\)。此处右侧的 \(r\) 表示从执行前等式取得的项，分支与返回采用 Predicate 文档的观察规则。

这些 32 位常元的加法不发生回绕。四次判断分别读取常元 0、1、2、3；前三次走 NotTaken，第四次走 Taken。

若每次到达都按创建顺序编号，判断节点引用为 0、3、6、9，位置 3 的引用为 10，Exit 的引用为 11。Step 次数为

\[
4\text{ 次判断}+3\text{ 次加法}+3\text{ 次跳转}+1\text{ 次返回}=11.
\]

故 \(B=11\) 时完成，\(B=10\) 时返回位置尚未展开。重复的程序位置对应不同快照节点，既保留逐轮状态，又满足展开图无环。

预算耗尽且待展开序列非空时，结果为 LimitExceeded；局部规则无定义或合并失败则产生相应的 Fail。二者都不构成程序不终止的证明。循环摘要与含星号的路径表达式另见 [代数程序分析](algebraic-program-analysis.zh.md)；它们需要独立的语义与证明。
