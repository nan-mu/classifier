# eBPF 的符号值函数与局部正确性

本文定义 eBPF 指令在共同 Expr 模型中的数值效果，并证明真实寄存器的位宽归一化、虚拟单元的局部覆盖与多目标更新性质。Reg 见[寄存器文档](registers.md)；Term、solve 和关系键覆写见 [共同数学基础](common-math.md)。

每条指令的操作、位宽、源形式和子类型视为给定参数。访问公式以唯一资源绑定为前提；外部调用结果和完整观察语义保留为未决定义。本文的局部性质不构成 eBPF 与 RV32IMC 的行为等价证明。

## 1. 指令参数与合法域

令 \(\mathcal I_B\) 为合法的已解码 eBPF 指令集合。二元算术使用运算宽度 \(q\in\{32,64\}\)，源为寄存器或 32 位立即数模式。立即数 \(\iota\in\mathbb B_{32}\) 的 64 位源项为

\[
t_{\mathrm{imm}}=C_{64}(M_{64}(s_{32}(\iota))).
\]

基本算术包括 ADD、SUB、MUL、DIV、SDIV、MOD、SMOD、OR、AND、XOR、LSH、RSH、ARSH，以及 NEG、MOV、MOVSX。MOVSX 的源宽度在 32 位形式中取 8、16，在 64 位形式中取 8、16、32。

字节序转换使用 \(q\in\{16,32,64\}\)。普通访问宽度为 8、16、32、64；符号扩展读取使用 8、16、32。原子数值操作使用 32 或 64 位单元，其 FETCH 参数决定是否同时写回旧值。

LDDW 的普通整数参数为 \(\iota_0,\iota_1\in\mathbb B_{32}\)，共同确定一个 64 位值。资源、代码位置等其他子类型需要额外绑定，不能仅从编号推导地址。

寄存器编号取 \(0\le j\le10\)，真实标记为 \(r_j\in\mathrm{Reg}_{\mathrm{Real},64}\)。对只读帧指针 \(r_{10}\) 的写入、非法参数与保留形式不属于相应值规则的定义域。

## 2. 值函数、覆写与重叠视图

### 2.1 部分函数

\[
\operatorname{value}_B:
\mathscr F(\mathrm{Expr})\times\mathcal I_B
\rightharpoonup\mathscr F(\mathrm{Expr}),
\qquad \operatorname{value}_B(E_g,i)=E_i.
\]

后文省略下标 B。\(E_g\) 是执行前关系集合；\(E_i\) 只记录局部新关系。输入与局部结果均要求键唯一，整体更新为 \(E_g'=E_g\times E_i\)。

虚拟访问的数值运算符同时依赖指令参数与绑定单元的位宽 \(w\)，严格记作 \(f_{i,w}\)；后文在位宽已明确时简写为 \(f_i\)。它不是跨越不同位宽仍保持同一签名的运算符。

源值须由唯一完整等式给定。不等式与低位等式不能替代完整值；未定义与成功空集不同。MOV 不读取目标旧值，其他规则只读取实际所需的源项。

### 2.2 键更新的含义

关系键为 \((r,\bowtie)\)，右侧项不是键。普通等式与低位等式、大小关系分别占据不同键，因此可以共存。例如

\[
E_g=\{r_1=C_{64}(3),\ r_1\le_u C_{64}(9)\},
\qquad E_i=\{r_1=C_{64}(7)\},
\]

\[
E_g\times E_i=\{r_1=C_{64}(7),\ r_1\le_u C_{64}(9)\}.
\]

保留旧关系是按键覆写的结果；它不提供旧约束对新值仍成立的一般证明。所有多目标规则同时读取旧 \(E_g\)，再一次覆写。

### 2.3 真实寄存器的 32 位视图

\(w_j\) 表示 \(r_j\) 的低 32 位视图，不是另一个寄存器身份。若 \(r_j=t_j\)，则

\[
\operatorname{read}(r_j)=t_j,
\qquad
\operatorname{read}(w_j)=\mathrm{LOW}_{32}^{(64),\star}(t_j).
\]

\(\operatorname{read}\) 仅是本式对既有等式右侧项的记法，不引入独立状态或资源读取规则。

ALU32 结果写回完整的 64 位真实标记。若数值结果为 \(t_{32}\)，则

\[
r_j=Z_{32\to64}^{(32),\star}(t_{32}).
\]

因而旧值无论为 \(\mathtt{0x10000}\) 还是 \(\mathtt{0x100000000}\)，32 位赋值 1 后都得到 \(r_j=C_{64}(1)\)。虚拟单元的局部写入采用另一种保留高位的公式。

## 3. 真实寄存器的数值函数

本节仅产生 Expr，不添加 Predicate；所有输出只写真实寄存器。

### 3.1 二元算术与位运算

当前 i 的运算宽度记作 q，只取 32 或 64。\(r_d\) 是目标，已有等式 \(r_d=t_d\) 提供旧值。

寄存器源由 \(E_g\) 中的 \(r_s=t_s\) 提供 \(t_{\mathrm{src}}=t_s\)。立即数源由 i 中的 32 位位模式 \(\iota\) 提供

\[
t_{\mathrm{src}}=C_{64}(M_{64}(s_{32}(\iota))).
\]

为当前 i 定义形式值运算符 \(f_i\)。其数值解释为
\(\widehat f_i:\mathbb B_{64}^2\to\mathbb B_{64}\)。
数值参数 a、b 分别对应目标旧值和源值，令

\[
A=M_q(a),\quad B=M_q(b),\quad k=B\bmod q.
\]

q 位非负结果作为同一整数放入 \(\mathbb B_{64}\)，所以 q=32 时高 32 位清零。

| 指令名称 | \(\widehat f_i(a,b)\) |
|---|---|
| ADD | \(M_q(A+B)\) |
| SUB | \(M_q(A-B)\) |
| MUL | \(M_q(AB)\) |
| OR | \(\mathrm{OR}_q(A,B)\) |
| AND | \(\mathrm{AND}_q(A,B)\) |
| XOR | \(\mathrm{XOR}_q(A,B)\) |
| LSH | \(M_q(A2^k)\) |
| RSH | \(\lfloor A/2^k\rfloor\) |
| ARSH | \(M_q(\lfloor s_q(A)/2^k\rfloor)\) |
| DIV | B=0 时为 0；否则为 \(\lfloor A/B\rfloor\) |
| MOD | B=0 时为 A；否则为 \(A-B\lfloor A/B\rfloor\) |

SDIV、SMOD 使用 \(x=s_q(A)\)、\(y=s_q(B)\)：

\[
\widehat f_i(a,b)=
\begin{cases}
0&y=0,\\
2^{q-1}&x=-2^{q-1}\land y=-1,\\
M_q(\mathrm{TQ}(x,y))&\text{其他情况},
\end{cases}
\qquad (i\text{ 为 SDIV}),
\]

\[
\widehat f_i(a,b)=
\begin{cases}
A&y=0,\\
0&x=-2^{q-1}\land y=-1,\\
M_q(\mathrm{TR}(x,y))&\text{其他情况},
\end{cases}
\qquad (i\text{ 为 SMOD}).
\]

TQ、TR 是共同定义中的向零商与余数。对上面每个名称和全部合法位宽、源形式，

\[
\boxed{
\operatorname{value}(E_g,i)
=\{r_d=f_i^\star(t_d,t_{\mathrm{src}})\}.
}
\]

\(f_i^\star\) 使用共同 solve：无变元时计算为常元，含变元时整个应用不变。

### 3.2 NEG、MOV、MOVSX

q 仍是当前指令的运算宽度。各单输入运算符的数值签名为 \(\mathbb B_{64}\to\mathbb B_{64}\)。

| 名称 | 从 \(E_g\) 和 i 取得的值项 | 数值公式 \(\widehat f_i(a)\) | \(E_i\) |
|---|---|---|---|
| NEG | 目标旧项 \(t_d\) | \(M_q(-M_q(a))\) | \(\{r_d=f_i^\star(t_d)\}\) |
| MOV，寄存器源 | 源项 \(t_s\)，不读目标旧值 | \(M_q(a)\) | \(\{r_d=f_i^\star(t_s)\}\) |
| MOV，立即数源 | i 中的 \(\iota\)，不读寄存器旧值 | 直接构造常元 | \(\{r_d=C_{64}(M_q(s_{32}(\iota)))\}\) |
| MOVSX | 源项 \(t_s\)；源宽度 \(\ell\) 来自 i | \(M_q(s_\ell(M_\ell(a)))\) | \(\{r_d=f_i^\star(t_s)\}\) |

MOVSX 的合法源宽度在第 1 节列明。32 位形式先符号扩展至 32 位，再清零真实寄存器高 32 位。

### 3.3 END、BSWAP

q 是转换宽度，取 16、32、64。D 是 END 指定的 LE 或 BE。H 是该数值模型的固定字节序参数。

由 \(E_g\) 取得 \(r_d=t_d\)。数值签名为 \(\mathbb B_{64}\to\mathbb B_{64}\)：

\[
\widehat f_i(a)=
\begin{cases}
M_q(a)&H=D,\\
\mathrm{BSWAP}^{(64)}_q(a)&H\ne D,
\end{cases}
\qquad (i\text{ 为 END}),
\]

\[
\widehat f_i(a)=\mathrm{BSWAP}^{(64)}_q(a),
\qquad (i\text{ 为 BSWAP}).
\]

共同 BSWAP 的 q 位非负结果在这里作为 64 位结果。两类指令均有

\[
\operatorname{value}(E_g,i)=\{r_d=f_i^\star(t_d)\}.
\]

### 3.4 LDDW 普通常元加载

i 的已配对槽位提供 \(\iota_0,\iota_1\in\mathbb B_{32}\)。无需读取目标旧值：

\[
\operatorname{value}(E_g,i)
=\{r_d=C_{64}(\iota_0+2^{32}\iota_1)\}.
\]

本节给出普通整数子类型；其他子类型的定义域见第 4、6 节。

## 4. 已绑定虚拟单元与多目标效果

**假设 BPF。** 当前指令与执行前关系唯一确定访问单元及其位宽，访问有效。以下公式描述已绑定单元的低位；一般地址、别名、跨单元访问和资源观察需要另外的语义。虚拟栈或 Map 访问可以同时产生观察，但本节仅规定数值关系。

本节的单元公式针对 Stack 与 Map。普通 Packet 读写采用[包寄存器分类规则](registers.md#6-虚拟包寄存器的分类规则)，取 \(w=64\)、\(m=1,2,4,8\)。LDX MEM 使用零扩展，MEMSX 按其合法宽度使用符号扩展；ST/STX 将源项的低 \(8m\) 位拆为字节，并同时覆写包标记。包原子访问与访问顺序不由这些普通字节规则定义。

### 4.1 只写真实寄存器：LDX、LOAD_ACQ、确定位置绑定的 LDDW

指令 i 与 \(E_g\) 必须唯一确定访问对应的虚拟标记 \(r_{\mathrm{virt}}\)。它是已定义的 SW、SR、Map32 或 Map64；位宽为 w，访问宽度 q 满足 \(q\le w\)。

\(E_g\) 中的 \(r_{\mathrm{virt}}=t_{\mathrm{virt}}\) 提供源项。指令与单元的唯一对应由假设 BPF 给定；未满足时值规则无定义。

| 指令 | \(E_i=\operatorname{value}(E_g,i)\) |
|---|---|
| LDX，MEM | \(\{r_d=Z_{q\to64}^{(w),\star}(t_{\mathrm{virt}})\}\) |
| LDX，MEMSX | \(\{r_d=S_{q\to64}^{(w),\star}(t_{\mathrm{virt}})\}\) |
| LOAD_ACQ | \(\{r_d=Z_{q\to64}^{(w),\star}(t_{\mathrm{virt}})\}\) |

MEMSX 只取 q=8、16、32。LOAD_ACQ 与普通零扩展读取有相同 Expr，不记录 acquire 或原子性。

LDDW 的资源位置或程序位置子类型也只写真实目标。由独立位置绑定 \(\Gamma_{\mathrm{pos}}(i)=t_{\mathrm{bind}}\in\mathrm{Term}_{64}\) 提供确定的位置项，则

\[
\operatorname{value}(E_g,i)=\{r_d=t_{\mathrm{bind}}\}.
\]

位置项由绑定参数提供，不从 Map 内容标记的等式取得，也不要求程序位置预先存入另一真实寄存器。若绑定只提供 32 位项，不能直接写入 64 位真实目标；在未给定转换语义时，该分支无定义。位置编号也不自行确定地址值。位置绑定的可靠性仍需独立证明。

### 4.2 只写虚拟栈寄存器：ST、STX、STORE_REL

i 与 \(E_g\) 对应到 SW 或 SR 时，左侧只写该虚拟栈标记 \(r_{\mathrm{virt}}\)。w 是标记位宽，q 是访问宽度，要求 \(q\le w\)。

ST 由立即数 \(\iota\) 取得
\(t_{\mathrm{src}}=C_{64}(M_{64}(s_{32}(\iota)))\)。
STX、STORE_REL 的 \(t_{\mathrm{src}}\) 由源寄存器已有等式取得。

当 q=w 时，不读取虚拟目标旧值。当前指令的数值签名和输出为

\[
\widehat f_i:\mathbb B_{64}\to\mathbb B_w,
\qquad \widehat f_i(b)=M_w(b),
\]

\[
\operatorname{value}(E_g,i)
=\{r_{\mathrm{virt}}=f_i^\star(t_{\mathrm{src}})\}.
\]

当 q<w 时，要求已有 \(r_{\mathrm{virt}}=t_{\mathrm{virt}}\)，定义

\[
\widehat f_i:\mathbb B_w\times\mathbb B_{64}\to\mathbb B_w,
\]

\[
\widehat f_i(a,b)
=2^q\left\lfloor a/2^q\right\rfloor+M_q(b),
\]

\[
\operatorname{value}(E_g,i)
=\{r_{\mathrm{virt}}=
f_i^\star(t_{\mathrm{virt}},t_{\mathrm{src}})\}.
\]

局部写入的数值公式替换标记对应单元的低 q 位，保留其余位。q<w 而目标旧值缺失时，不能确定完整新值，相应值函数无定义。

输出用普通 = 键，覆写旧完整值。不能只新增 \(=^{[q]}\) 关系，同时把旧完整等式当作写入后的值继续读取。

例如 SW 的已有 32 位值为 0x10000，执行 16 位 ST 写入 1，得到

\[
E_i=\{\mathrm{SW}(\alpha)=C_{32}(\mathtt{0x10001})\}.
\]

\(\alpha\) 是该 SW 的已有标识。这是虚拟单元的 16 位局部覆盖，不是 eBPF 32 位真实寄存器写回。

STORE_REL 与 STX 使用相同上述值函数，不记录 release 或原子性。

### 4.3 只写虚拟 Map 寄存器：ST、STX、STORE_REL

i 与 \(E_g\) 对应到 Map32 或 Map64 时，使用第 4.2 节完全相同的公式，将左侧取为该 Map 标记。位宽、源项取得方式和覆写规则相同。

栈与 Map 的区别在于目标标记类别，数值覆盖公式相同。

### 4.4 写虚拟寄存器，可能同时写真实寄存器：STX ATOMIC

本节给出虚拟栈或 Map 单元的一次数值效果。原子性、并发交错、锁、内存顺序与原子观察不属于这个数值投影。

q 为 32 或 64，虚拟目标标记位宽取 q。\(E_g\) 中的

\[
r_{\mathrm{virt}}=t_{\mathrm{virt}},\qquad
r_s=t_s,\qquad r_0=t_0
\]

提供所需值；只有 CMPXCHG 读取 R0。\(a\in\mathbb B_q\)、\(b,c\in\mathbb B_{64}\) 分别对应这些右侧项。

ADD、OR、AND、XOR 的数值签名为
\(\mathbb B_q\times\mathbb B_{64}\to\mathbb B_q\)：

| 运算 | \(\widehat f_i(a,b)\) |
|---|---|
| ADD | \(M_q(a+M_q(b))\) |
| OR | \(\mathrm{OR}_q(a,M_q(b))\) |
| AND | \(\mathrm{AND}_q(a,M_q(b))\) |
| XOR | \(\mathrm{XOR}_q(a,M_q(b))\) |

不带 FETCH 时，

\[
E_i=\{r_{\mathrm{virt}}=f_i^\star(t_{\mathrm{virt}},t_s)\}.
\]

带 FETCH 时，

\[
E_i=\{r_{\mathrm{virt}}=f_i^\star(t_{\mathrm{virt}},t_s),
\quad r_s=Z_{q\to64}^{(q),\star}(t_{\mathrm{virt}})\}.
\]

XCHG 的数值签名为 \(\mathbb B_{64}\to\mathbb B_q\)，且

\[
\widehat f_i(b)=M_q(b),
\]

\[
E_i=\{r_{\mathrm{virt}}=f_i^\star(t_s),
\quad r_s=Z_{q\to64}^{(q),\star}(t_{\mathrm{virt}})\}.
\]

CMPXCHG 的数值签名为
\(\mathbb B_q\times\mathbb B_{64}\times\mathbb B_{64}\to\mathbb B_q\)，且

\[
\widehat f_i(a,b,c)=
\begin{cases}
M_q(b)&a=M_q(c),\\
a&a\ne M_q(c),
\end{cases}
\]

\[
E_i=\{r_{\mathrm{virt}}=f_i^\star(t_{\mathrm{virt}},t_s,t_0),
\quad r_0=Z_{q\to64}^{(q),\star}(t_{\mathrm{virt}})\}.
\]

虚拟目标为 SW/SR 时归入栈输出，为 Map32/Map64 时归入 Map 输出。FETCH 决定附加的真实寄存器 Expr。所有结果由更新前的 \(E_g\) 同时计算。

### 4.5 外部 CALL 的结果规则待定

以 helper 或 BTF 标识指定的 CALL 具有外部调用语义。返回值和 Map 修改不能由一条通用算术规则确定。

调用前的 R0 项不是调用后的结果。没有外部结果语义时，该值分支无定义，不能解释为成功空集。

相应 \(\operatorname{value}(E_g,i)\) 分支须由独立的调用结果规则确定。纯数值运算的全定义假设不能确定外部资源的返回值。

## 5. 条件与控制效果

### 5.1 比较关系

条件跳转不产生新的寄存器值等式。设比较宽度 \(q\in\{32,64\}\)，第一源由旧完整等式提供。寄存器形式的第二源也由旧完整等式提供；立即数形式采用第 1 节的 \(t_{\mathrm{imm}}=C_{64}(M_{64}(s_{32}(\iota)))\)。在给定变元赋值下，两源解释为 \(a,b\in\mathbb B_{64}\)，再按比较宽度截取。其条件定义为

\[
\begin{aligned}
\mathrm{JEQ}&:\ M_q(a)=M_q(b),&
\mathrm{JNE}&:\ M_q(a)\ne M_q(b),\\
\mathrm{JGT}&:\ M_q(a)>M_q(b),&
\mathrm{JGE}&:\ M_q(a)\ge M_q(b),\\
\mathrm{JLT}&:\ M_q(a)<M_q(b),&
\mathrm{JLE}&:\ M_q(a)\le M_q(b),\\
\mathrm{JSGT}&:\ s_q(M_q(a))>s_q(M_q(b)),&
\mathrm{JSGE}&:\ s_q(M_q(a))\ge s_q(M_q(b)),\\
\mathrm{JSLT}&:\ s_q(M_q(a))<s_q(M_q(b)),&
\mathrm{JSLE}&:\ s_q(M_q(a))\le s_q(M_q(b)),\\
\mathrm{JSET}&:\ \mathrm{AND}_q(M_q(a),M_q(b))\ne0.
\end{aligned}
\]

这些数值条件可用共同的低位关系符号表达。Taken 使用原条件，NotTaken 使用其补；源项可求值时可以确定一侧，条件未确定时不能删去任何可能侧。[Predicate 文档](predicates.md)集中定义现有的 32 位比较观察与返回观察；本节的 32/64 位数值条件不自动建立对应的 Predicate，尤其 64 位比较观察仍须另行定义。

### 5.2 空值效果与返回

JA、程序内 CALL、条件跳转及 EXIT 的值效果为

\[
E_i=\varnothing,
\qquad E_g'=E_g.
\]

JA 改变后继；程序内 CALL 还需要调用、返回配对；EXIT 若表示最外层返回，则将已有的 64 位返回项按[Predicate 文档第 3.2 节](predicates.md#32-最外层返回)记录为值观察。空 Expr 效果不消除这些控制与观察要求，也不免除必需源值条件。

MAY_GOTO 的控制与观察规则尚未定义。本文不为顺序位置、跳转目标或调用建立额外 PC 值等式。

## 6. 定义域与未决语义

本模型以真实寄存器和已绑定的虚拟单元为值关系对象；包字节关系使用独立的寄存器文档所给规则。LDDW 的平台变量子类型、旧 LD ABS/IND 包读取和 CALLX 不在这里给出的成功规则中。

LOAD_ACQ 与 STORE_REL 的数值投影分别与普通读取、写入相同；STX ATOMIC 仅给出一次数值更新。并发交错、原子性和 acquire/release 排序观察均不包含在这些公式中，不能由数值相等推出完整行为相等。

以下情况使对应值分支无定义：非法参数、只读寄存器写入、必需完整等式缺失、虚拟单元不唯一、资源有效性未满足、局部写入缺少目标旧值、外部调用结果语义未给定。外部调用与资源位置的未知不能被成功空集代替。

## 7. 局部正确性与证明

### 7.1 ALU32 高位清零

**命题 B1。** 第 3 节的 32 位算术、移动与符号扩展结果均属于 \(\mathbb B_{32}\)，作为 64 位真实寄存器值时高 32 位为零。

**证明。** 各公式最终取 \(M_{32}\)，或直接给出介于 0 与 \(2^{32}-1\) 的数值。符号扩展的负值也先取其 32 位非负模式；将该模式作为 64 位非负值不改变低位并令高位为零。\(\square\)

### 7.2 局部覆盖与真实写回的区别

**命题 B2。** 对 \(q<w\) 的虚拟单元写入，结果

\[
a'=2^q\left\lfloor a/2^q\right\rfloor+M_q(b)
\]

保持旧高位并替换低 \(q\) 位；ALU32 写回则不保持真实寄存器旧高位。

**证明。** 写 \(a=2^q h+\ell\)，\(0\le\ell<2^q\)。虚拟结果为 \(2^q h+M_q(b)\)，故其高位商为 \(h\)。ALU32 的完整结果属于 \(\mathbb B_{32}\)，高 32 位由命题 B1 恒为零。\(\square\)

因此，16 位虚拟写入将 \(\mathtt{0x10000}\) 更新为 \(\mathtt{0x10001}\)，与 32 位真实赋值产生 1 并不矛盾：两者定义的写入范围不同。

### 7.3 FETCH 与交换操作使用旧值

**命题 B3。** 在第 4.4 节的有效规则中，FETCH、XCHG 的真实输出为更新前的虚拟值；CMPXCHG 的 R0 输出也为更新前的虚拟值，与比较是否成立无关。

**证明。** 三种规则的真实输出右侧均为 \(Z_{q\to64}^{(q),\star}(t_{\mathrm{virt}})\)。所有右侧由旧 \(E_g\) 取得，虚拟目标的新值不参与该输出。CMPXCHG 的分段条件只改变虚拟输出。\(\square\)

CMPXCHG 还满足：若旧虚拟值等于旧 R0 的低 \(q\) 位，虚拟单元取得源低 \(q\) 位；否则保持旧值。这由其分段公式直接得到。

### 7.4 位宽、解释与键唯一性

**命题 B4。** 在类型正确、参数合法且假设 BPF 成立时，各成功数值效果属于有限 Expr 集合；符号输出解释等于相应数值函数作用于源解释；整体覆写保持键唯一。

**证明。** 算术、移动和字节序结果属于 \(\mathbb B_{64}\)；LDDW 的普通整数及确定绑定也提供 64 位项；读取扩展到 64 位。虚拟局部写入由商余分解保证属于 \(\mathbb B_w\)；原子数值结果按 \(q\) 位取模。每个符号提升遵循对应位宽签名，其解释保持性由共同 solve 命题推出。普通规则只有一个目标；多目标规则分别写虚拟标记与真实标记，键互异，故局部键唯一。最终使用共同覆写命题。\(\square\)

这些性质只验证给定数值投影的内部一致性。资源绑定正确、完整外部效果、并发语义和跨架构等价性不在证明结论之内。

## 8. 数值语义依据

- [BPF ISA 标准](https://docs.kernel.org/bpf/standardization/instruction-set.html)：算术、重叠寄存器视图、字节序、MEMSX 与原子数值操作。
- [IANA BPF 指令登记表](https://www.iana.org/assignments/bpf-instructions/bpf-instructions.xhtml)：指令参数与合法形式。
- [Linux BPF 定义](https://github.com/torvalds/linux/blob/master/include/uapi/linux/bpf.h)与 [LLVM 扩展定义](https://llvm.googlesource.com/llvm-project/+/17bfc00f7c4a424d7b5dc6da575865833701fd1a%5E%21/)：LOAD_ACQ、STORE_REL 等扩展的范围。

每个未决资源或调用规则都需要自己的定义域与正确性证明。
