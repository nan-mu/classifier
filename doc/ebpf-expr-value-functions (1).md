# eBPF 指令的 Expr 值函数

本文只声明数学对象与函数，供之后转换为 Lean4 定义。共同的 Reg、Expr、Term、常元、变元和 solve 沿用 [common-math.md](common-math.md)。本文件补充当前指令输入、关系键覆写和 eBPF 寄存器视图。

指令保留 ADD、MOV、LDX、STX、CALL 等名称。位宽、源操作数和指令子类型作为指令对象的字段，不再通过数学名称为每种字段组合另造名字。

## 1. 指令名称与指令对象

### 1.1 名称空间

使用 eBPF 命名空间。Instruction 是一条已解码的指令对象，包含指令名称及该名称所需的带类型字段。原始编码仍属于共同定义的 Insn。

“寄存器源”和“立即数源”是操作数的两个构造分支：前者携带寄存器编号，后者携带 32 位立即数位模式。下表规定所有名称及合法变体，可以直接对应之后的 Lean4 指令对象。

| 指令名称 | 位宽或子类型 | 所需字段 |
|---|---|---|
| ADD、SUB、MUL、DIV、SDIV、OR、AND、LSH、RSH、MOD、SMOD、XOR、ARSH | 运算宽度 32 或 64 | 目标寄存器；寄存器源或立即数源 |
| NEG | 运算宽度 32 或 64 | 目标寄存器；只接受规定的 K 编码 |
| MOV | 运算宽度 32 或 64 | 目标寄存器；寄存器源或立即数源 |
| MOVSX | 32 位运算：源宽度 8、16；64 位运算：源宽度 8、16、32 | 目标、源寄存器；源宽度 |
| END | LE 或 BE；转换宽度 16、32、64 | 目标寄存器；目标字节序；转换宽度 |
| BSWAP | 反转宽度 16、32、64 | 目标寄存器；反转宽度；对应 ALU64 类 END |
| LDDW | 整数、Map fd、Map 值位置 fd、平台变量、代码位置、Map 索引、Map 值位置索引 | 目标寄存器；两槽位的立即数字段；子类型 |
| LDX | MEM：8、16、32、64；MEMSX：8、16、32 | 目标、基址寄存器；偏移；访问宽度；扩展方式 |
| ST | 访问宽度 8、16、32、64 | 基址寄存器；偏移；立即数源 |
| STX，MEM 模式 | 访问宽度 8、16、32、64 | 基址、源寄存器；偏移；访问宽度 |
| STX，ATOMIC 模式 | ADD、OR、AND、XOR；访问宽度 32、64；带或不带 FETCH | 基址、源寄存器；偏移；运算；FETCH 标志 |
| STX，ATOMIC 模式 | XCHG、CMPXCHG；访问宽度 32、64；规定的 FETCH 编码 | 基址、源寄存器；偏移；运算 |
| JEQ、JNE、JGT、JGE、JLT、JLE、JSGT、JSGE、JSLT、JSLE、JSET | 比较宽度 32 或 64 | 比较寄存器；寄存器源或立即数源；16 位跳转偏移 |
| JA | JMP 使用 16 位 offset；JMP32 使用 32 位 imm | 已解码跳转偏移及其字段种类 |
| CALL | 静态 helper ID、程序内函数偏移、BTF ID | 调用种类；对应 ID 或偏移 |
| EXIT | 无额外变体 | 无显式数据操作数 |
| LD，ABS 或 IND 模式 | 访问宽度 8、16、32 | 立即数偏移；IND 另含源寄存器 |

另外登记以下 Linux 扩展或候选编码：

| 名称 | 字段与范围 | 本文件处理 |
|---|---|---|
| LOAD_ACQ | 8、16、32、64 位；目标、基址、偏移 | 按普通读取的 Expr 效果处理 |
| STORE_REL | 8、16、32、64 位；基址、源、偏移 | 按普通写入的 Expr 效果处理 |
| MAY_GOTO | Linux 条件伪跳转及偏移 | 本轮没有 Expr；控制流与 Predicate 规则待定 |
| CALLX | 寄存器间接 helper 调用，编码 0x8d | 登记拒绝项，不视为当前可接受指令 |

前置解码给出这里的 Instruction。LDDW 的两个 64 位槽位在此阶段配对；第二槽位不是独立可执行指令。本文不实现解码。

后文 i 指当前已解码的指令对象。名称、操作数、位宽、立即数和偏移均从 i 取得，不成为值函数的额外输入。原始 Insn 保留在对应历史项中。

### 1.2 覆盖口径

本次实际核对的 IANA 登记表有 168 行，其中一行为宽立即数续槽。标准文档另列 MEMSX 的三个读取变体。按可执行首指令的语义变体统计，标准范围为：

| 标准指令组 | 变体数 |
|---|---:|
| 二元算术，含有符号除法和余数 | 52 |
| NEG、MOV、MOVSX | 11 |
| END、BSWAP | 9 |
| LDDW 子类型 | 7 |
| LDX、ST、STX 普通访问，含 MEMSX | 15 |
| STX ATOMIC 的数值变体 | 20 |
| 条件跳转、两种 JA | 46 |
| 三种 CALL、EXIT | 4 |
| 旧 ABS、IND 包读取 | 6 |
| 合计 | 170 |

此外登记 8 个 LOAD_ACQ/STORE_REL 变体、MAY_GOTO、CALLX，得到 180 个首指令变体或候选项；加上续槽是 181 个核对条目。这是本文件明确采用的统计口径，尚不能认定用户所记的“181 条指令”采用相同口径。

已按 opcode、src_reg 子类型、offset 限制和 imm 限制逐项比对 IANA 表：所有首指令登记项均对应上述变体，额外三个标准文档变体恰为 MEMSX 的 8、16、32 位读取。LOAD_ACQ/STORE_REL 来自另列的 Linux/LLVM 扩展依据。

列入清单、已定义 Expr 函数、当前模型接受执行，分别核对。CALL 的外部结果规则待定；平台变量和旧包读取仍拒绝；续槽不是指令。本文不再用名称数量直接声称所有指令都可执行。

## 2. 输入、输出与覆写更新

### 2.1 唯一输入

\[
\boxed{\operatorname{value}(E_g,i)=E_i.}
\]

\(E_g\) 是执行当前指令前的全局 Expr 有限集合，i 是当前 Instruction，\(E_i\) 是当前指令新产生的 Expr 有限集合。数学签名为

\[
\operatorname{value}:
\mathscr F(\mathrm{Expr})\times\mathrm{eBPF.Instruction}
\rightharpoonup\mathscr F(\mathrm{Expr}).
\]

部分函数箭头表示某些输入被拒绝或尚未定义。成功返回空集表示没有新增 Expr，不能表示拒绝。

需要读取寄存器 r 的确定值时，从 \(E_g\) 中取得唯一等式 \(r=t\)，使用其右侧项 t。不另传入寄存器与 Expr 配对。不等式等约束不能代替唯一值等式；缺少所需等式时拒绝。

只要求实际读取的值：MOV 赋值不读取目标旧值，立即数源直接取自 i。

### 2.2 寄存器关系键

对 \(e=(r,\bowtie,t)\)，定义

\[
\operatorname{key}(e)=(r,\bowtie).
\]

r 是规范化后的寄存器标记，\(\bowtie\) 是完整关系符号，包括其位宽修饰；右侧项不是键。

\(r_1=\) 与 \(r_1\le_u\) 是不同键，可以共存。普通 = 与 \(=^{[8]}\) 也是不同关系符号。

\(E_g\)、\(E_i\) 各自要求同一键至多对应一个 Expr：

\[
e,e'\in E,\quad\operatorname{key}(e)=\operatorname{key}(e')
\Longrightarrow e=e',
\]

其中 E 分别取 \(E_g\)、\(E_i\)。这是之后 Lean4 有限集合对象的有效性条件。

### 2.3 覆写

沿用用户指定的 \(\times\)，本节中它表示按键覆写，不表示笛卡尔积：

\[
\boxed{
E_g'=E_g\times E_i
=
\{e\in E_g:\nexists e_i\in E_i,\
\operatorname{key}(e)=\operatorname{key}(e_i)\}
\cup E_i.
}
\]

新 Expr 覆盖旧集合中的同键项，不同键保留。\(E_i=\varnothing\) 时 \(E_g'=E_g\)。

例如

\[
E_g=\{r_1=C_{64}(3),\ r_1\le_u C_{64}(9)\},
\quad E_i=\{r_1=C_{64}(7)\},
\]

得到

\[
E_g'=\{r_1=C_{64}(7),\ r_1\le_u C_{64}(9)\}.
\]

这是标记的更新规则，本身不证明旧约束对更新后的值仍成立。本文不自行添加其他关系键的删除规则。

多结果指令全部读取同一个 \(E_g\)，产生完整 \(E_i\) 后一次覆写，不先更新某个输出再计算另一个输出。

### 2.4 重叠寄存器视图

相同编号 j 的 rj 是 64 位视图，wj 是同一个寄存器的低 32 位视图。它们没有两个独立寄存器身份。\(E_g\) 统一使用 64 位真实寄存器标记 \(r_j\)。

若已有 \(r_j=t_j\)，则

\[
\text{读取 }r_j:\ t_j,
\qquad
\text{读取 }w_j:\ \mathrm{LOW}_{32}^{(64),\star}(t_j).
\]

当前指令按对应位宽运算；输出先规范化为 \(r_j=t_{64}\)，再按键覆写。

eBPF 的 ALU32 写回清零高 32 位。若运算得到 \(t_{32}\)，写回为

\[
r_j=Z_{32\to64}^{(32),\star}(t_{32}).
\]

因此按实际架构行为，r1=0x10000 后执行 w1=0x1，结果为 r1=0x1。即使旧值为 0x100000000，该 32 位真实寄存器写回也得到 0x1。

虚拟栈、Map 单元的局部写入按访问宽度覆盖，见第 4 节，不套用 ALU32 的高位清零规则。

## 3. 只产生 Expr 的指令

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

q 是转换宽度，取 16、32、64。D 是 END 指定的 LE 或 BE。H 是定义本文件函数时已经固定的宿主字节序，不是额外运行输入。

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

本节只处理普通整数子类型，其余子类型在第 4、6 节登记。

## 4. 同时产生 Expr 与 Predicate 的指令

本节沿用已有分类：虚拟栈/Map 的访问以及外部调用需要相应 Predicate。这里只定义 Expr 部分，不定义新 Predicate，不向 value 添加 Predicate 输入。

### 4.1 只写真实寄存器：LDX、LOAD_ACQ、已有绑定的 LDDW

当前 i 与 \(E_g\) 必须唯一确定访问对应的虚拟标记 \(r_{\mathrm{virt}}\)。它是已定义的 SW、SR、Map32 或 Map64；位宽为 w，访问宽度 q 满足 \(q\le w\)。

\(E_g\) 中的 \(r_{\mathrm{virt}}=t_{\mathrm{virt}}\) 提供源项。不另定义 READ、LOAD 或取地址函数。指令到标记的匹配沿用虚拟寄存器语义；没有唯一匹配则拒绝，不能把该标记作为第三个输入。

| 指令 | \(E_i=\operatorname{value}(E_g,i)\) |
|---|---|
| LDX，MEM | \(\{r_d=Z_{q\to64}^{(w),\star}(t_{\mathrm{virt}})\}\) |
| LDX，MEMSX | \(\{r_d=S_{q\to64}^{(w),\star}(t_{\mathrm{virt}})\}\) |
| LOAD_ACQ | \(\{r_d=Z_{q\to64}^{(w),\star}(t_{\mathrm{virt}})\}\) |

MEMSX 只取 q=8、16、32。LOAD_ACQ 与普通零扩展读取有相同 Expr，不记录 acquire 或原子性。

LDDW 的 Map fd、Map 索引、Map 值位置 fd、Map 值位置索引及代码位置子类型，也只写真实目标。若对应的确定绑定已在 \(E_g\) 中表达，其右侧项记作 \(t_{\mathrm{bind}}\)，则

\[
\operatorname{value}(E_g,i)=\{r_d=t_{\mathrm{bind}}\}.
\]

Map 绑定采用现有 Map 标记，代码位置绑定采用现有真实寄存器标记。这里不从 fd、索引或偏移自行制造未定义地址值。没有确定绑定时拒绝；精确绑定匹配待与 Predicate 语义一并完成。

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

这是该写指令自身的数值公式：替换标记对应单元的低 q 位，保留其余位。不额外建立传值函数或存储布局对象。q<w 而目标旧值缺失时，不能确定完整新值，按已约定的确定行为范围拒绝。

输出用普通 = 键，覆写旧完整值。不能只新增 \(=^{[q]}\) 关系，同时把旧完整等式当作写入后的值继续读取。

例如 SW 的已有 32 位值为 0x10000，执行 16 位 ST 写入 1，得到

\[
E_i=\{\mathrm{SW}(\alpha)=C_{32}(\mathtt{0x10001})\}.
\]

\(\alpha\) 是该 SW 的已有标识。这是虚拟单元的 16 位局部覆盖，不是 eBPF 32 位真实寄存器写回。

STORE_REL 与 STX 使用相同上述值函数，不记录 release 或原子性。

### 4.3 只写虚拟 Map 寄存器：ST、STX、STORE_REL

i 与 \(E_g\) 对应到 Map32 或 Map64 时，使用第 4.2 节完全相同的公式，将左侧取为该 Map 标记。位宽、源项取得方式和覆写规则相同。

这个划分依据指令当前对应的虚拟目标类型；不为同一 ST/STX 名称增加新的架构类别。

### 4.4 写虚拟寄存器，可能同时写真实寄存器：STX ATOMIC

只记录数值效果，不建模原子性、并发交错、锁、内存顺序或额外原子事件谓词。它属于本节，是因为访问虚拟栈/Map。

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

虚拟目标为 SW/SR 时归入栈输出，为 Map32/Map64 时归入 Map 输出。FETCH 只决定附加的真实寄存器 Expr，不引入传值函数。所有结果由更新前的 \(E_g\) 同时计算。

### 4.5 外部 CALL 的结果规则待定

静态 helper ID、BTF ID 的 CALL 属于此前约定的外部调用。返回值和 Map 修改不能由一条通用算术规则确定。

本次不再增加“调用结果 Expr 集合”作为第三个输入，不把调用前的 R0 等式当成调用结果，也不把这些 CALL 默认写成成功返回空集。

相应 \(\operatorname{value}(E_g,i)\) 分支待明确调用结果规则后补充。它们仍然只有 \(E_g,i\) 两个输入。此处登记名称与分类，不宣称已经完成外部调用的 Expr 定义。

## 5. 不产生 Expr 的指令

下表的本轮 Expr 函数均返回

\[
\operatorname{value}(E_g,i)=\varnothing,
\qquad E_g'=E_g.
\]

| 已约定分类 | 指令 | 本轮 Expr 效果 |
|---|---|---|
| 只产生 Predicate | JEQ、JNE、JGT、JGE、JLT、JLE、JSGT、JSGE、JSLT、JSLE、JSET 的全部 32/64 位、寄存器/立即数变体 | 空集；比较条件留给 Predicate 规则 |
| 只产生 Predicate | EXIT | 空集；返回观察与内部返回处理留给后续规则 |
| 两者都不产生 | JA 的两种偏移形式 | 空集；后继重排留给后续规则 |
| 两者都不产生 | 程序内 CALL | 空集；不虚构链接寄存器 |
| 分类待定的 Linux 扩展 | MAY_GOTO | 本轮没有 Expr；控制流与 Predicate 规则待定 |

没有 Expr 输出，不表示整条指令不读取寄存器。比较源、EXIT 的返回值仍须满足定义行为要求，由后续相应规则核对。

PC 仍是已定义的真实寄存器。本轮不添加 PC 推进或跳转目标 Expr，继续只锁定符号运算。

## 6. 拒绝项与尚未完成的定义

| 指令或情形 | 状态 |
|---|---|
| LDDW 平台变量子类型 | 当前虚拟栈/Map 范围不接受 |
| LD ABS、LD IND | 当前模型不接受包区域读取 |
| CALLX | Linux 文档列为 verifier 不支持的编码，当前拒绝 |
| 保留编码、非法字段组合、只读寄存器写入、未启用扩展 | 拒绝 |
| 必需等式缺失、没有唯一虚拟标记或确定绑定 | 拒绝 |
| 静态 helper、BTF CALL 的结果 Expr | 等待调用结果规则，不伪装为成功空集 |
| 指令字段与虚拟栈/Map 的精确匹配 | 待与 Predicate 语义一并完成；第 4 节定义匹配确定后的值函数 |
| MAY_GOTO 的控制与 Predicate 效果 | 待定；本轮无 Expr |

## 7. 依据与 Lean4 对象对应

- [IANA BPF 指令登记表](https://www.iana.org/assignments/bpf-instructions/bpf-instructions.xhtml)：登记条目及宽立即数续槽。
- [BPF ISA 标准文档](https://docs.kernel.org/bpf/standardization/instruction-set.html)：算术、字节序、MEMSX、原子数值操作及标准变体。
- [Linux BPF 公开定义](https://github.com/torvalds/linux/blob/master/include/uapi/linux/bpf.h)：LOAD_ACQ、STORE_REL、JCOND/MAY_GOTO 等扩展。
- [LLVM 的 LOAD_ACQ/STORE_REL 定义与测试](https://llvm.googlesource.com/llvm-project/+/17bfc00f7c4a424d7b5dc6da575865833701fd1a%5E%21/)：8/16/32/64 位访问变体。
- [Linux implementation notes](https://docs.kernel.org/bpf/linux-notes.html)：CALLX 支持状态及旧包访问。

Instruction 对应携带带类型字段的指令对象；Expr 沿用共同定义；\(E_g,E_i\) 对应满足键唯一条件的有限 Expr 集合；key 是键投影；\(\times\) 过滤旧同键项后加入新项。这里不写 Lean 代码，也不把尚未规定的调用、定位规则补成默认实现。
