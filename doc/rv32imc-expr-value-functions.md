# RV32IMC 的符号值函数与局部正确性

本文将 RV32IMC 指令解释为寄存器关系上的部分值函数。目标是规定数值运算、符号提升及局部更新，并证明位宽、零寄存器和解释保持性质。共同对象与 solve 的定义见 [共同数学基础](common-math.md)。

指令的寄存器、立即数、位宽和偏移视为已给定的数学参数。本文不讨论这些参数如何从位模式取得。内存访问公式以资源绑定已确定为前提；外部调用与完整访问观察尚未定义。

## 1. 指令参数与寄存器

### 1.1 寄存器身份

令 \(x_0,\ldots,x_{31},\mathrm{PC}\in\mathrm{Reg}_{\mathrm{Real},32}\)。\(\mathrm{SP}=x_2\)、\(\mathrm{RA}=x_1\) 是同一标记的别名。RV32 的真实寄存器均为 32 位，虚拟 SR 或 Map64 的存在不产生 64 位真实寄存器。

读取 \(x_0\) 恒得 \(C_{32}(0)\)，写入 \(x_0\) 不生成赋值。输入若含 \(x_0=t\)，要求 \(\operatorname{solve}_{32}(t)=C_{32}(0)\)；否则值规则无定义。

### 1.2 数值参数

算术立即数为已扩展的整数 \(\iota\)，其 32 位模式为 \(I=M_{32}(\iota)\)。上位立即数为 \(U\in\mathbb B_{32}\)，满足 \(M_{12}(U)=0\)。立即数移位量 \(k\) 满足 \(0\le k<32\)。

跳转与分支使用完整的有符号字节偏移 \(\delta\)。普通指令长度为 4 字节，压缩指令长度为 2 字节；这一差别只影响链接值与地址关系。

压缩指令的数值参数遵循各自合法域：C.ADDI、C.LI、C.ANDI 使用已符号扩展的六位立即数；C.LUI 的上位值为 \(U_C=M_{32}(s_6(h)2^{12})\)，其中 \(h\in\mathbb B_6\)；C.ADDI16SP 使用非零、16 的整数倍偏移；C.ADDI4SPN 使用非零、4 的非负整数倍偏移。压缩字访问使用完整字节偏移，受限寄存器取自 \(x_8,\ldots,x_{15}\)。

## 2. 部分值函数与更新

### 2.1 局部效果

设 \(\mathcal I_R\) 为参数满足合法域的已解码指令集合。定义

\[
\operatorname{value}_R:
\mathscr F(\mathrm{Expr})\times\mathcal I_R
\rightharpoonup\mathscr F(\mathrm{Expr}),
\qquad
\operatorname{value}_R(E_g,i)=E_i.
\]

后文省略下标 R。\(E_g\) 是执行前关系集合，\(E_i\) 只含当前指令产生的关系。成功空集表示没有新增 Expr；部分函数无定义表示不能给出成功值效果。

必需源值由 \(E_g\) 中唯一的完整等式取得。不等式或低位等式不能替代完整值；未定义源也不自动变成新输入变元。\(r_d,r_a,r_b\) 表示目标与源，源项为 \(t_a,t_b\in\mathrm{Term}_{32}\)。只要求实际读取的源值，普通赋值不要求目标旧值。

### 2.2 同一源快照

所有输出由同一个 \(E_g\) 计算，再按共同的关系键 \((r,\bowtie)\) 一次覆写：

\[
E_g'=E_g\times E_i.
\]

\(E_g,E_i\) 均要求键唯一。覆盖普通等式不自动删去其他关系键，也不证明保留的旧约束仍成立。

PC 作为数值源时，\(\mathrm{PC}=t_\pi\) 表示当前指令位置。本文只定义使用该源项的 AUIPC 与链接值，不将旧 PC 项沿用为下一条指令的位置。

### 2.3 符号提升

每种数值规则给出 \(\widehat f_i\)，其形式运算符为 \(f_i\)，符号输出使用 \(f_i^\star\)。纯寄存器运算的指令参数固定运算、立即数与位宽。虚拟访问还依赖绑定给出的单元位宽 \(w\)，相应运算符严格记作 \(f_{i,w}\)；后文在位宽已明确时简写为 \(f_i\)。同一指令在不同单元位宽下可以具有不同的函数签名与元数。目标寄存器身份不作为右侧数值参数。

对纯数值全函数，闭输入应用由 solve 求得常元；含变元时保留完整项，不做局部代数化简。外部资源结果不能仅因地址或实参为常元而套用这一规则。

## 3. 算术与链接值

本节仅产生 Expr，不添加 Predicate。所有输出只写真实寄存器。合法 HINT、写 x0 等无输出情况按第 5 节处理；以下非空等式均以实际目标不是 x0 为前提。

### 3.1 LUI 与 AUIPC

U 是 i 中已恢复的 U 型 32 位立即数。LUI 不读取目标旧值：

\[
\operatorname{value}(E_g,i)=\{r_d=C_{32}(U)\},
\qquad (i\text{ 为 LUI}).
\]

AUIPC 读取 \(E_g\) 中的 PC 等式，其数值签名为
\(\mathbb B_{32}\to\mathbb B_{32}\)：

\[
\widehat f_i(\pi)=M_{32}(\pi+U),
\qquad
\operatorname{value}(E_g,i)=\{r_d=f_i^\star(t_\pi)\}.
\]

\(\pi\in\mathbb B_{32}\) 是 \(t_\pi\) 对应的数值，不是额外函数输入。

### 3.2 立即数算术

从 \(E_g\) 读取 \(r_a=t_a\)。\(\iota\) 是当前 i 的已扩展有符号立即数，令 \(I=M_{32}(\iota)\)；移位量 k 来自 i。

各行的数值签名为 \(\mathbb B_{32}\to\mathbb B_{32}\)，a 对应源项 \(t_a\)。

| 指令 | \(\widehat f_i(a)\) |
|---|---|
| ADDI | \(M_{32}(a+I)\) |
| SLTI | \(\mathbf1[s_{32}(a)<s_{32}(I)]\) |
| SLTIU | \(\mathbf1[a<I]\) |
| ANDI | \(\mathrm{AND}_{32}(a,I)\) |
| ORI | \(\mathrm{OR}_{32}(a,I)\) |
| XORI | \(\mathrm{XOR}_{32}(a,I)\) |
| SLLI | \(M_{32}(a2^k)\) |
| SRLI | \(\lfloor a/2^k\rfloor\) |
| SRAI | \(M_{32}(\lfloor s_{32}(a)/2^k\rfloor)\) |

对每行，

\[
\operatorname{value}(E_g,i)=\{r_d=f_i^\star(t_a)\}.
\]

\(\mathbf1[\cdot]\) 是共同定义的命题指示函数。SLTIU 的立即数先符号扩展成 32 位，再按无符号位模式比较。SLTI/SLTIU 输出 0 或 1 的值项，不产生分支 Predicate。

### 3.3 双源算术

读取两个源项 \(t_a,t_b\)。数值签名均为
\(\mathbb B_{32}^2\to\mathbb B_{32}\)，令 \(k=b\bmod32\)。

| 指令 | \(\widehat f_i(a,b)\) |
|---|---|
| ADD | \(M_{32}(a+b)\) |
| SUB | \(M_{32}(a-b)\) |
| SLT | \(\mathbf1[s_{32}(a)<s_{32}(b)]\) |
| SLTU | \(\mathbf1[a<b]\) |
| AND | \(\mathrm{AND}_{32}(a,b)\) |
| OR | \(\mathrm{OR}_{32}(a,b)\) |
| XOR | \(\mathrm{XOR}_{32}(a,b)\) |
| SLL | \(M_{32}(a2^k)\) |
| SRL | \(\lfloor a/2^k\rfloor\) |
| SRA | \(M_{32}(\lfloor s_{32}(a)/2^k\rfloor)\) |

对每行，

\[
\operatorname{value}(E_g,i)=\{r_d=f_i^\star(t_a,t_b)\}.
\]

只读取指令指定的 rs1、rs2，不默认读取 rd 的旧值。SLT/SLTU 同样只写比较结果 Expr。

### 3.4 乘法低半与高半

读取 rs1、rs2 对应的 \(t_a,t_b\)，顺序不能交换 MULHSU 的有符号与无符号参数。数值签名为 \(\mathbb B_{32}^2\to\mathbb B_{32}\)。

| 指令 | \(\widehat f_i(a,b)\) |
|---|---|
| MUL | \(M_{32}(ab)\) |
| MULHU | \(M_{32}(\lfloor ab/2^{32}\rfloor)\) |
| MULH | \(M_{32}(\lfloor s_{32}(a)s_{32}(b)/2^{32}\rfloor)\) |
| MULHSU | \(M_{32}(\lfloor s_{32}(a)b/2^{32}\rfloor)\) |

对每行，

\[
\operatorname{value}(E_g,i)=\{r_d=f_i^\star(t_a,t_b)\}.
\]

高半乘法使用向下取整，再取 32 位位模式；没有新增 64 位真实寄存器。

### 3.5 除法与余数

读取两个源项，数值签名均为 \(\mathbb B_{32}^2\to\mathbb B_{32}\)。DIVU、REMU 定义为

\[
\widehat f_i(a,b)=
\begin{cases}
2^{32}-1&b=0,\\
\lfloor a/b\rfloor&b\ne0,
\end{cases}
\qquad (i\text{ 为 DIVU}),
\]

\[
\widehat f_i(a,b)=
\begin{cases}
a&b=0,\\
a-b\lfloor a/b\rfloor&b\ne0,
\end{cases}
\qquad (i\text{ 为 REMU}).
\]

对 DIV、REM，令 \(x=s_{32}(a)\)、\(y=s_{32}(b)\)，则

\[
\widehat f_i(a,b)=
\begin{cases}
2^{32}-1&y=0,\\
2^{31}&x=-2^{31}\land y=-1,\\
M_{32}(\mathrm{TQ}(x,y))&\text{其他情况},
\end{cases}
\qquad (i\text{ 为 DIV}),
\]

\[
\widehat f_i(a,b)=
\begin{cases}
a&y=0,\\
0&x=-2^{31}\land y=-1,\\
M_{32}(\mathrm{TR}(x,y))&\text{其他情况},
\end{cases}
\qquad (i\text{ 为 REM}).
\]

四种指令均输出

\[
\operatorname{value}(E_g,i)=\{r_d=f_i^\star(t_a,t_b)\}.
\]

除零和最小负数除以 −1 在 M 扩展中有上述确定结果，不作为异常拒绝。TQ、TR 是共同定义的向零商与余数。

### 3.6 压缩算术的同值归约

以下仅列合法、非 HINT 的压缩运算。立即数与移位量满足第 1.2 节的数值约定。

单输入函数的签名为 \(\mathbb B_{32}\to\mathbb B_{32}\)；双输入函数为 \(\mathbb B_{32}^2\to\mathbb B_{32}\)。a、b 对应本行实际读取的项，不代表一组额外运行输入。

| 指令 | 从 \(E_g\) 读取 | 数值公式 | Expr 左侧 |
|---|---|---|---|
| C.ADDI4SPN | x2 的项 \(t_{\mathrm{SP}}\) | \(\widehat f_i(a)=M_{32}(a+\iota)\) | i 指定的目标 |
| C.ADDI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=M_{32}(a+\iota)\) | 同一个目标 |
| C.ADDI16SP | x2 的项 \(t_{\mathrm{SP}}\) | \(\widehat f_i(a)=M_{32}(a+\iota)\) | x2 |
| C.SRLI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=\lfloor a/2^k\rfloor\) | 同一个目标 |
| C.SRAI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=M_{32}(\lfloor s_{32}(a)/2^k\rfloor)\) | 同一个目标 |
| C.SLLI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=M_{32}(a2^k)\) | 同一个目标 |
| C.ANDI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=\mathrm{AND}_{32}(a,M_{32}(\iota))\) | 同一个目标 |
| C.SUB | 目标旧项 \(t_d\)、另一个源 \(t_b\) | \(\widehat f_i(a,b)=M_{32}(a-b)\) | 同一个目标 |
| C.XOR | \(t_d,t_b\) | \(\widehat f_i(a,b)=\mathrm{XOR}_{32}(a,b)\) | 同一个目标 |
| C.OR | \(t_d,t_b\) | \(\widehat f_i(a,b)=\mathrm{OR}_{32}(a,b)\) | 同一个目标 |
| C.AND | \(t_d,t_b\) | \(\widehat f_i(a,b)=\mathrm{AND}_{32}(a,b)\) | 同一个目标 |
| C.ADD | \(t_d,t_b\) | \(\widehat f_i(a,b)=M_{32}(a+b)\) | 同一个目标 |
| C.MV | 仅源项 \(t_b\) | \(\widehat f_i(b)=b\) | i 指定的目标 |

各行返回一个普通等式：左侧是本行目标，右侧是 \(f_i^\star\) 应用于本行读取的值项。例如

\[
\operatorname{value}(E_g,i)
=\{x_2=f_i^\star(t_{\mathrm{SP}})\},
\qquad (i\text{ 为 C.ADDI16SP}),
\]

\[
\operatorname{value}(E_g,i)
=\{r_d=f_i^\star(t_d,t_b)\},
\qquad (i\text{ 为 C.ADD}).
\]

C.LI、C.LUI 不读取目标旧值，直接定义

\[
\operatorname{value}(E_g,i)
=\{r_d=C_{32}(M_{32}(\iota))\},
\qquad (i\text{ 为 C.LI}),
\]

\[
\operatorname{value}(E_g,i)
=\{r_d=C_{32}(U_C)\},
\qquad (i\text{ 为 C.LUI}).
\]

C.ADDI16SP 改变的是真实 x2，不是虚拟 SW/SR 标记；C.ADDI4SPN 同样只计算真实目标值，不新增虚拟栈单元。

### 3.7 链接值：JAL、JALR、C.JAL、C.JALR

链接关系只描述跳转产生的返回地址值；控制目标另由第 5 节的规则确定。读取 \(E_g\) 中当前 PC 的项 \(t_\pi\)，数值签名为
\(\mathbb B_{32}\to\mathbb B_{32}\)。

| 指令 | \(\widehat f_i(\pi)\) | \(E_i\) |
|---|---|---|
| JAL，rd≠x0 | \(M_{32}(\pi+4)\) | \(\{r_d=f_i^\star(t_\pi)\}\) |
| JALR，rd≠x0 | \(M_{32}(\pi+4)\) | \(\{r_d=f_i^\star(t_\pi)\}\) |
| C.JAL | \(M_{32}(\pi+2)\) | \(\{x_1=f_i^\star(t_\pi)\}\) |
| C.JALR | \(M_{32}(\pi+2)\) | \(\{x_1=f_i^\star(t_\pi)\}\) |

JALR 的目标基址仍是整条指令读取的输入，但它不参与链接值的数值公式。确定后继前，控制规则须从旧 \(E_g\) 核对目标；不能因为链接函数不需要基址值就接受未定义输入或变元目标。

若调用具有外部语义，仍需独立定义其返回值和资源效果。链接等式不确定这些结果。

## 4. 已绑定虚拟单元的读写

### 4.1 访问假设与读取

**假设 R。** 当前指令与执行前关系唯一确定访问单元 \(r_v\)，其位宽为 \(w\in W\)；访问宽度 \(q\le w\)，资源有效。以下公式描述所绑定单元的低 \(q\) 位。一般地址、别名与跨单元访问的对应关系尚需独立定义。

若 \(r_v=t_v\)，目标 \(r_d\ne x_0\)，则

\[
\begin{aligned}
\operatorname{value}(E_g,\mathrm{LB})&=\{r_d=S_{8\to32}^{(w),\star}(t_v)\},\\
\operatorname{value}(E_g,\mathrm{LBU})&=\{r_d=Z_{8\to32}^{(w),\star}(t_v)\},\\
\operatorname{value}(E_g,\mathrm{LH})&=\{r_d=S_{16\to32}^{(w),\star}(t_v)\},\\
\operatorname{value}(E_g,\mathrm{LHU})&=\{r_d=Z_{16\to32}^{(w),\star}(t_v)\},\\
\operatorname{value}(E_g,\mathrm{LW})&=\{r_d=Z_{32\to32}^{(w),\star}(t_v)\}.
\end{aligned}
\]

C.LW 与 C.LWSP 采用 LW 的数值函数；后者以 SP 为基址。目标身份、基址关系和资源绑定仍须满足合法域。

窄读取覆盖整个 32 位目标，按零扩展或符号扩展确定其高位，不保留目标旧高位。普通 LOAD 的目标为 \(x_0\) 时局部 Expr 为空，但访问假设仍须成立；若选取访问观察，还须保留相应 Predicate。C.LWSP 的零目标不属于合法域。

### 4.2 完整写入与低位写入

设源项 \(t_b\in\mathrm{Term}_{32}\)，虚拟目标 \(r_v\) 的位宽为 \(w\)。SB、SH、SW 分别取 \(q=8,16,32\)；C.SW、C.SWSP 取 \(q=32\)。SP 的数值改变与虚拟栈单元写入是不同的数学效果。

当 \(q=w\) 时，写入不读取目标旧值，定义

\[
\widehat f_i:\mathbb B_{32}\to\mathbb B_w,
\qquad\widehat f_i(b)=M_w(b),
\qquad E_i=\{r_v=f_i^\star(t_b)\}.
\]

在 RV32 中，此情形只有 \(q=w=32\)。当 \(q<w\) 时，要求旧等式 \(r_v=t_v\)，定义

\[
\widehat f_i:\mathbb B_w\times\mathbb B_{32}\to\mathbb B_w,
\qquad
\widehat f_i(a,b)=2^q\left\lfloor a/2^q\right\rfloor+M_q(b),
\]

\[
E_i=\{r_v=f_i^\star(t_v,t_b)\}.
\]

该公式只规定已绑定单元的低位覆盖，不断言任意地址写入都对应这一区域。缺少必要旧值时，完整新值不能确定，值函数无定义。

新关系使用普通等式键，覆写旧完整值。只新增 \(=^{[q]}\) 而保留旧完整值供后续读取，会混淆写入前与写入后的值。

目标可为 SW、SR、Map32 或 Map64，数值公式由位宽决定。Map 的实际绑定与访问观察仍属于假设 R，不由该公式生成。

### 4.3 局部覆盖的性质

**命题 R1。** 令 \(a\in\mathbb B_w\)、\(b\in\mathbb B_{32}\)、\(q<w\)，写入结果 \(a'\) 满足

\[
M_q(a')=M_q(b),
\qquad
\left\lfloor a'/2^q\right\rfloor=\left\lfloor a/2^q\right\rfloor,
\qquad a'\in\mathbb B_w.
\]

**证明。** 设 \(a=2^q h+\ell\)，其中 \(0\le\ell<2^q\)。公式给出 \(a'=2^q h+M_q(b)\)。低位由新余数确定，高位商为 \(h\)。又 \(h<2^{w-q}\)，故 \(a'<2^w\)。\(\square\)

例如，已有 \(\mathrm{SW}(\alpha)=C_{32}(\mathtt{0x10000})\)，16 位写入 1 后得到 \(C_{32}(\mathtt{0x10001})\)。保留高位的结论来自局部覆盖公式。

## 5. 分支、跳转与返回观察

### 5.1 不产生赋值的控制效果

条件分支、无链接跳转和返回观察的局部值集合为 \(E_i=\varnothing\)，故 \(E_g'=E_g\)。这不表示它们不读取源值或不产生 Predicate。

合法 NOP、C.NOP 和 HINT 也不产生数据赋值。FENCE 与 FENCE.TSO 在不观察内存排序的模型中取空效果；这一抽象不证明它们在包含并发排序观察的语义中等价于空操作。

### 5.2 条件两侧

BEQ、BNE、BLT、BGE、BLTU、BGEU 的关系分别为

\[
=,\quad\ne,\quad<_s,\quad\ge_s,\quad<_u,\quad\ge_u.
\]

C.BEQZ、C.BNEZ 将第二源取为 \(C_{32}(0)\)。检查时固定源项 \(t_a,t_b\)，Taken 使用原关系，NotTaken 使用补关系。

**命题 R2（方向划分）。** 对每个变元赋值 \(\nu\)，原条件与补条件恰有一个成立。

**证明。** 两个源项在同一赋值下得到确定数值。补关系的定义正是对该次比较的布尔否定。\(\square\)

两个闭源可求值时选择确定方向；无法确定时保留两侧。不同时间的条件检查可能读取不同项，不能将同一助记符的两次检查当作同一个命题。

### 5.3 后继绑定与返回

给定指令地址 \(\pi\) 与偏移 \(\delta\)，直接目标由地址与程序位置的既定对应确定。JALR 的数值目标为

\[
\tau=2\left\lfloor M_{32}(a+\iota)/2\right\rfloor,
\]

其中 \(a\) 是执行前基址值；这清除最低位。链接写入不得改变目标计算使用的旧源。

程序内部目标、最外层正常返回与外部调用具有不同的语义。只有已识别的返回且到达既定外层返回位置，才能产生 Exit；返回观察使用返回规则确定的最终值项。未知目标不能作为 Exit，也不能作为已证明不可行的方向。

访问观察和外部调用结果尚未完整规定。普通链接值函数不提供外部调用的返回值、Map 修改或其他寄存器变化。

## 6. 定义域与排除行为

前述公式要求指令参数合法，输入键唯一且必需源项存在。压缩指令的非零立即数、寄存器范围与移位量限制都属于定义域；保留编码不因某个数值公式可计算而变为合法。

本模型不包含异常处理或特权状态，因此 ECALL、EBREAK、C.EBREAK、MRET、SRET、WFI、SFENCE.VMA 及非法指令没有成功值规则。重新解释某指令为外部操作时，须先给定独立语义。

虚拟单元不唯一、资源有效性未确立、局部写入缺少旧值和未绑定间接目标，也不在相应成功规则的定义域中。M 扩展的除零、最小负数除以 −1 则具有第 3.5 节给出的确定值，不属于异常拒绝。

## 7. 局部正确性命题

### 7.1 位宽闭合

**命题 R3。** 在源项类型正确、假设 R 成立且指令参数合法时，前述成功效果均属于 \(\mathscr F(\mathrm{Expr})\)，输出左右两侧同位宽。

**证明。** 算术、链接和读取结果均属于 \(\mathbb B_{32}\)，对应 \(\mathrm{Term}_{32}\) 与 32 位真实目标。完整虚拟写入按目标宽度取模；局部写入由命题 R1 保证结果属于 \(\mathbb B_w\)。符号提升遵循同一输入、输出签名，有限个目标产生有限关系集合。\(\square\)

### 7.2 数值解释保持

**命题 R4。** 对任一纯数值规则及类型正确的源项，有

\[
\llbracket f_i^\star(t_1,\ldots,t_n)\rrbracket_\nu
=\widehat f_i(\llbracket t_1\rrbracket_\nu,\ldots,
\llbracket t_n\rrbracket_\nu).
\]

**证明。** 符号提升是应用项的 solve。由共同数学基础的解释保持命题，solve 不改变应用项的解释；再用应用项定义。\(\square\)

这一命题证明给定公式与其符号表示一致。数值公式符合 ISA 的论证依赖相应规范；资源绑定、访问观察和完整控制行为的正确性需要另外的证明。

### 7.3 零寄存器不变与覆写

**命题 R5。** 有效输入中，成功局部效果不改变 \(x_0\) 的固定值；覆写后保持关系键唯一。

**证明。** 每个赋值规则在目标为 \(x_0\) 时删除该赋值，其他规则不写 \(x_0\)。原有合法零等式因而保持；若未记录零等式，读取规则仍恒给出零。其余关系的键唯一性由共同覆写命题得到。\(\square\)

上述局部结论不推出 RV32IMC 与 eBPF 的完整行为等价。后者仍需入口、资源、观察与控制规则之间的对应。

## 8. 数值语义依据

- [RV32I 2.1](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html)：整数运算、零寄存器、地址与链接值。
- [M 2.0](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html)：高半乘法、除零、溢出与向零商。
- [C 2.0](https://docs.riscv.org/reference/isa/v20260120/unpriv/c-st-ext.html)：压缩指令的数值域与指令长度。

虚拟单元投影、关系键覆写和选定观察范围是本文模型的定义，须与 ISA 数值事实分别论证。
