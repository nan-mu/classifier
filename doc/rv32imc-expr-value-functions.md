# RV32IMC 指令的 Expr 值函数

本文采用与 [eBPF 文档](ebpf-expr-value-functions.md) 相同的输入、输出和按键覆写格式。共同的 Reg、Expr、Term、常元、变元和 solve 沿用 [common-math.md](common-math.md)。这里只作数学声明，不写 Lean4 实现，不使用 Sail 模拟执行器的 SailM、pure 或 ExecutionResult。

保留已有 Sail instruction 的构造器名称。UTYPE、ITYPE 等构造器中的操作字段决定 LUI、ADDI 等具体指令，不为它们重新发明数学名称。

## 1. 指令名称与指令对象

### 1.1 名称空间与已有 Sail 构造器

使用 RV32IMC 命名空间。本文的 Instruction 指已有 Sail 导出 instruction 所描述的已解码对象；这是数学类型名称，不要求重建另一套指令类型。对象字段的实际 Lean4 类型继续采用已有导出声明。

| Sail 构造器 | 对应指令名称 | 数学上需要的字段 |
|---|---|---|
| UTYPE | LUI、AUIPC | 立即数、目标、操作 |
| ITYPE | ADDI、SLTI、SLTIU、ANDI、ORI、XORI | 立即数、源、目标、操作 |
| SHIFTIOP | SLLI、SRLI、SRAI | 移位量、源、目标、操作 |
| RTYPE | ADD、SUB、SLT、SLTU、AND、OR、XOR、SLL、SRL、SRA | 两个源、目标、操作 |
| MUL | MUL、MULH、MULHSU、MULHU | 两个源、目标、乘法操作 |
| DIV | DIV、DIVU | 两个源、目标、有符号或无符号选择 |
| REM | REM、REMU | 两个源、目标、有符号或无符号选择 |
| LOAD | LB、LBU、LH、LHU、LW | 偏移、基址、目标、访问宽度、扩展方式 |
| STORE | SB、SH、SW | 偏移、基址、值源、访问宽度 |
| JAL | JAL | 已解码跳转偏移、链接目标 |
| JALR | JALR | 偏移、基址、链接目标 |
| BTYPE | BEQ、BNE、BLT、BGE、BLTU、BGEU | 两个比较源、偏移、操作 |
| FENCE、FENCE_TSO | FENCE、FENCE.TSO | 对应屏障字段；本模型不观察排序效果 |
| ECALL、EBREAK | ECALL、EBREAK | 既有构造器字段；异常默认拒绝 |

压缩构造器保留如下对应关系。表中寄存器和立即数字段来自既有 Sail 对象；隐含寄存器也明确列出。

| Sail 构造器 | 指令名称 | 所需操作数或隐含寄存器 |
|---|---|---|
| C_ADDI4SPN | C.ADDI4SPN | 目标、立即数；源为 x2 |
| C_ADDI | C.ADDI | 同一个源与目标、立即数 |
| C_LI | C.LI | 目标、立即数 |
| C_ADDI16SP | C.ADDI16SP | 立即数；源、目标均为 x2 |
| C_LUI | C.LUI | 目标、立即数 |
| C_SRLI、C_SRAI、C_SLLI | C.SRLI、C.SRAI、C.SLLI | 同一个源与目标、移位量 |
| C_ANDI | C.ANDI | 同一个源与目标、立即数 |
| C_SUB、C_XOR、C_OR、C_AND、C_ADD | C.SUB、C.XOR、C.OR、C.AND、C.ADD | 目标旧值与另一个源；写回目标 |
| C_MV | C.MV | 源、目标；不读目标旧值 |
| C_LW、C_SW | C.LW、C.SW | 基址、值寄存器、偏移 |
| C_LWSP、C_SWSP | C.LWSP、C.SWSP | 值寄存器、偏移；基址为 x2 |
| C_J、C_JAL | C.J、C.JAL | 跳转偏移；C.JAL 的链接目标为 x1 |
| C_JR、C_JALR | C.JR、C.JALR | 基址；C.JALR 的链接目标为 x1 |
| C_BEQZ、C_BNEZ | C.BEQZ、C.BNEZ | 比较源、偏移；另一个比较值为 0 |
| C_NOP | C.NOP | 无数据操作数 |
| C_EBREAK | C.EBREAK | 异常，拒绝 |

另外登记 MRET、SRET、WFI、SFENCE_VMA、ILLEGAL、C_ILLEGAL。它们在第 6 节处理，不扩充特权状态或其他指令集。

压缩三位寄存器编号对应 x8–x15。若已有字段尚是压缩编号，前置解码按规范完成这一映射；若已经是完整编号，不能重复加 8。

### 1.2 当前指令与立即数

后文 i 是当前已解码对象，原始编码仍属于共同的 Insn 并保留在历史项中。源、目标、操作、立即数、偏移均从 i 取得，不作为 value 的额外输入。

本文使用已经恢复完整数值的立即数：

| 字段含义 | 本文采用的值 |
|---|---|
| 普通 I/S 型立即数 | 有符号整数 \(\iota\)，来自完整 12 位立即数的符号扩展 |
| U 型立即数 | 32 位位模式 U，已包含低 12 位零 |
| 普通立即数移位量 | 整数 k，满足 \(0\le k<32\) |
| B/J 型偏移 | 完整有符号字节偏移，最低位零已经恢复 |
| C.ADDI、C.LI、C.ANDI 的立即数 | 六位立即数符号扩展所得 \(\iota\) |
| C.LUI 的立即数 | \(U_C=M_{32}(s_6(h)2^{12})\)，h 是原始六位位模式 |
| C.ADDI16SP 的立即数 | 完整有符号 \(\iota\)，低四位为零且非零 |
| C.ADDI4SPN 的立即数 | 完整非负 \(\iota\)，低两位为零且非零 |
| 压缩 load/store 偏移 | 完整非负字节偏移，低两位零已恢复 |
| 压缩跳转、分支偏移 | 完整有符号字节偏移，最低位零已恢复 |

若 Sail 字段已经给出扩展后的位模式或完整偏移，直接使用它，不重复符号扩展、左移或乘 2。上表规定输入的数学含义，不重新描述机器码位的拼接。

## 2. 输入、关系键与更新

### 2.1 唯一输入

\[
\boxed{\operatorname{value}(E_g,i)=E_i.}
\]

\(E_g\) 是当前指令发生前的全局 Expr 有限集合，\(E_i\) 是当前指令新产生的有限 Expr 集合。数学签名为

\[
\operatorname{value}:
\mathscr F(\mathrm{Expr})\times\mathrm{RV32IMC.Instruction}
\rightharpoonup\mathscr F(\mathrm{Expr}).
\]

部分函数箭头表示拒绝或规则待定；成功空集只表示没有新增 Expr。

从 \(E_g\) 的唯一等式 \(r=t\) 读取 r 的值项。不等式等关系不能代替该确定值等式；必需的源项缺失时拒绝。

\(r_d,r_a,r_b\) 表示当前指令指定的目标、两个源标记，均属于 \(\mathrm{Reg}_{\mathrm{Real},32}\)。源等式的右侧记为 \(t_a,t_b\in\mathrm{Term}_{32}\)。只在指令实际读取时才要求相应等式。

### 2.2 寄存器身份与零寄存器

x0–x31、PC 都使用共同的 32 位真实寄存器标记，不增加架构寄存器类型。SP 是 x2 的别名，RA 是 x1 的别名；关系键使用同一个底层标记，不为别名建立第二份值。

RV32 的通用寄存器自身是 32 位。本文件没有一个与它重叠的 RV64 寄存器，也不把 eBPF 的 r/w 视图写回规则套到这里。

读取 x0 总是得到 \(C_{32}(0)\)，不要求 \(E_g\) 包含 x0 的等式。写 x0 不生成赋值 Expr，不能改变它的值。若输入含 x0 的普通等式，其右侧经 solve 必须为 \(C_{32}(0)\)，否则拒绝该输入；其他关系不能用来替代这个固定值。

省略 x0 写回不等于省略整条指令的合法性核对。尤其 LOAD 的目标为 x0 时，访问仍需有效，仍保留其虚拟访问的 Predicate；不能因为丢弃结果就接受异常访问。

\(E_g\) 中的 \(\mathrm{PC}_{32}=t_\pi\) 表示当前指令发生前的位置。AUIPC 和链接值计算读取它。这里不自动生成下一条指令的 PC 等式，也不能把尚未更新的旧 PC 当作下一条指令的当前位置。

### 2.3 关系键与覆写

对 \(e=(r,\bowtie,t)\)，定义

\[
\operatorname{key}(e)=(r,\bowtie).
\]

寄存器别名先规范化；关系符号含已有位宽修饰。右侧项不属于键。\(r=\) 和 \(r\le_u\) 可共存。

\(E_g\)、\(E_i\) 各自满足键唯一条件：

\[
e,e'\in E,\quad \operatorname{key}(e)=\operatorname{key}(e')
\Longrightarrow e=e'.
\]

E 分别取 \(E_g\)、\(E_i\)。覆写规则与 eBPF 相同：

\[
\boxed{
E_g'=E_g\times E_i
=
\{e\in E_g:\nexists e_i\in E_i,\
\operatorname{key}(e)=\operatorname{key}(e_i)\}
\cup E_i.
}
\]

本节的 \(\times\) 是覆写运算，不是笛卡尔积。新同键项替换旧项，不同键保留。保留不同关系键本身不保证旧约束对新值仍成立。

所有右侧项先由同一个 \(E_g\) 取得并计算，再一次覆写。目标恰好与源、PC 或链接寄存器相关时，也不读取刚产生的输出。

### 2.4 数值公式与符号提升

每条指令的形式运算符记为 \(f_i\)，数值解释为 \(\widehat f_i\)，符号提升为 \(f_i^\star\)，沿用共同定义。下标 i 标识指令规定的运算及其立即数参数，不把目标编号或当前指令实例编号作为右侧值运算的参数。

无变元时 solve 得到常元；只要有变元，整个函数应用不变。数值公式内的截取、取模、移位不会单独触发含变元项的局部化简。

## 3. 只产生 Expr 的指令

本节仅产生 Expr，不添加 Predicate。所有输出只写真实寄存器。合法 HINT、写 x0 等无输出情况按第 5 节处理；以下非空等式均以实际目标不是 x0 为前提。

### 3.1 UTYPE：LUI、AUIPC

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

### 3.2 ITYPE、SHIFTIOP：立即数运算

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

### 3.3 RTYPE：寄存器运算

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

### 3.4 MUL：四种乘法

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

### 3.5 DIV、REM：除法与余数

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

### 3.6 压缩算术：全部数据值函数

以下仅列合法、非 HINT 的压缩运算。立即数与移位量已按第 1.2 节恢复。

单输入函数的签名为 \(\mathbb B_{32}\to\mathbb B_{32}\)；双输入函数为 \(\mathbb B_{32}^2\to\mathbb B_{32}\)。a、b 对应本行实际读取的项，不代表一组额外运行输入。

| 构造器/指令 | 从 \(E_g\) 读取 | 数值公式 | Expr 左侧 |
|---|---|---|---|
| C_ADDI4SPN / C.ADDI4SPN | x2 的项 \(t_{\mathrm{SP}}\) | \(\widehat f_i(a)=M_{32}(a+\iota)\) | i 指定的目标 |
| C_ADDI / C.ADDI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=M_{32}(a+\iota)\) | 同一个目标 |
| C_ADDI16SP / C.ADDI16SP | x2 的项 \(t_{\mathrm{SP}}\) | \(\widehat f_i(a)=M_{32}(a+\iota)\) | x2 |
| C_SRLI / C.SRLI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=\lfloor a/2^k\rfloor\) | 同一个目标 |
| C_SRAI / C.SRAI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=M_{32}(\lfloor s_{32}(a)/2^k\rfloor)\) | 同一个目标 |
| C_SLLI / C.SLLI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=M_{32}(a2^k)\) | 同一个目标 |
| C_ANDI / C.ANDI | 目标旧项 \(t_d\) | \(\widehat f_i(a)=\mathrm{AND}_{32}(a,M_{32}(\iota))\) | 同一个目标 |
| C_SUB / C.SUB | 目标旧项 \(t_d\)、另一个源 \(t_b\) | \(\widehat f_i(a,b)=M_{32}(a-b)\) | 同一个目标 |
| C_XOR / C.XOR | \(t_d,t_b\) | \(\widehat f_i(a,b)=\mathrm{XOR}_{32}(a,b)\) | 同一个目标 |
| C_OR / C.OR | \(t_d,t_b\) | \(\widehat f_i(a,b)=\mathrm{OR}_{32}(a,b)\) | 同一个目标 |
| C_AND / C.AND | \(t_d,t_b\) | \(\widehat f_i(a,b)=\mathrm{AND}_{32}(a,b)\) | 同一个目标 |
| C_ADD / C.ADD | \(t_d,t_b\) | \(\widehat f_i(a,b)=M_{32}(a+b)\) | 同一个目标 |
| C_MV / C.MV | 仅源项 \(t_b\) | \(\widehat f_i(b)=b\) | i 指定的目标 |

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

这里只定义普通跳转或内部调用的链接 Expr，不定义目标 PC 或后继重排。读取 \(E_g\) 中当前 PC 的项 \(t_\pi\)，数值签名为
\(\mathbb B_{32}\to\mathbb B_{32}\)。

| 指令 | \(\widehat f_i(\pi)\) | \(E_i\) |
|---|---|---|
| JAL，rd≠x0 | \(M_{32}(\pi+4)\) | \(\{r_d=f_i^\star(t_\pi)\}\) |
| JALR，rd≠x0 | \(M_{32}(\pi+4)\) | \(\{r_d=f_i^\star(t_\pi)\}\) |
| C_JAL / C.JAL | \(M_{32}(\pi+2)\) | \(\{x_1=f_i^\star(t_\pi)\}\) |
| C_JALR / C.JALR | \(M_{32}(\pi+2)\) | \(\{x_1=f_i^\star(t_\pi)\}\) |

JALR 的目标基址仍是整条指令读取的输入，但它不参与链接值的数值公式。实际接受该跳转前，后续控制规则须从旧 \(E_g\) 核对目标；不能因为链接函数不需要基址值就接受未定义输入或变元目标。

若某个调用被运行时规则识别为外部调用，其返回值/Map 效果适用第 4.4 节的待定规则；上述链接等式不替代外部调用结果。

## 4. 同时产生 Expr 与 Predicate 的指令

本节沿用虚拟栈/Map 访问与外部调用的分类，只定义其中的 Expr 部分。value 仍只有 \(E_g,i\) 两个输入，不增加 Predicate、访问描述或调用结果集合参数。

### 4.1 只写真实寄存器：LOAD 与压缩读取

当前 i 与 \(E_g\) 必须唯一确定虚拟标记 \(r_{\mathrm{virt}}\)，它是已有 SW、SR、Map32 或 Map64。w 是该标记位宽，q 是访问宽度，要求 \(q\le w\)。

已有等式 \(r_{\mathrm{virt}}=t_{\mathrm{virt}}\) 提供读取值。标记匹配沿用虚拟寄存器语义，精确规则待与 Predicate 定义一并完成；没有唯一匹配或值等式则拒绝。不另定义 READ、LOAD、取地址或存储布局函数。

目标不是 x0 时：

| 指令 | q | \(\operatorname{value}(E_g,i)\) |
|---|---:|---|
| LB | 8 | \(\{r_d=S_{8\to32}^{(w),\star}(t_{\mathrm{virt}})\}\) |
| LBU | 8 | \(\{r_d=Z_{8\to32}^{(w),\star}(t_{\mathrm{virt}})\}\) |
| LH | 16 | \(\{r_d=S_{16\to32}^{(w),\star}(t_{\mathrm{virt}})\}\) |
| LHU | 16 | \(\{r_d=Z_{16\to32}^{(w),\star}(t_{\mathrm{virt}})\}\) |
| LW | 32 | \(\{r_d=Z_{32\to32}^{(w),\star}(t_{\mathrm{virt}})\}\) |
| C_LW / C.LW | 32 | 与 LW 相同 |
| C_LWSP / C.LWSP | 32 | 与 LW 相同；隐含基址为 x2 |

真实目标始终为 32 位；较窄读取覆盖完整目标并按表符号扩展或零扩展，不保留目标旧高位。C.LWSP 的 rd=x0 编码是保留编码，先拒绝，不能套用普通 LOAD 的丢弃结果规则。

普通 LOAD 的 rd=x0 且访问有效时，\(E_i=\varnothing\)，仍保留访问的 Predicate。因此该指令实例只产生 Predicate。

C.LWSP 使用 SP 基址；它是否对应虚拟栈标记，仍由当前已确定的绑定判断，不只根据名称替代标记匹配。

### 4.2 只写虚拟栈寄存器：STORE 与压缩写入

i 与 \(E_g\) 对应到 SW 或 SR 时，输出只写该虚拟栈标记 \(r_{\mathrm{virt}}\)。w 是标记位宽；SB、SH、SW 的访问宽度 q 分别为 8、16、32，要求 \(q\le w\)。

C_SW、C_SWSP 的 q=32，沿用 SW 的值函数；C.SWSP 的隐含基址为 x2。指令名 SW 与标记 \(\mathrm{SW}(\alpha)\) 由上下文区分。

值源 \(r_b=t_b\) 从 \(E_g\) 读取；源为 x0 时 \(t_b=C_{32}(0)\)。

当 q=w 时，不读取虚拟目标旧值。当前指令的数值签名和输出为

\[
\widehat f_i:\mathbb B_{32}\to\mathbb B_w,
\qquad \widehat f_i(b)=M_w(b),
\]

\[
\operatorname{value}(E_g,i)
=\{r_{\mathrm{virt}}=f_i^\star(t_b)\}.
\]

本文件 q≤32，因此 q=w 的情况实际是 q=w=32。

当 q<w 时，要求已有 \(r_{\mathrm{virt}}=t_{\mathrm{virt}}\)，定义

\[
\widehat f_i:\mathbb B_w\times\mathbb B_{32}\to\mathbb B_w,
\]

\[
\widehat f_i(a,b)
=2^q\left\lfloor a/2^q\right\rfloor+M_q(b),
\]

\[
\operatorname{value}(E_g,i)
=\{r_{\mathrm{virt}}=f_i^\star(t_{\mathrm{virt}},t_b)\}.
\]

a 是虚拟单元旧值，b 是源寄存器值。公式覆盖所对应单元的低 q 位，保留其余位；没有额外传值函数或位段布局对象。

输出使用普通 = 键，覆写旧完整等式，不只新增 \(=^{[q]}\) 而继续读取旧完整值。局部写入缺少必要旧值时，完整结果不确定，按当前范围拒绝。

例如 SH 向已有 \(\mathrm{SW}(\alpha)=C_{32}(\mathtt{0x10000})\) 写入 1，得到

\[
E_i=\{\mathrm{SW}(\alpha)=C_{32}(\mathtt{0x10001})\}.
\]

这里 \(\alpha\) 是已确定的虚拟栈标记标识。

### 4.3 只写虚拟 Map 寄存器：STORE 与压缩写入

若对应标记是 Map32 或 Map64，使用第 4.2 节相同公式，将左侧取为相应 Map 标记。源项、访问宽度和覆写规则相同。

这是按已确定的输出目标类型分类；不新增 STORE 名称或架构寄存器类别。SR、Map64 仍是共同的虚拟标记，并不意味着 RV32 有 64 位真实通用寄存器。

### 4.4 已识别的外部调用：结果规则待定

RV32IMC 的 JAL/JALR 指令含义不足以指定 helper ABI、返回寄存器、Map 修改或寄存器失效规则。ECALL 本征行为是异常，也不能自动视为已定义的 helper。

若后续运行时规则把某个调用明确解释为外部调用，其 \(\operatorname{value}(E_g,i)\) 分支须随相应调用结果规则补充。当前不增加结果集合作为第三个输入，不制造返回变元，也不默认成功返回空集。

普通链接值已在第 3.7 节定义，外部结果规则尚待确定。这与 eBPF 外部 CALL 的当前边界一致。

## 5. 不产生 Expr 的指令

下表的本轮 Expr 函数为

\[
\operatorname{value}(E_g,i)=\varnothing,\qquad E_g'=E_g,
\]

以指令合法且所需输入与访问有效为前提。

| 分类 | 指令实例 | 本轮处理 |
|---|---|---|
| 只产生 Predicate | BEQ、BNE、BLT、BGE、BLTU、BGEU | 比较条件属于后续 Predicate，不新增条件 Expr |
| 只产生 Predicate | C_BEQZ、C_BNEZ | 同上 |
| 只产生 Predicate | 已识别为返回的无链接 JALR、C.JR | 返回观察由后续规则确定；不新增返回值赋值 |
| 只产生 Predicate | 有效普通 LOAD 且 rd=x0 | 结果丢弃，访问 Predicate 保留 |
| 两者都不产生 | 普通 JAL 且 rd=x0、C_J | 仅触发后继重排 |
| 两者都不产生 | 未识别为返回或外部调用的无链接 JALR、C_JR | 后继处理留给控制规则 |
| 两者都不产生 | FENCE、FENCE_TSO | 按已约定的不可见屏障抽象 |
| 两者都不产生 | NOP、C_NOP、已识别的合法 HINT | 不添加数据、PC 或计数器 Expr |

NOP 是 ADDI x0,x0,0 的伪指令，不新增 Sail 构造器。其他未写任何可变真实标记的合法数据指令按实际效果返回空集。

是否属于返回或外部调用须有相应明确规则，不能把每条 C.JR/JALR 都当成返回。分支、返回所需值的确定性仍由各自规则核对。

PC 作为真实寄存器的身份不变。本轮不定义顺序 PC、条件 PC 或跳转目标 Expr，只保留第 3 节中真正需要 PC 作为源的数值计算。

## 6. 拒绝项与定义边界

| 构造器或情形 | 处理 |
|---|---|
| ECALL、EBREAK、C_EBREAK | 按异常范围拒绝；外部接口的重新解释须先有明确规则 |
| MRET、SRET、WFI、SFENCE_VMA | 超出本次 RV32IMC 投影，拒绝 |
| ILLEGAL、C_ILLEGAL、保留编码、未启用扩展 | 拒绝 |
| 必需源等式缺失或违反关系键唯一条件 | 拒绝 |
| 没有唯一虚拟标记、访问越出已允许范围、会触发异常的访问 | 拒绝 |
| 局部虚拟写入没有足够信息确定完整新值 | 拒绝 |
| 未解析的变元间接跳转目标 | 沿用拒绝策略；目标核对由后续控制规则完成 |
| 虚拟标记与指令字段的精确匹配 | 待与 Predicate 语义一并完成 |
| 外部调用的返回值、Map 结果及失效规则 | 待对应运行时规则确定 |

RV32C 的非零立即数限制、寄存器限制和移位量限制必须先核对。C.LWSP 的零目标、C.JR 的零基址、C.LUI 的零立即数等不能套普通值函数。合法 HINT、保留编码、其他扩展专用编码分别处理。

FENCE.TSO 在 RV32I 文档中作为 FENCE 的特定编码定义；本文按既定屏障抽象返回空集，不把它仅因 Sail 单独提供 FENCE_TSO 构造器就视为缺失或自动拒绝。

除零、有符号除法溢出和整数加减乘的取模结果均由前文值函数确定，不属于此表的异常拒绝。

## 7. 构造器覆盖核对与 Lean4 对应

### 7.1 全部 49 个给定 Sail 构造器

以下清单逐个登记用户提供的 execute 分支。构造器数量不等于指令助记符数量；UTYPE、RTYPE 等包含多个操作变体。

| 构造器 | 定义或处理位置 |
|---|---|
| UTYPE | 3.1 |
| ITYPE | 3.2 |
| SHIFTIOP | 3.2 |
| RTYPE | 3.3 |
| MUL | 3.4 |
| DIV | 3.5 |
| REM | 3.5 |
| JAL | 3.7、5 |
| JALR | 3.7、5、6 |
| BTYPE | 5 |
| LOAD | 4.1、5 |
| STORE | 4.2、4.3 |
| FENCE | 5 |
| FENCE_TSO | 5、6 |
| ECALL | 4.4、6 |
| EBREAK | 6 |
| MRET | 6 |
| SRET | 6 |
| WFI | 6 |
| SFENCE_VMA | 6 |
| ILLEGAL | 6 |
| C_ADDI4SPN | 3.6 |
| C_ADDI | 3.6、5 |
| C_LI | 3.6、5 |
| C_ADDI16SP | 3.6 |
| C_LUI | 3.6、5、6 |
| C_SRLI | 3.6、5、6 |
| C_SRAI | 3.6、5、6 |
| C_ANDI | 3.6 |
| C_SUB | 3.6 |
| C_XOR | 3.6 |
| C_OR | 3.6 |
| C_AND | 3.6 |
| C_SLLI | 3.6、5、6 |
| C_MV | 3.6、5 |
| C_ADD | 3.6、5 |
| C_LW | 4.1 |
| C_SW | 4.2、4.3 |
| C_LWSP | 4.1、6 |
| C_SWSP | 4.2、4.3 |
| C_JAL | 3.7 |
| C_JALR | 3.7、6 |
| C_J | 5 |
| C_JR | 5、6 |
| C_BEQZ | 5 |
| C_BNEZ | 5 |
| C_NOP | 5 |
| C_EBREAK | 6 |
| C_ILLEGAL | 6 |

表内每个构造器都有已定义值函数、成功空集规则或明确拒绝/待定边界。登记齐全不意味着尚未确定的定位、外部调用和控制规则已经完成。

### 7.2 对象对应

Instruction 沿用 Sail 的带类型构造器；Expr 沿用共同对象；\(E_g,E_i\) 对应满足键唯一条件的有限集合；key 是键投影；\(\times\) 过滤旧同键项后加入新项。

压缩编号映射与立即数恢复属于指令字段解释。数值公式定义形式运算符及其解释，solve 采用共同规则。这里不引入机器状态记录、虚拟传值函数或新的运行输入。

## 8. 规范依据

- [RV32I 2.1](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html)：整数运算、立即数、链接值、load/store、零寄存器与 FENCE。
- [M 2.0](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html)：乘法高半、除零、溢出与向零除法。
- [C 2.0](https://docs.riscv.org/reference/isa/v20260120/unpriv/c-st-ext.html)：压缩运算、寄存器映射、链接长度及合法编码。

这些指令事实按规范核对；虚拟栈/Map 投影、选择的 Predicate 范围、按关系键覆写和未定义输入拒绝是已约定的研究模型。
