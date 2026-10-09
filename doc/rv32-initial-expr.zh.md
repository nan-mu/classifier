# RV32 入口关系：构造、相容性与唯一性

本文给出 XDP 入口的符号关系集合 \(\mathcal E_0\)，并证明其有限性、位宽一致性与关系键唯一性。Reg 采用[寄存器文档](registers.md)的定义；Term、符号提升及覆写采用 [共同数学基础](common-math.md)。

入口关系以调用环境已经建立、目标程序尚未执行为时刻。调用环境的赋值与资源有效性是前提；本文不从一般机器状态推导这些前提。输入包与 Map 的后续行为也不由初态关系单独确定。

## 1. 入口项与假设

给定以下 \(\mathrm{Term}_{32}\) 中的项：

- \(t_{\mathrm{ctx}}\)：上下文对象起始地址。
- \(t_{\mathrm{data}}\)、\(t_{\mathrm{len}}\)：输入包起始地址与字节长度。
- \(t_{\mathrm{sp}}\)：入口栈指针。
- \(t_{\mathrm{return}}\)：外层正常返回位置。
- \(t_{\mathrm{frame}}\)：调用环境保存区起始地址。
- \(t_{\mathrm{entry}}\)：目标程序入口位置。

确定输入可取常元，符号输入可取固定名称变元。同一来源复用同一项；这些项不引用随后会变化的寄存器。

**假设 I。** 入口项位宽正确；调用环境满足其对齐、资源与调用有效性条件；本文规定的寄存器赋值就是入口时的赋值。资源条件的完整形式保留为模型参数。

定义包结束地址项

\[
t_{\mathrm{end}}
=\mathrm{ADD}_{32}^{\star}(t_{\mathrm{data}},t_{\mathrm{len}}).
\]

给定 \(\iota_{\mathrm{wifi}}\in\mathbb B_{32}\) 作为接口编号常量。模加法只确定 32 位地址模式；若要解释为不回绕的地址区间，还须加入对实际地址与长度的有效性条件。

## 2. 真实寄存器关系

### 2.1 基础赋值

寄存器别名采用同一标记，例如 \(\mathrm{sp}=x_2\)、\(\mathrm{ra}=x_1\)。令

\[
R_s=\{\mathrm{s0},\ldots,\mathrm{s11}\}.
\]

对 \(r\in R_s\cup\{\mathrm{gp},\mathrm{tp}\}\)，给定入口项 \(t_r\in\mathrm{Term}_{32}\)。未知值使用各自固定的输入名称。

定义基础关系集合

\[
\begin{aligned}
\mathcal E_{\mathrm{base}}={}&
\{\mathrm{Real}_{32}(\mathrm{zero})=C_{32}(0),\
\mathrm{Real}_{32}(\mathrm{ra})=t_{\mathrm{return}},\
\mathrm{Real}_{32}(\mathrm{sp})=t_{\mathrm{sp}},\\
&\mathrm{Real}_{32}(\mathrm{t0})=t_{\mathrm{sp}},\
\mathrm{Real}_{32}(\mathrm{t1})=t_{\mathrm{return}},\
\mathrm{Real}_{32}(\mathrm{t2})=t_{\mathrm{frame}},\
\mathrm{Real}_{32}(\mathrm{a0})=t_{\mathrm{ctx}}\}\\
&\cup\{\mathrm{Real}_{32}(r)=t_r:r\in R_s\cup\{\mathrm{gp},\mathrm{tp}\}\}.
\end{aligned}
\]

\(\mathrm{t0}\) 与 SP 具有相同入口值，\(\mathrm{t1}\) 与 RA 具有相同返回值项。这些是入口关系，不表示两个不同寄存器具有相同身份。目标程序尚未执行，所以不预设 \(\mathrm{s0}=\mathrm{sp}\)。

### 2.2 承载入口位置的寄存器

令 \(r_{\mathrm{entry}}\) 为承载入口位置的真实寄存器标识，并满足调用环境约束。本文取其允许范围为

\[
r_{\mathrm{entry}}\in
\{\mathrm{ra}\}\cup R_s\cup\{\mathrm{a1},\ldots,\mathrm{a7}\}
\cup\{\mathrm{t3},\ldots,\mathrm{t6}\}.
\]

调用建立返回地址后，若该标识为 RA，其入口位置旧值已被返回地址覆盖；其他允许标识仍保留入口位置项。定义

\[
\mathcal E_{\mathrm{real},0}=
\begin{cases}
\mathcal E_{\mathrm{base}},&r_{\mathrm{entry}}=\mathrm{ra},\\[2pt]
\operatorname{updateExpr}\left(\mathcal E_{\mathrm{base}},
\{\mathrm{Real}_{32}(r_{\mathrm{entry}})=t_{\mathrm{entry}}\}\right),
&r_{\mathrm{entry}}\ne\mathrm{ra}.
\end{cases}
\]

若承载标识属于保存寄存器，普通等式被替换，不同时保留两份完整值定义。未在构造中出现的真实寄存器没有入口等式，读取这些缺失值仍不满足值函数定义域。

## 3. 上下文六槽关系

标准 \(\mathrm{xdp\_md}\) 上下文包含六个连续 32 位字段：data、data_end、data_meta、ingress_ifindex、rx_queue_index、egress_ifindex。第 \(j\) 个字段的字节偏移为 \(4j\)。本文规定其初值向量为

\[
(u_0,u_1,u_2,u_3,u_4,u_5)
=(t_{\mathrm{data}},t_{\mathrm{end}},C_{32}(0),
C_{32}(\iota_{\mathrm{wifi}}),C_{32}(0),C_{32}(0)).
\]

这些初值属于本入口模型的假设；字段布局本身不确定这些值。

给定互不相同的虚拟栈标识 \(\alpha_{\mathrm{ctx},0},\ldots,\alpha_{\mathrm{ctx},5}\)。

**假设 II（上下文绑定）。** 地址项

\[
\mathrm{ADD}_{32}^{\star}(t_{\mathrm{ctx}},C_{32}(4j))
\]

对应字段的访问唯一绑定到 \(\mathrm{SW}(\alpha_{\mathrm{ctx},j})\)，且访问有效。绑定与资源观察的完整语义需另外给定；Expr 本身只记录值关系。

定义

\[
\boxed{
\mathcal E_{\mathrm{ctx},0}
=\{\mathrm{SW}(\alpha_{\mathrm{ctx},j})=u_j:0\le j<6\}.
}
\]

\(u_j\) 只是右侧项的记法，不构成额外字段状态。后续若有合法字段更新，应覆写相应值关系；入口项仍表示原始输入。本文的初态构造不保证任意后续字段写入都有定义。

## 4. 初态及其性质

给定有限入口谓词集合 \(\mathcal P_0\)，定义

\[
\boxed{
\mathcal E_0=\mathcal E_{\mathrm{real},0}\cup\mathcal E_{\mathrm{ctx},0},
\qquad\sigma_0=(\mathcal E_0,\mathcal P_0).
}
\]

\(\mathcal P_0\) 的观察类型与解释采用[Predicate 文档](predicates.md)的定义；若无额外入口观察，可取 \(\mathcal P_0=\varnothing\)。本构造不凭空添加观察，扩展入口假设时须另行规定其含义。

**命题 I1（有限性与位宽）。** 假设 I、II 成立时，\(\mathcal E_0\in\mathscr F(\mathrm{Expr})\)，每个关系均为完整的 32 位等式。

**证明。** 基础赋值包含有限个真实标识，覆写至多添加一个目标；上下文有六个标识。所有入口项为 32 位，模加法与常元也为 32 位。两部分的每个左侧标记均为 32 位，故每个等式类型正确且总集合有限。\(\square\)

**命题 I2（键唯一性）。** \(\mathcal E_0\) 满足同键关系唯一。

**证明。** 基础赋值中的真实寄存器身份互异，别名不重复加入；按键覆写保持唯一性。上下文六个栈标识互异，故内部键唯一。Real 与 Stack 是不交类别，两部分没有公共键，因此它们的并集仍有效。\(\square\)

**命题 I3（基数）。**

\[
|\mathcal E_0|=
\begin{cases}
27,&r_{\mathrm{entry}}\in\{\mathrm{ra}\}\cup R_s,\\
28,&r_{\mathrm{entry}}\in\{\mathrm{a1},\ldots,\mathrm{a7},\mathrm{t3},\ldots,\mathrm{t6}\}.
\end{cases}
\]

**证明。** \(\mathcal E_{\mathrm{base}}\) 有 \(7+12+2=21\) 个真实键。第一种情形不增加键，第二种增加一个原本不存在的真实键；上下文六键与真实键不交。\(\square\)

**命题 I4（入口关系可满足）。** 对每个变元赋值 \(\nu\)，存在寄存器赋值 \(\rho\) 使 \(\mathcal E_0\) 的全部等式成立。

**证明。** 对每个已定义标记，将 \(\rho\) 指定为其唯一右侧项在 \(\nu\) 下的解释。命题 I2 保证没有冲突。其余寄存器任选满足其位宽与类别值域的值即可；未出现的包标记可取零。\(\square\)

该命题只证明 Expr 的代数相容性，不证明入口谓词可满足、资源有效或调用环境真实存在。

## 5. 适用边界与依据

未初始化局部栈槽不补零，未出现的真实寄存器不补任意值。本文的 \(\mathcal E_0\) 不含包字节关系，其基数结论不计入后续引入的包标记。输入单元的引入与四类访问规则见[寄存器分类文档](registers.md)第 2—6 节。初态本身不定义 Map 访问或外部调用，也不证明 RV32 与 eBPF 入口观察等价。

上下文字段布局见 [Linux UAPI 的 xdp_md 定义](https://github.com/torvalds/linux/blob/master/include/uapi/linux/bpf.h)。真实寄存器入口赋值、接口编号与字段初值由本文的入口契约规定，不是由该布局自动推导的事实。
