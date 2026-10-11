# Helper谓词

## 类型定义

Helper谓词是 `Predicate` 中 `helper` 类的元素，其类型为：

\[
\mathrm{Helper}:=\mathrm{MapLookup}\sqcup\mathrm{MapUpdate}
\sqcup\mathrm{MapDelete}\sqcup\mathrm{OtherHelper}.
\]

其中 \(\sqcup\) 保留四个构造的类别标签；MapLookup、MapUpdate、MapDelete 分别记录查询、更新、删除 Map 的调用参数，OtherHelper 保留其他 helper 的调用记录。调用身份与 helper 类型是结构标记，不赋予机器位宽。

四类谓词的定义、解释与专用规则分别见：

- [MapLookup谓词](MapLookup谓词.md)
- [MapUpdate谓词](MapUpdate谓词.md)
- [MapDelete谓词](MapDelete谓词.md)
- [OtherHelper谓词](OtherHelper谓词.md)

32 位分派约定为：\(a_0=\mathrm{Real}_{32}(10)\) 保存 helper 编号，\(a_j=\mathrm{Real}_{32}(10+j)\)（\(1\le j\le5\)）保存附加参数，返回寄存器为 \(r_{\mathrm{ret}}=a_0\)。这是指定调用约定，不将原生 eBPF 的参数位置与此约定混同。

\(\mathrm{Real}_{32}\) 为按机器寄存器编号构造真实寄存器标记的记号；\(a_0\)、\(a_j\) 与 \(r_{\mathrm{ret}}\) 均属于 32 位真实寄存器集合，其值域为 \(\mathbb B_{32}\)，即 32 位位向量集合。下标 \(j\) 为附加参数的位置。

类型集合 \(H\) 包含以下七个带名称的类型。编号函数 \(\operatorname{id}:H\to\mathbb B_{32}\) 与参数个数 \(n:H\to\mathbb N\) 定义为：

- `BPF_FUNC_MAP_LOOKUP_ELEM`：编号 1，参数 \((a_1,a_2)\)，\(n=2\)。
- `BPF_FUNC_MAP_UPDATE_ELEM`：编号 2，参数 \((a_1,a_2,a_3,a_4)\)，\(n=4\)。
- `BPF_FUNC_MAP_DELETE_ELEM`：编号 3，参数 \((a_1,a_2)\)，\(n=2\)。
- `BPF_FUNC_KTIME_GET_NS`：编号 5，无附加参数，\(n=0\)。
- `BPF_FUNC_TRACE_PRINTK`：编号 6，参数 \((a_1,a_2,a_3,a_4,a_5)\)，\(n=5\)。
- `BPF_FUNC_CSUM_DIFF`：编号 28，参数 \((a_1,a_2,a_3,a_4,a_5)\)，\(n=5\)。
- `BPF_FUNC_XDP_ADJUST_TAIL`：编号 65，参数 \((a_1,a_2)\)，\(n=2\)。

\(\operatorname{id}\) 给出类型的 32 位分派编号，\(n\) 给出所需附加参数的数量，\(\mathbb N\) 为包含零的自然数集合；这里的参数个数不包含编号寄存器 \(a_0\)。时钟类型也必须读取 \(a_0\)，但不要求 \(a_1,\ldots,a_5\) 已定义。

\(H\) 另含确定的未支持编号对应的类型 \(\operatorname{unsupported}(k)\)，其中 \(k\in\mathbb B_{32}\setminus\{1,2,3,5,6,28,65\}\)，规定其编号为 \(k\)、\(n=0\)。

令 \(\varepsilon\) 为本次动态调用的唯一身份，属于 \(\mathcal I_{\mathrm{call}}\)：不同调用步骤取不同身份，循环中再次执行同一指令位置也不复用旧身份。同一候选的谓词及结果项使用同一个 \(\varepsilon\)。

Map 三个构造的全部分量及字节数组顺序也参与结构相等。

### 字节项数组

\(\mathrm{BytesTerm}(n)\) 是长度恰好为 \(n\in\mathbb N\) 的有序字节符号项数组：

\[
\mathrm{BytesTerm}(n):=
\left\{(b_1,\ldots,b_n)\in\mathrm{Term}_{32}^{n}:
\forall(\nu,\theta)\ \forall j\in\{1,\ldots,n\},\
\llbracket b_j\rrbracket_{\nu,\theta}\in\mathbb B_8
\right\}.
\]

其中 \(b_j\) 为第 \(j\) 个 32 位有限符号项，\(\nu,\theta\) 遍历 [Expr 项解释](../Expr/待处理.md#右值)允许的赋值与解释补全，\(\mathbb B_8\subset\mathbb B_{32}\) 是[字节值域](../寄存器定义.md)。每项承载一个 8 位字节，高 24 位为零。数组的位置从 1 开始；\(n=0\) 时数组为空。数组按位置逐项结构相等，重复项保留。

字节项沿用[包字节的 32 位项表示](../Expr/待处理.md#读取拼接与写入拆分)。从较宽单元取得字节时，使用[字段投影与零扩展](../Expr/待处理.md#单元字段读写)的 \(q=8,v=32\) 实例；从已有包字节项取得字节时，使用[零扩展](../Expr/待处理.md#截取与扩展)的 \(Z_{8\to32}^{(32),\star}\) 固定字节语义。这些运算保留调用时的符号值表达式，不要求折叠为常元。

在固定 \((\nu,\theta)\) 下，字节数组的解释为：

\[
\llbracket(b_1,\ldots,b_n)\rrbracket_{\nu,\theta}
:=(\llbracket b_1\rrbracket_{\nu,\theta},\ldots,
\llbracket b_n\rrbracket_{\nu,\theta})\in\mathbb B_8^n.
\]

其中左侧为 \(\mathrm{BytesTerm}(n)\) 数组的逐项解释，右侧为长度恰好是 \(n\) 的有序字节值数组；\(\nu,\theta\) 与字节项类型定义中的解释参数相同。

### 解释参数

\(\nu\) 为[项解释](../Expr/待处理.md#右值)中的赋值族，将各位宽变元映到相应的 \(\mathbb B_w\)，其中 \(w\in\{32,64\}\)；\(\theta\) 为未解释运算的解释补全，按运算符签名提供值函数。\(\left[\!\left[\cdot\right]\!\right]_{\nu,\theta}\) 为固定该赋值与补全后的解释。

## 触发逻辑

### RV32IMC

当前 RV32IMC 指令为链接寄存器 \(x_1\) 的 `JAL` 或 `JALR`，或为 `C.JAL` 或 `C.JALR` 时，检查以下调用条件：

- 指令参数合法。
- 当前位置具有机器地址绑定。
- 调用目标已确定并等于既定 helper 分派器地址。

这些条件成立时，按分派编号选择 Helper 的四个构造。

已绑定 helper 的局部观察规则见[生成指令局部效果](../NodeInference/step.md)。外部调用分类见[控制转移与返回识别](../NodeInference/Jump/待处理.md)。

### eBPF

一般 eBPF helper 与 BTF CALL 的Helper谓词构造无定义，见[指令参数与规则定义域](../NodeInference/step.md#局部规则的合法域)。

## 生成条件

\(E_g\) 为执行前的有效 [Expr 关系](../Expr/待处理.md#表达式分量)，其完整值绑定分量为 \(\mathcal V_g\)。\(P_g\) 为执行前的[观察集合](谓词定义.md#类型与结构相等)。\(\Gamma\) 为本次处理显式给定的[资源绑定](../Expr/待处理.md#分类所需的输入)；三个 Map 构造还从中取得唯一绑定对象的已知 Map 布局。

分派编号要求 \(\mathcal V_g\) 中存在唯一的完整等式 \(a_0=u_0\)，且其右侧项经求值确定类型 \(h\in H\)：

\[
(a_0=u_0)\in\mathcal V_g,\qquad u_0\in\mathrm{Term}_{32},
\qquad D_{32}(\operatorname{solve}(u_0))=\operatorname{id}(h).
\]

\(u_0\) 为编号寄存器的 32 位右侧项；\(\operatorname{solve}\) 为保留位宽的整项折叠，\(D_{32}\) 为 32 位项的部分数值求值，有定义时取值属于 \(\mathbb B_{32}\)。

每个所需参数要求同一 \(E_g\) 中存在唯一的完整等式 \(a_j=u_j\)，其中 \(1\le j\le n(h)\)：

\[
\forall j\in\{1,\ldots,n(h)\},\quad
(a_j=u_j)\in\mathcal V_g,\qquad u_j\in\mathrm{Term}_{32},
\qquad t_j=\operatorname{solve}(u_j)\in\mathrm{Term}_{32}.
\]

\(u_j\) 为第 \(j\) 个参数寄存器的 32 位右侧项，折叠后的项为参数向量中的 \(t_j\)。

只有低位关系或不等式不满足这个要求；Stack、Map、Packet 标记也不能替代所要求的真实参数寄存器。参数项可以是符号项，不要求数值可求。

未被该类型使用的参数不参与校验。

Helper谓词构造对 \(P_g\) 无成员前提。

满足共同前提及所选 Map 构造的生成条件时，生成 Helper 谓词：

\[
\operatorname{makeHelperPredicate}(\varepsilon,E_g,\Gamma):=
\begin{cases}
\operatorname{mapLookup}(\varepsilon,t_1,
\operatorname{readBytes}(\Gamma,E_g,t_2,L_k(\Gamma,t_1))),
&h=\mathrm{MAP\_LOOKUP},\\
\operatorname{mapUpdate}(\varepsilon,t_1,
\operatorname{readBytes}(\Gamma,E_g,t_2,L_k(\Gamma,t_1)),
\operatorname{readBytes}(\Gamma,E_g,t_3,L_v(\Gamma,t_1)),t_4),
&h=\mathrm{MAP\_UPDATE},\\
\operatorname{mapDelete}(\varepsilon,t_1,
\operatorname{readBytes}(\Gamma,E_g,t_2,L_k(\Gamma,t_1))),
&h=\mathrm{MAP\_DELETE},\\
\operatorname{helper}(\varepsilon,h,\vec t),&h\in H_{\mathrm{other}}.
\end{cases}
\]

其中 \(\operatorname{makeHelperPredicate}\) 是以调用身份、执行前 Expr 关系和资源绑定为输入、取值于 \(\mathrm{Helper}\) 的部分构造；\(h,t_j,\vec t\) 由同一 \(E_g\) 按上述编号与参数等式取得。三个 \(\mathrm{MAP\_*}\) 标签分别为编号 1、2、3 的已命名类型；\(H_{\mathrm{other}}\) 见[OtherHelper 类型定义](OtherHelper谓词.md#类型定义)。\(L_k(\Gamma,t_m)\)、\(L_v(\Gamma,t_m)\) 分别为 \(\Gamma\) 对 Map 参数项 \(t_m\) 唯一绑定对象给出的键、值字节长度；绑定或所需布局不确定时，相应长度无定义。\(\operatorname{readBytes}\) 的定义见[调用时的字节读取](#调用时的字节读取)。

成功生成 \(p=\operatorname{makeHelperPredicate}(\varepsilon,E_g,\Gamma)\) 后，本步骤的局部观察集合为：

\[
\mathcal P_i:=\{p\}.
\]

其中 \(p\in\mathrm{Helper}\) 为本次调用的观察，\(\mathcal P_i\) 为局部谓词增量。

### 调用时的字节读取

给定资源绑定 \(\Gamma\)、同一调用前关系 \(E_g\)、缓冲区地址项 \(t_b\in\mathrm{Term}_{32}\) 及所需字节数 \(n\in\mathbb N\)，定义部分读取：

\[
\operatorname{readBytes}(\Gamma,E_g,t_b,n)
:=(b_1,\ldots,b_n)\in\mathrm{BytesTerm}(n).
\]

其中 \(b_j\) 是从 \(t_b\) 所绑定缓冲区的第 \(j\) 个字节取得的有限符号值项，按内存地址递增排列；\(\Gamma\) 决定资源身份、规范单元、字节偏移和字节序，\(E_g\) 提供这些单元的完整旧值项。每个 \(b_j\) 依[字节项数组](#字节项数组)中的已有字节投影取得。

读取的定义域要求：

- \(\Gamma\) 将全部所需字节唯一归约到已有的资源单元及字段。
- 读取满足所属资源的访问条件。
- \(E_g\) 为每个所需单元提供唯一、位宽匹配的完整等式。
- 全部字节投影有定义。

保存的是调用时取得的有限符号项，而非供以后再次解引用的缓冲区地址。键和值均使用这个读取；生成时读取完整数组。后续覆写缓冲区不修改已保存的项。读取的资源归约、源项或投影不足时，\(\operatorname{readBytes}\) 无定义。

### 错误类型

已选定 helper 分派的步骤在下列任一情形下构造无定义，不生成谓词或局部观察集合，必须[拒绝本次处理](../NodeInference/step.md)并保留当前图：

- 必需的调用绑定缺失或不唯一。
- \(E_g\) 无效。
- \(a_0\) 或任一所需 \(a_j\) 的完整等式缺失、不唯一，或位宽不符。
- \(D_{32}(\operatorname{solve}(u_0))\) 无定义。

确定的未支持编号不属于上述失败情形，其类型为 \(\operatorname{unsupported}(k)\)，属于 [OtherHelper](OtherHelper谓词.md#类型定义)。

## 数学性质

OtherHelper 生成的唯一性与参数齐备见[命题 H1](OtherHelper谓词.md#数学性质)。

**命题 H3（动态调用区分）。** 同一种 Helper 构造的两个元素若调用身份 \(\varepsilon\ne\varepsilon'\)，则两谓词不同，在集合合并后均保留。

**证明。** 四个构造均将事件身份作为结构相等的一部分，两谓词不同；并集包含两者。\(\square\)

**命题 H4（保存的字节项保持）。** 已生成的 Map 谓词在后续缓冲区覆写后，其字节数组及在同一 \((\nu,\theta)\) 下的解释保持不变。

**证明。** \(\operatorname{readBytes}\) 的结果保存有限项。后续[按键覆写](../Expr/待处理.md#关系集合按键覆写)只改变当前 Expr 绑定，不修改既有项。数组各分量的结构不变，其逐项解释在固定赋值和补全下不变。\(\square\)

**证明义务 H-B（字节读取与布局可靠性）。** 须证明给定 \(\Gamma\) 的 Map 对象绑定和布局与实际调用对象一致。须证明 \(\operatorname{readBytes}\) 的源项、字节顺序及访问条件准确描述实际调用时的全部缓冲区字节。跨规范单元和别名访问的一致性由[资源归约义务](../Expr/待处理.md#来源与结构性质)承担。缺少具体归约时，读取保持无定义，不补造字节项。

**证明义务 H-C（跨架构调用对应）。** 须给出动态调用身份、Map 对象参数及符号赋值的跨架构对应，并证明对应调用的冻结字节解释及其他参数值相符。结构相等和本篇的局部生成性质不提供该对应。

## 相关文档

- [helper 的 Expr](../Expr/待处理.md#辅助调用结果)
- [检查源项与资源绑定](../NodeInference/step.md)
- [指令参数与规则定义域](../NodeInference/step.md#局部规则的合法域)
- [符号项求值与常量折叠](../Expr/待处理.md#符号项求值与常量折叠)
- [右值与项解释](../Expr/待处理.md#右值)
