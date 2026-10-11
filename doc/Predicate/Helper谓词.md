# Helper谓词

## 类型定义

Helper谓词是 `Predicate` 中 `helper` 类的元素，其类型为：

\[
\mathrm{Helper}_{32}
:=\bigsqcup_{h\in H}
\bigl(\mathcal I_{\mathrm{call}}\times\{h\}\times\mathrm{Term}_{32}^{n(h)}\bigr).
\]

其中 \(\bigsqcup\) 表示保留类型标签的不交并，\(h\in H\) 为 helper 类型，\(\{h\}\) 为该类型的单元素集合，\(\times\) 为笛卡尔积；\(\mathcal I_{\mathrm{call}}\) 为动态调用身份集合，\(\mathrm{Term}_{32}\) 为 32 位有限符号项集合，\(\mathrm{Term}_{32}^{n(h)}\) 为长度恰好是 \(n(h)\) 的参数向量集合。调用身份与 helper 类型是结构标记，不赋予机器位宽。

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

\(H\) 另含确定的未支持编号对应的类型 \(\operatorname{unsupported}(k)\)，其中 \(k\in\mathbb B_{32}\setminus\{1,2,3,5,6,28,65\}\)，规定其编号为 \(k\)、\(n=0\)。它不是七种已支持 helper 的额外契约。

令 \(\varepsilon\) 为本次动态调用的唯一身份，属于 \(\mathcal I_{\mathrm{call}}\)：不同调用步骤取不同身份，循环中再次执行同一指令位置也不复用旧身份。同一候选的谓词及结果项使用同一个 \(\varepsilon\)。

令 \(\vec t=(t_1,\ldots,t_{n(h)})\) 为参数向量，其中每个 \(t_j\) 为 32 位参数项；参数个数为零时，向量为空。Helper谓词记作 \(\operatorname{helper}(\varepsilon,h,\vec t)\)，其调用身份、类型及参数向量均参与结构相等。

### Helper谓词的解释

\(\nu\) 为项中变元的赋值族，将 32 位变元映到 \(\mathbb B_{32}\)；\(\theta\) 为未解释运算的解释补全，按运算符签名提供同位宽的值函数。\(\left[\!\left[\cdot\right]\!\right]_{\nu,\theta}\) 为固定该赋值与补全后的解释，\(\mathsf{helper}\) 为事件的类别标签。

Helper谓词解释为事件记录，而不是布尔条件：

\[
\left[\!\left[\operatorname{helper}(\varepsilon,h,\vec t)\right]\!\right]_{\nu,\theta}
:=\bigl(\mathsf{helper},\varepsilon,h,
\left[\!\left[\vec t\right]\!\right]_{\nu,\theta}\bigr),
\]

其中向量解释逐项进行。事件身份区分具体调用，\(h\) 记录 helper 类型，参数项记录调用前取得的值。

## 触发逻辑

### RV32IMC

当前 RV32IMC 指令为链接寄存器 \(x_1\) 的 `JAL` 或 `JALR`，或为 `C.JAL` 或 `C.JALR`，且指令参数合法、当前位置具有机器地址绑定、调用目标已确定并等于既定 helper 分派器地址时，触发Helper谓词构造。

已绑定 helper 的局部观察规则见[生成指令局部效果](../NodeInference/推理过程.md)。外部调用分类见[控制转移与返回识别](../NodeInference/Jump/待处理.md)。

### eBPF

一般 eBPF helper 与 BTF CALL 的Helper谓词构造无定义，见[指令参数与规则定义域](../NodeInference/推理过程.md#局部规则的合法域)。

## 生成条件

\(E_g=(\mathcal V_g,\mathcal C_g)\) 为执行前的有效 [Expr 关系](../Expr/表达式定义.md#表达式分量)。\(P_g\) 为执行前的[观察集合](谓词定义.md#类型与结构相等)。\(\mathcal V_g\) 为有限完整值绑定集合，\(\mathcal C_g\) 为有限比较关系集合；\(P_g\) 是状态的有限谓词集合。

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

满足前提时，生成Helper谓词及局部观察集合：

\[
\boxed{
\operatorname{makeHelperPredicate}(\varepsilon,E_g)
:=p=\operatorname{helper}(\varepsilon,h,\vec t),
\qquad \mathcal P_i=\{p\}.
}
\]

\(\operatorname{makeHelperPredicate}\) 为以本次调用身份和执行前 Expr 关系为输入的部分构造，\(p\) 为生成的Helper谓词，\(\mathcal P_i\) 为本步骤的局部谓词增量。

### 错误类型

已选定 helper 分派的步骤在下列任一情形下构造无定义，不生成谓词或局部观察集合，必须[拒绝本次处理](../NodeInference/推理过程.md)并保留当前图：

- 必需的调用绑定缺失或不唯一。
- \(E_g\) 无效。
- \(a_0\) 或任一所需 \(a_j\) 的完整等式缺失、不唯一，或位宽不符。
- \(D_{32}(\operatorname{solve}(u_0))\) 无定义。

确定的未支持编号不属于上述失败情形，其类型为 \(\operatorname{unsupported}(k)\)。

## 数学性质

**命题 H1（生成的唯一性与参数齐备）。** 在有效 \(E_g\)、既定调用绑定及固定 \(\varepsilon\) 下，成功生成的 helper Predicate 唯一，并具有恰好 \(n(h)\) 个 32 位参数项。

**证明。** 编号求值确定，七个编号互异，因此 \(h\) 唯一。完整等式的键唯一使每个参数项唯一，solve 是确定的；构造逐一取得所需的 \(n(h)\) 个项。\(\square\)

**命题 H3（动态调用区分）。** 若 \(\varepsilon\ne\varepsilon'\)，则 \(\operatorname{helper}(\varepsilon,h,\vec t)\ne\operatorname{helper}(\varepsilon',h,\vec t)\)，两谓词在集合合并后均保留。

**证明。** 事件身份是结构相等的一部分，两谓词不同；并集包含两者。\(\square\)

## 相关文档

- [helper 的 Expr](../Expr/辅助调用结果.md)
- [检查源项与资源绑定](../NodeInference/推理过程.md)
- [指令参数与规则定义域](../NodeInference/推理过程.md#局部规则的合法域)
- [符号项求值与常量折叠](../Expr/符号项求值与常量折叠.md)
- [右值与项解释](../Expr/右值.md)
