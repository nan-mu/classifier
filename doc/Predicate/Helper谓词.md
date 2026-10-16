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

RV32 的 32 位分派器约定为：\(a_0=\mathrm{Real}_{32}(10)\) 保存 helper 编号，\(a_j=\mathrm{Real}_{32}(10+j)\)（\(1\le j\le n(h)\)）保存附加参数，返回寄存器为 \(r_{\mathrm{ret}}=a_0\)。

原生 eBPF `call imm` 使用独立的 64 位约定：编号 \(k\in\mathbb B_{32}\) 由指令立即数提供，\(a_j=\mathrm{Real}_{64}(j)\)（\(1\le j\le n(h)\)）保存附加参数，返回寄存器为 \(r_{\mathrm{ret}}=\mathrm{Real}_{64}(0)\)。

\(\mathrm{Real}_w\) 为按机器编号构造真实寄存器标记的记号，载体宽度 \(w\) 在 RV32 中为 32，在原生 eBPF 中为 64；参数和返回寄存器的值域均为 \(\mathbb B_w\)。原生 eBPF 取得完整 64 位等式，不以寄存器低 32 位投影复用 RV32 分派规则。

两种约定使用相同的类型集合 \(H\)。编号函数 \(\operatorname{id}:H\to\mathbb B_{32}\) 与参数个数 \(n:H\to\mathbb N\) 定义为：

- `BPF_FUNC_MAP_LOOKUP_ELEM`：编号 1，\(n=2\)。
- `BPF_FUNC_MAP_UPDATE_ELEM`：编号 2，\(n=4\)。
- `BPF_FUNC_MAP_DELETE_ELEM`：编号 3，\(n=2\)。
- `BPF_FUNC_KTIME_GET_NS`：编号 5，\(n=0\)。
- `BPF_FUNC_TRACE_PRINTK`：编号 6，\(n=5\)。
- `BPF_FUNC_CSUM_DIFF`：编号 28，\(n=5\)。
- `BPF_FUNC_XDP_ADJUST_TAIL`：编号 65，\(n=2\)。

\(\operatorname{id}\) 给出 32 位类型编号，\(n\) 给出 ABI 参数数量，\(\mathbb N\) 为包含零的自然数集合；参数数量不包含编号。RV32 时钟调用仍须读取 \(a_0\) 的编号等式；原生 eBPF 时钟调用直接使用立即数编号。两者均不要求附加参数寄存器已定义。

\(H\) 另含确定的未支持编号对应的类型 \(\operatorname{unsupported}(k)\)，其中 \(k\in\mathbb B_{32}\setminus\{1,2,3,5,6,28,65\}\)，规定其编号为 \(k\)、\(n=0\)。

令 \(\varepsilon\) 为本次动态调用的唯一身份，属于 \(\mathcal I_{\mathrm{call}}\)：不同调用步骤取不同身份，循环中再次执行同一指令位置也不复用旧身份。同一候选的谓词及结果项使用同一个 \(\varepsilon\)。

Map 三个构造的全部分量及字节数组顺序也参与结构相等。

### 字节项数组

\(\mathrm{BytesTerm}_w(n)\) 是载体宽度 \(w\in\{32,64\}\)、长度恰好为 \(n\in\mathbb N\) 的有序字节符号项数组：

\[
\mathrm{BytesTerm}_w(n):=
\left\{(b_1,\ldots,b_n)\in\mathrm{Term}_{w}^{n}:
\forall(\nu,\theta)\ \forall j\in\{1,\ldots,n\},\
\llbracket b_j\rrbracket_{\nu,\theta}\in\mathbb B_8
\right\}.
\]

其中 \(b_j\) 为第 \(j\) 个 \(w\) 位有限符号项，\(\nu,\theta\) 遍历 [Expr 项解释](../Expr/Term/Term.md#term)允许的赋值与解释补全，\(\mathbb B_8\subset\mathbb B_w\) 是[位向量值集](../Expr/Term/位向量.md#位向量)的包含关系。每项承载一个 8 位字节，高 \(w-8\) 位为零。数组的位置从 1 开始；\(n=0\) 时数组为空。数组按位置逐项结构相等，重复项保留。既有记号 \(\mathrm{BytesTerm}(n)\) 表示 \(\mathrm{BytesTerm}_{32}(n)\)。

从较宽单元取得字节时，使用[字段投影与零扩展](../Expr/寄存器/单元字段读写.md#单元字段读写)的 \(q=8\) 实例，再按所选载体零扩展；从已有包字节项取得字节时，使用[零扩展](../Expr/Term/数值函数.md#截取与扩展)固定字节语义。读取单元的位宽与字节项的载体宽度分别确定。这些运算保留调用时的符号值表达式；能折叠为常元时，字节项为 \(C_w(c)\)，其中 \(0\le c<256\)。

在固定 \((\nu,\theta)\) 下，字节数组的解释为：

\[
\llbracket(b_1,\ldots,b_n)\rrbracket_{\nu,\theta}
:=(\llbracket b_1\rrbracket_{\nu,\theta},\ldots,
\llbracket b_n\rrbracket_{\nu,\theta})\in\mathbb B_8^n.
\]

其中左侧为 \(\mathrm{BytesTerm}_w(n)\) 数组的逐项解释，右侧为长度恰好是 \(n\) 的有序字节值数组；\(\nu,\theta\) 与字节项类型定义中的解释参数相同。

### 解释参数

\(\nu\) 为[项解释](../Expr/Term/Term.md#term)中的赋值族，将各位宽变元映到相应的 \(\mathbb B_w\)，其中 \(w\in\{32,64\}\)；\(\theta\) 为未解释运算的解释补全，按运算符签名提供值函数。\(\left[\!\left[\cdot\right]\!\right]_{\nu,\theta}\) 为固定该赋值与补全后的解释。

## 触发逻辑

### RV32IMC

当前 RV32IMC 指令为链接寄存器 \(x_1\) 的 `JAL` 或 `JALR`，或为 `C.JAL` 或 `C.JALR` 时，检查以下调用条件：

- 指令参数合法。
- 当前位置具有机器地址绑定。
- 调用目标已确定并等于既定 helper 分派器地址。

这些条件成立时，按分派编号选择 Helper 的四个构造。

已绑定 helper 的局部观察规则见[生成指令结果](../NodeInference/step.md#生成指令结果)。

### eBPF

操作码 `0x85` 且 `dst=src=off=0` 的 `call imm` 触发原生 helper 调用，立即数作为 32 位编号。按[共同类型与参数数量](#类型定义)选择 \(h\)，并按[生成条件](#生成条件)从执行前关系取得所需完整参数。调用必须具有下一原始槽位；成功时生成调用观察、[返回效果及 lookup 关联](#生成的-expr)，沿 OK 方向到达下一槽位。其余 `0x85` 形式、BTF CALL 与 CALLX 不在该规则的定义域内。

## 生成条件

\(E_g\) 为执行前的有效 [Expr 关系](../Expr/Expr.md#表达式分量)，其完整值绑定分量为 \(\mathcal V_g\)。\(P_g\) 为执行前的[观察集合](谓词定义.md#类型与结构相等)。调用约定确定载体宽度 \(w\)、参数标记 \(a_j\) 与返回标记 \(r_{\mathrm{ret}}\)，见[类型定义](#类型定义)。

RV32 分派编号要求 \(\mathcal V_g\) 中存在唯一的完整等式 \(a_0=u_0\)，且其右侧项经求值确定编号：

\[
(a_0=u_0)\in\mathcal V_g,\qquad u_0\in\mathrm{Term}_{32},
\qquad k=D_{32}(\operatorname{solve}(u_0))\in\mathbb B_{32}.
\]

\(u_0\) 为编号寄存器的 32 位右侧项；\(\operatorname{solve}\) 为[化简函数](../Expr/Term/solve.md#化简规则)，\(D_{32}\) 为 32 位项的部分数值求值。原生 eBPF 的 \(k\) 直接取自 `call imm` 的立即数，不读取编号寄存器。两种约定均选择满足 \(\operatorname{id}(h)=k\) 的唯一 \(h\in H\)，包括未支持类型。

每个所需参数要求同一 \(E_g\) 中存在唯一的完整等式 \(a_j=u_j\)，其中 \(1\le j\le n(h)\)：

\[
\forall j\in\{1,\ldots,n(h)\},\quad
(a_j=u_j)\in\mathcal V_g,\qquad u_j\in\mathrm{Term}_{w},
\qquad t_j=\operatorname{solve}(u_j)\in\mathrm{Term}_{w}.
\]

\(u_j\) 为第 \(j\) 个参数寄存器的完整右侧项，折叠后的项为 ABI 参数向量 \(\vec t=(t_1,\ldots,t_{n(h)})\) 的第 \(j\) 项。

只有低位关系或不等式不满足这个要求；Stack、Map、Packet 标记也不能替代所要求的真实参数寄存器。参数项可以是符号项，不要求数值可求。未被该类型使用的参数不参与校验。共同构造对 \(P_g\) 无成员前提。

ABI 调用观察保存调用身份、类型及完整 ABI 参数前缀；共同取源成功即可生成该观察及返回效果。冻结读取采用[调用时的字节读取](#调用时的字节读取)，范围可以横跨已有规范单元，资源可以是唯一可解析的 Stack、Map、Packet 或具有显式绑定的 Context 缓冲区。Stack、Map、Context 单元的字节项来自调用时已有的唯一、位宽匹配的完整等式，Context 另需显式入口绑定。Packet 单元在调用时未记录（既无完整等式也无比较关系）时，按[未记录虚拟寄存器的取源](../Expr/Expr.md#未记录虚拟寄存器的取源)依输入契约引入 `low 8 (inputByte κ [base, base+o])` 项，前提为调用时包基绑定与所需字节范围成立；其中 `κ` 为包身份，`base` 为包基项，`o` 为该字节相对包基的偏移。已记录的 Packet 字节必须复用当前关系，不得重新取入口输入；仅有比较关系而无完整等式时，读取无定义。该输入契约补充只对 Packet 成立，Stack、Map、Context 仍不补造字节项。整个观察参数数组使用同一载体宽度：RV32 为 32，原生 eBPF 为 64；冻结尾与 ABI 前缀同宽。

令 \(\vec k,\vec v\) 分别为完整键、值读取结果，\(\mathbin{+\!\!+}\) 表示有序列表拼接。ABI 观察参数列表为

\[
\operatorname{args}(h,\vec t):=
\begin{cases}
\vec t\mathbin{+\!\!+}\vec k,&h\in\{\mathrm{MAP\_LOOKUP},\mathrm{MAP\_DELETE}\}\text{ 且键读取有定义},\\
\vec t\mathbin{+\!\!+}\vec k\mathbin{+\!\!+}\vec v,&h=\mathrm{MAP\_UPDATE}\text{ 且键、值读取均有定义},\\
\vec t,&\text{其余情形}.
\end{cases}
\]

Map 布局须唯一确定完整长度。更新时任一读取无定义，就保留原 ABI 前缀，不追加半个冻结尾。布局缺失、布局歧义、资源解析不唯一或旧内容不齐全均保持前缀，不因此拒绝共同 ABI 调用。三个 Map 谓词的完整字节事件是下列部分精化，其读取前提决定精化是否有定义，不增加外部调用实际成功的结论。

令 \(\mathcal L\) 为调用时给定的部分地址解释，其输入为 \(\mathrm{Term}_{32}\cup\mathrm{Term}_{64}\) 中的地址项，输出为唯一资源对象、起始字节偏移及该对象的规范单元布局；对象类别和单元标记使用[资源寄存器定义](../寄存器定义.md)。Map 布局还给出键、值字节长度，分别记作 \(L_k(t_m;\mathcal L)\)、\(L_v(t_m;\mathcal L)\)，其中 \(t_m\) 是唯一指向该 Map 对象的参数项。所需长度和字节读取均有定义时，完整事件的构造为：

\[
\operatorname{makeHelperPredicate}(\varepsilon,E_g,h,\vec t,\mathcal L,w):=
\begin{cases}
\operatorname{mapLookup}(\varepsilon,t_1,
\operatorname{readBytes}(E_g,t_2,L_k(t_1;\mathcal L),\mathcal L,w)),
&h=\mathrm{MAP\_LOOKUP},\\
\operatorname{mapUpdate}(\varepsilon,t_1,
\operatorname{readBytes}(E_g,t_2,L_k(t_1;\mathcal L),\mathcal L,w),
\operatorname{readBytes}(E_g,t_3,L_v(t_1;\mathcal L),\mathcal L,w),t_4),
&h=\mathrm{MAP\_UPDATE},\\
\operatorname{mapDelete}(\varepsilon,t_1,
\operatorname{readBytes}(E_g,t_2,L_k(t_1;\mathcal L),\mathcal L,w)),
&h=\mathrm{MAP\_DELETE},\\
\operatorname{helper}(\varepsilon,h,\vec t),&h\in H_{\mathrm{other}}.
\end{cases}
\]

\(\operatorname{makeHelperPredicate}\) 取值于 \(\mathrm{Helper}\)，\(\varepsilon\) 为调用身份，\(h,\vec t\) 已按共同取源确定；三个 \(\mathrm{MAP\_*}\) 标签分别为编号 1、2、3 的已命名类型。\(H_{\mathrm{other}}\) 见[OtherHelper 类型定义](OtherHelper谓词.md#类型定义)，包含未支持类型。\(\operatorname{readBytes}\) 见[调用时的字节读取](#调用时的字节读取)。

若上述完整事件构造成功得到 \(p\)，其局部观察集合为：

\[
P_i:=\{p\}.
\]

其中 \(p\in\mathrm{Helper}\) 为本次调用的完整事件，\(P_i\) 为该精化的谓词分量。ABI 观察与完整事件的表示对应须满足[实现对应中的义务](../NodeInference/路径合并FFI.md#五类观察的实现对应)。

### 生成的 Expr

共同取源成功后，由调用身份与 ABI 参数前缀构造同载体外部结果项：

\[
e_w:=\operatorname{externalResult}_{\varepsilon,0}^{w}
(C_w(\operatorname{id}(h)),t_1,\ldots,t_{n(h)}).
\]

其中 \(e_w\in\mathrm{Term}_w\)，\(\operatorname{externalResult}_{\varepsilon,0}^{w}\) 是以事件身份 \(\varepsilon\)、结果分量 0 标记的未解释外部运算；其所有参数与结果均为 \(w\) 位。编号常元保证参数数组非空。冻结字节尾不参与这个结果项，外部运算的解释补全见[解释参数](#解释参数)。

返回项按类型确定：

\[
t_{\mathrm{ret}}:=
\begin{cases}
C_w(2^w-1),&h=\operatorname{unsupported}(k),\\
Z_{16\to w}^{(w),\star}(e_w),&h=\mathrm{BPF\_FUNC\_CSUM\_DIFF},\\
e_w,&\text{otherwise}.
\end{cases}
\]

\(t_{\mathrm{ret}}\in\mathrm{Term}_w\) 为完整返回项；\(Z_{16\to w}^{(w),\star}\) 为[低位零扩展的符号提升](../Expr/Term/数值函数.md#截取与扩展)，保留低 16 位并将高 \(w-16\) 位清零。未支持编号生成 \(n=0\) 的 OtherHelper 调用观察，返回载体全一常元。

创建真实返回寄存器的完整等式：

\[
r_{\mathrm{ret}}=t_{\mathrm{ret}}.
\]

\(r_{\mathrm{ret}}\) 是该调用约定的真实返回标记。lookup 还创建虚拟 Map 的完整等式：

\[
\mathrm{Map}_{w}(\alpha_{\varepsilon,0})=R_{w}^{\varepsilon}(r_{\mathrm{ret}}).
\]

\(\alpha_{\varepsilon,0}\) 标识本次调用事件命名空间中、字节偏移 0 的首个 Map 单元，使用[Map 标记](../寄存器定义.md)；\(R_w^\varepsilon(r_{\mathrm{ret}})\) 为[调用返回时刻的真实寄存器变元](../Expr/Term/Term.md#叶子与运算符)。RV32 的单元为 4 字节，覆盖 \([0,4)\)，返回标记为 \(\mathrm{Real}_{32}(10)\)；原生 eBPF 的单元为 8 字节，覆盖 \([0,8)\)，返回标记为 \(\mathrm{Real}_{64}(0)\)。其他类型只创建真实返回等式；完整等式按[关系集合按键覆写](../Expr/Expr.md#关系集合按键覆写)写入 Expr 分量。

### 调用时的字节读取

给定同一调用前关系 \(E_g\)、缓冲区地址项 \(t_b\in\mathrm{Term}_{w}\)、所需字节数 \(n\in\mathbb N\)、资源布局与地址解析依据 \(\mathcal L\) 及载体宽度 \(w\in\{32,64\}\)，定义部分读取：

\[
\operatorname{readBytes}(E_g,t_b,n,\mathcal L,w)
:=(b_1,\ldots,b_n)\in\mathrm{BytesTerm}_w(n).
\]

其中 \(b_j\) 是从地址项 \(t_b\) 指向的缓冲区取得的第 \(j\) 个有限符号字节值项，按内存地址递增排列；对象与起始字节偏移由 \(\mathcal L\) 对该地址项的解析确定，所需范围由字节数 \(n\) 确定。规范单元、字段位置及字节序按该对象的布局与访问规则确定；源项取自 \(E_g\) 的当前完整等式，或按下列 Packet 输入契约取得。每个 \(b_j\) 依[字节项数组](#字节项数组)中的字节投影取得。

读取的定义域要求：

- 调用时地址项 \(t_b\) 指向唯一缓冲区对象，且 \(\mathcal L\) 确定所需 \(n\) 个字节的资源单元及字段。
- 读取满足所属资源的访问条件。
- Stack、Map、Context 的每个所需单元由 \(E_g\) 提供唯一、位宽匹配的完整等式；Context 另需显式入口绑定。这三类资源不补造字节项。
- Packet 的每个所需字节若在 \(E_g\) 中已有完整等式，须复用其当前、唯一且位宽匹配的完整等式；仅有比较关系时读取无定义，不得重新取入口输入。若该字节既无完整等式也无比较关系，则须有调用时包基绑定和所需字节范围的依据，才能按[未记录虚拟寄存器的取源](../Expr/Expr.md#未记录虚拟寄存器的取源)依输入契约引入 `low 8 (inputByte κ [base, base+o])` 项；该补充只适用于 Packet。
- 全部字节投影有定义。

保存的是调用时取得的有限符号项；完整 Map 事件的键和值均使用这个读取。后续覆写缓冲区不修改已保存的项。读取的对象或字段不能确定、源项或投影不足时，\(\operatorname{readBytes}\) 无定义。

### 错误类型

共同 ABI 调用构造在下列任一情形下无定义，不生成调用观察或返回效果，必须[拒绝本次处理](../NodeInference/step.md#无定义时的处理)：

- 指令形式不在[触发定义域](#触发逻辑)内，或必需的调用绑定、顺序后继缺失。
- \(E_g\) 的完整值键不唯一或关系位宽无效。
- 任一所需 \(a_j\) 的完整等式缺失、不唯一，或载体位宽不符。
- RV32 编号寄存器 \(a_0\) 的完整 32 位等式缺失、不唯一，或 \(D_{32}(\operatorname{solve}(u_0))\) 无定义。

完整 Map 事件的附加读取定义域见各子谓词的生成条件。

## 数学性质

OtherHelper 生成的唯一性与参数齐备见[命题 H1](OtherHelper谓词.md#数学性质)。

引理 M5 与命题 H2 的对象为调用产生的真实返回等式与 lookup 的虚拟 Map 等式。

**引理 M5（lookup 关联的结构有效性）。** 对固定调用约定的载体宽度 \(w\)，lookup 产生两个互异键的 \(w\) 位完整等式，其中一个写真实返回标记，另一个建立虚拟 Map 关联；之后覆写 \(r_{\mathrm{ret}}\) 不改变已经构造的真实寄存器变元身份。

**证明。** Real 与 Map 类别不交，因此两个键不同。返回项与真实寄存器变元均为 \(w\) 位，与左侧位宽匹配。变元身份固定了调用事件与寄存器标记，后续覆写不修改已有项。\(\square\)

**命题 H2（返回更新的有限性与位宽）。** 对共同取源成功的调用，生成的 Expr 集合含真实返回键，lookup 另含一个虚拟 Map 键；集合有限、位宽匹配且键唯一，覆写不改变其余 Expr 键。

**证明。** 结果项与真实寄存器变元均为所选约定的 \(w\) 位。lookup 的两个左侧分别属于 Real 与 Map，键互异；其他类型只有返回键。覆写结论由[按键覆写](../Expr/Expr.md#关系集合按键覆写)的定义得到。结论限于所选值更新的结构性质。\(\square\)

**命题 H3（动态调用区分）。** 同一种 Helper 构造的两个元素若调用身份 \(\varepsilon\ne\varepsilon'\)，则两谓词不同，在集合合并后均保留。

**证明。** 四个构造均将事件身份作为结构相等的一部分，两谓词不同；并集包含两者。\(\square\)

**命题 H4（保存的字节项保持）。** 已生成的 Map 谓词在后续缓冲区覆写后，其字节数组及在同一 \((\nu,\theta)\) 下的解释保持不变。

**证明。** \(\operatorname{readBytes}\) 的结果保存有限项。后续[按键覆写](../Expr/Expr.md#关系集合按键覆写)只改变当前 Expr 绑定，不修改既有项。数组各分量的结构不变，其逐项解释在固定赋值和补全下不变。\(\square\)

**证明义务 H-B（字节读取与布局可靠性）。** 须证明 Map 参数项指向的对象和调用时已知布局与实际调用对象一致。须证明 \(\operatorname{readBytes}\) 的源项、字节顺序及访问条件准确描述实际调用时的全部缓冲区字节。Packet 未记录字节的输入项物化须以调用时包基与包界限绑定、偏移范围成立、资源身份唯一及此前无写入改变该字节为前提。物化的 `inputByte` 项与真实输入字节的对应仍属 H-B 与 [CP-Bytes](跨架构谓词.md#待证明义务) 的未决义务；有限 `#guard` 或夹具检查不构成该对应的一般证明。跨规范单元和别名访问的一致性见[访问对象与单元一致性的义务](../Expr/Expr.md#来源与结构性质)。对象或字段不能确定时，读取保持无定义，不补造字节项。

### 跨架构调用观察

M6 的查询比较使用[CrossHelper](跨架构谓词.md#条件与各类观察)的 Map 项和完整冻结键列表。完整更新、删除的冻结数据按[观察规范化](跨架构谓词.md#观察规范化)进入统一 Map 变更。动态调用身份擦除由 `cross_helper_event` 证明；同程序的 H3 保持原判据。`externalResult` 返回项的 ABI 参数与冻结键具有不同来源，其 lookup-null 条件的测量边界见[跨架构判断范围](跨架构谓词.md#判断范围)。

2026-10-14 20:20 的 `/tmp/compare-just-tx.json` 中，节点 15 的 RV32IMC `loc:"45"` 与 eBPF `loc:"37"` 均为同一 Map 项 `1077412584` 的 lookup。RV32IMC 的冻结键是 `low8(inputByte0(v32:4,add32(v32:4,24)))` 上的四个字节切片树，切片分别为 `extract(0,8)`、`extract(8,8)`、`extract(16,8)`、`extract(24,8)`。eBPF 对应树在载体转换中多出 `or64(0,shl64(·,0))` 包裹；两侧已有的同类零拼接包裹也按零恒等剥除。剥除后，四个冻结键字节逐项结构相同。

该 lookup 实例的冻结键差异因此闭合；剩余对应涉及 ABI 指针前缀的擦除及 Map 项身份。键指针在 RV32IMC 侧为栈基项偏移 −16，在 eBPF 侧为偏移 −4。查询观察取 ABI 前缀后的冻结键，lane 0 返回项则依 [CP-ABI](跨架构谓词.md#待证明义务) 删除该指针尾部并保留 helper 编号与 Map 项；该有限实例的 Map 项规范结果相同，资源身份的可靠对应仍须生成侧依据。冻结字节的来源与值对应仍由 H-B 和 CP-Bytes 承担。

完整查询、更新和删除的冻结范围由[共同生成条件](#生成条件)确定。完整尾部进入规范观察时，更新、删除被分类为 `mapWrite`。该标签在 Helper 来源下表示尝试提交的变更参数，成功返回、flags 条件、Map 权限及真实资源变化仍分别需要 H-U、H-D 与 [CP-Bytes](跨架构谓词.md#待证明义务)；完整冻结与规范分类本身不能证明成功。读取不足而保留 ABI 前缀时仍分类为 `other`。

## 相关文档

- [生成的 Expr](#生成的-expr)
- [检查源项与访问对象](../NodeInference/step.md#检查源项与访问对象)
- [指令参数与规则定义域](../NodeInference/step.md#局部规则的合法域)
- [solve 的化简与求值](../Expr/Term/solve.md#solve-的化简与求值)
- [Term与项解释](../Expr/Term/Term.md#term)
