# MapWrite谓词

## 类型定义

MapWrite谓词记录一次向 Map 元素值内部写入的事件。其类型为：

\[
\mathrm{MapWrite}
:=\bigsqcup_{w,v\in\{32,64\}}\ \bigsqcup_{n\in\mathbb N}
\left\{\operatorname{mapWrite}(\varepsilon,t_m,\vec k,o,t):
\varepsilon\in\mathcal I_{\mathrm{write}},\
t_m\in\mathrm{Term}_w,\
\vec k\in\mathrm{BytesTerm}(n),\
o\in\mathbb N,\
t\in\mathrm{Term}_v\right\}.
\]

其中 \(\bigsqcup\) 保留 Map 项位宽 \(w\)、写入源项位宽 \(v\) 和完整键长度 \(n\)；\(\mathcal I_{\mathrm{write}}\) 是动态写入事件身份集合，身份没有机器位宽。\(t_m\) 是 Map 身份的符号项，\(\vec k\) 是完整元素键的符号字节数组，\(o\) 是元素值内部从零开始的起始字节偏移，\(t\) 是写入源值项。\(\mathrm{Term}_w\) 与 \(\mathrm{Term}_v\) 由 [Expr Term](../Expr/Term/Term.md#term)定义；\(\mathrm{BytesTerm}(n)\) 的字节取值集合 \(\mathbb B_8\)、数组顺序与解释由 [Helper 字节项数组](Helper谓词.md#字节项数组)定义。

\(t_m\) 与 \(\vec k\) 共同选择 Map 元素，\(o\) 再选择该元素值内部的写入起点。\(o\) 不参与元素键的字节编号。

同一类型中的两个 MapWrite谓词结构相等，当且仅当上述标签和五个构造分量分别结构相等。项的变元身份、运算符与参数均参与结构比较；键数组按其既定顺序逐项比较。

### 写入宽度与覆盖范围

写入位宽 \(q\in\{8,16,32,64\}\) 是生成接口的显式输入，要求 \(q\le v\)。源项位宽 \(v\) 与实际写入位宽 \(q\) 分别检查。写入字节序 \(e\in\{\mathrm{LE},\mathrm{BE}\}\) 也由生成接口显式接收。

\[
\operatorname{mapWriteRange}(o,q)
:=\{b\in\mathbb N:o\le b<o+q/8\}.
\]

其中 \(\operatorname{mapWriteRange}\) 把非负字节偏移 \(o\) 与上述写入位宽 \(q\) 映到有限字节偏移集合；\(b\) 是元素值内部的字节偏移，\(q/8\) 是此次写入的字节数。

### 写入事件的解释

令 \(p=\operatorname{mapWrite}(\varepsilon,t_m,\vec k,o,t)\)，其中 \(t\in\mathrm{Term}_v\)。解释显式接收写入位宽 \(q\)、字节序 \(e\)、变元赋值族 \(\nu\) 与未解释运算补全 \(\theta\)：

\[
\left[\!\left[p\right]\!\right]_{q,e,\nu,\theta}
:=\left(\mathsf{mapWrite},\varepsilon,
\left[\!\left[t_m\right]\!\right]_{\nu,\theta},
\left[\!\left[\vec k\right]\!\right]_{\nu,\theta},o,
\left(\widehat D_{q/8,j,e,v}
\left(\left[\!\left[t\right]\!\right]_{\nu,\theta}\right)\right)_{j=0}^{q/8-1}\right).
\]

其中 \(\mathsf{mapWrite}\) 是事件类别标签，\(\varepsilon\) 是写入事件身份，\(t_m\) 与 \(\vec k\) 分别解释为 Map 值标识与完整键字节数组，\(o\) 给出首个目标字节；\(\widehat D_{q/8,j,e,v}\) 是 [Expr 写入拆分](../Expr/寄存器/包字节.md#读取拼接与写入拆分)拥有的第 \(j\) 个字节提取函数，最后一个分量按目标地址递增顺序记录 \(q/8\) 个写入字节。\(\nu\) 与 \(\theta\) 的类型及项解释见 [Expr 项的解释](../Expr/Term/Term.md#项的解释)与[解释补全](../Expr/Term/Term.md#未解释运算的解释补全)。解释的定义域沿用上述 \(q,e,v\) 条件。

## 触发逻辑

只有地址源寄存器的项及指令偏移唯一确定写入目标为 Map 元素值，且满足[指令结果的前提](../Expr/Expr.md#指令结果的前提)的指令实例，才进入 MapWrite谓词生成。元素内部偏移由上述地址项与指令偏移确定，所涉及的规范单元由对象布局及访问宽度确定。Map 读取仍采用 [Expr Map 读取](../Expr/寄存器/虚拟映射.md#虚拟映射读写)；MapUpdate helper 的整元素调用观察由 [MapUpdate谓词](MapUpdate谓词.md)维护。

### RV32IMC

Map 来源已确定的 `SB`、`SH`、`SW` 分别以 \(q=8,16,32\) 触发写入生成。合法的 `C.SW`、`C.SWSP` 以 \(q=32\) 处理，目标类别仍由地址源寄存器的项及指令偏移确定。源值项取自该指令执行前的真实源寄存器，源项位宽为 32；固定零寄存器按 [Expr 固定值规则](../Expr/寄存器/真实寄存器.md#固定与只读目标)取源。

### eBPF

Map 来源已确定的普通 `ST`、`STX` 写入按指令大小字段取得 \(q=8,16,32,64\)。`ST` 按 [Expr 立即数规则](../Expr/寄存器/真实寄存器.md#常元赋值)取得 64 位源项；`STX` 读取执行前源寄存器的完整 64 位等式。`STORE_REL` 的数值写入部分按 [Expr 访问参数](../Expr/寄存器/单元字段读写.md#访问参数与源项)取得相同来源与位宽；其 release 语义的证明边界见[证明义务](#证明义务)。

原子访问的真实更新值与并发观察尚需对应契约，见[原子写入义务](#证明义务)。

## 生成条件

生成输入包括本次事件身份 \(\varepsilon\)、执行前 Expr 关系 \(E_g\)、已解码指令 \(i\)，以及显式的 \(q,e,B,n_k,n_v,t_m,\vec k,o,t\)。其中 \(B\in\mathscr F(\mathbb N)\) 是候选覆盖范围，\(\mathscr F\) 是有限子集族；\(n_k,n_v\in\mathbb N\) 分别是目标 Map 布局的完整键字节数与元素值字节数。其余输入的类型见[类型定义](#类型定义)。所有来源校验均使用当前指令写入前的 \(E_g\) 与指令操作数。

成功构造要求：

- \(E_g\) 有效，指令参数合法。
- 地址源寄存器的项与指令偏移唯一确定此次访问的 Map 对象、元素及内部偏移，候选 \(t_m,\vec k,o\) 与该访问对象和偏移一致。
- \(n_k,n_v\) 与该对象的布局一致，且 \(\vec k\in\mathrm{BytesTerm}(n_k)\)。
- \(q\) 与指令宽度字段给出的写入大小一致，\(e\) 与访问形式的字节序一致。
- \(t\) 是按[触发逻辑](#触发逻辑)从同一执行前关系取得的完整源项。
- \(B=\operatorname{mapWriteRange}(o,q)\)，且 \(o+q/8\le n_v\)。
- \(B\) 中各字节在 Map 值布局中的规范单元及字段唯一确定；跨单元访问具有既定的分段和组合规则。
- 访问规则所要求的有效性、权限与对齐条件成立。

源项可以含变元或未解释运算，无须在生成时取得具体数值。上述条件只限定部分构造的定义域；从机器访问证明这些条件的义务集中在[证明义务](#证明义务)。

\[
\operatorname{makeMapWritePredicate}
(\varepsilon,E_g,i,q,e,B,n_k,n_v,t_m,\vec k,o,t)
:=\operatorname{mapWrite}(\varepsilon,t_m,\vec k,o,t).
\]

其中 \(\operatorname{makeMapWritePredicate}\) 是上述定义域上的部分构造；\(\varepsilon,E_g,i\) 指定事件及取源语境，\(q,e,B,n_k,n_v\) 指定访问及布局检查输入，\(t_m,\vec k,o,t\) 是通过这些检查的五分量构造中的四个值分量。

\[
P_i:=\{\operatorname{mapWrite}(\varepsilon,t_m,\vec k,o,t)\}.
\]

其中 \(P_i\in\mathscr F(\mathrm{MapWrite})\) 是此次成功写入的局部观察增量，\(\varepsilon,t_m,\vec k,o,t\) 是成功构造保存的分量。该增量与 Map 值的局部 Expr 写入共同发生；混合观察累积与历史接入见[证明义务](#证明义务)。

### 来自 MapLookup 的值引用

写入所用 Map 值引用若来自先前的 MapLookup，地址源寄存器的项须依 [Expr lookup 返回关联](Helper谓词.md#生成的-expr)确定它的引用来源。\(t_m\) 使用该来源对应的 Map 参数项；\(\vec k\) 复用 [MapLookup 观察](MapLookup谓词.md)在查询时保存的完整符号键。写入时不重新读取查询使用的原始键指针所指向的当前字节。

产品 RV32IMC step 在 Meta `maps` 与栈上 `readStackBytes` 成功时，于 lookup 的 helper `args` 尾部保存冻结键，MapWrite 再按 lookup 事件身份取回该数组；这是实现侧的来源规则，不是 MW-O2 的证明。别名传播、空返回与失效引用的完备性仍列为 [MW-O2](#证明义务)，不能只凭 Map 编号、指针数值或返回寄存器变元判定该依赖已经满足。

### 错误类型

已识别为 Map 写入的步骤在下列任一情形下构造无定义，依照 [step 失败处理](../NodeInference/step.md#失败情形)拒绝整个步骤；不生成当前步骤的成功观察或部分写入效果：

- 执行前 Expr 无效，或所需完整源值缺失、不唯一、位宽不符。
- 地址源寄存器的项与指令偏移不能唯一确定 Map 对象、元素或偏移；空 lookup 返回也不提供有效值引用。
- 来自 lookup 的引用来源不能确定，或该来源保存的完整键无法取得。
- 候选键长度与布局不符，或字节项不满足共享字节类型。
- 候选宽度、字节序、覆盖范围或布局大小与指令宽度字段、访问形式或对象布局不符。
- 覆盖越过元素值边界，或跨单元分段和组合规则缺失。
- 所需访问有效性、权限或对齐条件不能成立。

目标已确定为其他资源的指令由所属规则处理，不进入本构造。

## 数学性质

### 构造与覆盖范围

**命题 MW1（构造唯一性）。** 固定全部生成输入，且输入属于上述定义域时，生成的 MapWrite谓词唯一，局部观察增量为单元素有限集合。

**证明。** 部分构造直接保存输入的五个分量，未在构造内部选择其他项或事件身份。其结果确定，所定义的增量只有该元素。\(\square\)

**命题 MW2（范围由宽度确定）。** 对 \(o\in\mathbb N\) 与 \(q\in\{8,16,32,64\}\)，覆盖范围包含恰好 \(q/8\) 个连续字节偏移。在生成条件的布局界限下，这些偏移均位于元素值内部。

**证明。** 范围由从 \(o\) 到 \(o+q/8-1\) 的整数组成；\(q/8\) 是正整数。布局界限保证每个成员小于 \(n_v\)，非负性由 \(o\in\mathbb N\) 保证。\(\square\)

**命题 MW3（动态写入区分）。** 两个 MapWrite谓词的事件身份不同，则其结构不同。

**证明。** 事件身份是构造分量之一，结构相等要求该分量相同。\(\square\)

### Expr 覆写与固定观察

[Expr 按键覆写](../Expr/Expr.md#赋值覆盖全部旧关系)中的键是 Expr 左值。写入一个 Map 值规范单元时，该单元左值的旧完整值关系与旧比较关系被删除，再写入新关系。若实际覆盖的是保存查询键字节的缓冲区单元，同样删除被写左值的旧关系；这与已经保存在 MapWrite 中的元素键数组是不同对象。

**命题 MW4（固定观察不受 Expr 按键删除）。** 给定已经构造的 MapWrite谓词 \(p\)，对 Expr 分量施行其既定按键覆写，不会对 \(p\) 执行删除，也不会改变它的构造分量。在固定 \(q,e,\nu,\theta\) 下，\(p\) 的解释保持不变。

**证明。** Expr 更新的输入与输出仅为 Expr 分量；过滤条件针对其关系的左值，MapWrite 不在该函数的定义域内。\(p\) 保存固定的项与键数组，不读取后来改变的真实寄存器或键缓冲区。其解释仅使用保存的分量及给定的 \(q,e,\nu,\theta\)，故结果不变。\(\square\)

这个结论限于 Expr 更新对固定对象的作用。MapWrite 在全状态中按[结构并集](谓词定义.md#结构并集)保留；其与真实写入及历史的对应仍需满足下列义务。

### 证明义务

- **MW-O1（宽度、字节序与事件身份）。** 五分量构造自身无法表达写入宽度与字节序。须证明每个动态写入身份 \(\varepsilon\) 唯一关联其固有属性 \((q,e)\)，并使生成校验、解释与历史读取采用同一关联。同一 Term32 源项用于 `SB` 与 `SW` 时，覆盖范围分别由各自的宽度确定。若该关联无法证明，则构造需增分量，由操作者裁定。
- **MW-O2（lookup 冻结键与引用来源）。** 依照 [Expr lookup 返回关联](Helper谓词.md#生成的-expr)与[指令结果的前提](../Expr/Expr.md#指令结果的前提)，证明地址源寄存器的值引用到 [MapLookup](MapLookup谓词.md)所保存 \(t_m,\vec k\) 的来源规则。实现已在具备 Meta 布局时把栈上读出的冻结键附在 lookup 观察上并由 MapWrite 复用，但仍须证明别名传播、指针偏移和原始键缓冲区覆写均保持所引用的查询键，并证明空返回与失效引用被拒绝。
- **MW-O3（机器写入与布局兼容）。** 证明各架构触发指令取得的 \(t_m,\vec k,o,t,q,e,B,n_k,n_v\) 符合生成定义域，且字节拆分与实际写入一致。须覆盖权限、对齐、有效范围、规范单元分段、重叠访问与别名一致性；仅有范围界限不能证明这些性质。
- **MW-O4（Expr 删除与键关系的含义）。** 已有覆写规则只按实际写入的 Expr 左值删除关系。若“删除一个 key 关系”意指另一种按 Map 元素键删除关联的操作，须先在 [Expr](../Expr/Expr.md#关系集合按键覆写)确定其关系类型、删除条件与作用范围，再证明该操作保留已经固定的 MapWrite 观察；现有按左值覆写不推出这种额外删除。
- **MW-O5（观察累积与历史对应）。** 按[统一谓词域与混合累积](谓词定义.md#观察集合累积与可满足性)及 [History 状态组合](../NodeInference/History.md#状态组合的定义域)保存 MapWrite 增量，证明具体记录与成功写入的 Expr 和观察对应。证明历史保留所需事件顺序及 MW-O1 的属性。还须按 [History 完整依赖提取](../NodeInference/History.md#完整依赖提取)处理 Map 身份、冻结键与值项的依赖。
- **MW-O6（原子写入与 release）。** 对原子访问，先由 [Expr 原子数值规则](../Expr/寄存器/原子数值更新与旧值返回.md#原子数值更新与旧值返回)确定真正写入的新值，再证明其与 MapWrite 的事件、范围和字节解释相符。并发交错、原子性与 `STORE_REL` 的内存顺序仍需独立语义；普通写入字节解释不证明这些性质。

## 相关文档

- [Helper 字节项数组](Helper谓词.md#字节项数组)与[MapLookup](MapLookup谓词.md)：共享冻结字节类型及查询观察。
- [Expr Map 读写](../Expr/寄存器/虚拟映射.md#虚拟映射读写)：架构内部的 Map 值关系。
- [Expr lookup 返回关联](Helper谓词.md#生成的-expr)：值引用与资源来源的接入依据。
- [Expr 单元字段读写](../Expr/寄存器/单元字段读写.md#单元字段读写)：Map 值内部字段的数值更新。
- [寄存器定义](../寄存器定义.md)：Map 对象、条目与规范单元的身份。
- [统一谓词类型](谓词定义.md#类型与结构相等)：类别标签与结构比较。
- [History](../NodeInference/History.md#完整依赖提取)：逐步写入记录与依赖对应义务。
