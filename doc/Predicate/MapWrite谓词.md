# MapWrite谓词

## 类型定义

MapWrite谓词记录一次向 Map 元素值内部写入的事件。其类型为：

\[
\mathrm{MapWrite}
:=\bigsqcup_{w,v\in\{32,64\}}\ \bigsqcup_{n\in\mathbb N}
\left\{\operatorname{mapWrite}(\varepsilon,t_m,\vec k,o,q,t):
\varepsilon\in\mathcal I_{\mathrm{write}},\
t_m\in\mathrm{Term}_w,\
\vec k\in\mathrm{BytesTerm}(n),\
o\in\mathbb N,\
q\in\{8,16,32,64\},\ q\le v,\ t\in\mathrm{Term}_v\right\}.
\]

其中 \(\bigsqcup\) 保留 Map 项位宽 \(w\)、写入源项位宽 \(v\) 和完整键长度 \(n\)；\(\mathcal I_{\mathrm{write}}\) 是动态写入事件身份集合，身份没有机器位宽。\(t_m\) 是 Map 身份的符号项，\(\vec k\) 是完整元素键的符号字节数组，\(o\) 是元素值内部从零开始的起始字节偏移，\(q\) 是保存的访问位宽，\(t\) 是写入源值项。\(\mathrm{Term}_w\) 与 \(\mathrm{Term}_v\) 由 [Expr Term](../Expr/Term/Term.md#term)定义；\(\mathrm{BytesTerm}(n)\) 的字节取值集合 \(\mathbb B_8\)、数组顺序与解释由 [Helper 字节项数组](Helper谓词.md#字节项数组)定义。

\(t_m\) 与 \(\vec k\) 共同选择 Map 元素，\(o\) 再选择该元素值内部的写入起点。\(o\) 不参与元素键的字节编号。

同一类型中的两个 MapWrite谓词结构相等，当且仅当上述标签和六个构造分量分别结构相等。项的变元身份、运算符与参数均参与结构比较；键数组按其既定顺序逐项比较。

### 写入宽度与覆盖范围

写入位宽 \(q\in\{8,16,32,64\}\) 是生成接口的显式输入及保存的构造分量，要求 \(q\le v\)。源项位宽 \(v\) 与实际写入位宽 \(q\) 分别检查。RV32IMC 与 eBPF XDP 的写入字节序按定义固定为 \(e=\mathrm{LE}\)。

\[
\operatorname{mapWriteRange}(o,q)
:=\{b\in\mathbb N:o\le b<o+q/8\}.
\]

其中 \(\operatorname{mapWriteRange}\) 把非负字节偏移 \(o\) 与上述写入位宽 \(q\) 映到有限字节偏移集合；\(b\) 是元素值内部的字节偏移，\(q/8\) 是此次写入的字节数。

原生 eBPF 普通 `ST DW`、`STX DW`、`STORE_REL DW` 写入 Map 单元时，机器访问位宽为 64，生成器将其分为两次 \(q=32\) 的构造调用。令 \(t\in\mathrm{Term}_{64}\) 为同次执行前完整寄存器源项或合法立即数项，低半源项为

\[
t_{\mathrm{lo}}:=\operatorname{star}_{32}(\operatorname{extract}(0,32,64),[t]).
\]

高半源项为

\[
t_{\mathrm{hi}}:=\operatorname{star}_{32}(\operatorname{extract}(32,32,64),[t]).
\]

其中 \(\operatorname{star}_{32}\) 是结果载体为 32 位的[符号提升](../Expr/Term/solve.md#化简规则)，`extract` 的三个参数依次为起始位偏移、截取长度与输入载体位宽；两式对应 Lean 的 `star .w32 (.extract 0 32 64) [t]` 与 `star .w32 (.extract 32 32 64) [t]`。两个源项均属于 \(\mathrm{Term}_{32}\)，故每次调用的 \(v=32\)。生成顺序为低半在元素偏移 \(o\)，高半在 \(o+4\)；两次调用共用同一 \(\varepsilon,t_m,\vec k\) 及小端字节序，偏移以完整 8 字节访问解析得到的 \(o\) 为基准。Map 值的 Expr 效果仍以 \(t\) 覆写整个 64 位规范单元。\(q\in\{8,16,32\}\) 的 Map 写入保持一次构造调用，其源项仍为完整 64 位源项。

### 写入事件的解释

令 \(p=\operatorname{mapWrite}(\varepsilon,t_m,\vec k,o,q,t)\)，其中 \(t\in\mathrm{Term}_v\)。解释读取保存的访问位宽 \(q\)，字节序使用上述固定小端约定；外部参数为变元赋值族 \(\nu\) 与未解释运算补全 \(\theta\)：

\[
\left[\!\left[p\right]\!\right]_{\nu,\theta}
:=\left(\mathsf{mapWrite},\varepsilon,
\left[\!\left[t_m\right]\!\right]_{\nu,\theta},
\left[\!\left[\vec k\right]\!\right]_{\nu,\theta},o,
\left(\widehat D_{q/8,j,\mathrm{LE},v}
\left(\left[\!\left[t\right]\!\right]_{\nu,\theta}\right)\right)_{j=0}^{q/8-1}\right).
\]

其中 \(\mathsf{mapWrite}\) 是事件类别标签，\(\varepsilon\) 是写入事件身份，\(t_m\) 与 \(\vec k\) 分别解释为 Map 值标识与完整键字节数组，\(o\) 给出首个目标字节；\(\widehat D_{q/8,j,\mathrm{LE},v}\) 是 [Expr 写入拆分](../Expr/寄存器/包字节.md#读取拼接与写入拆分)拥有的第 \(j\) 个小端字节提取函数，最后一个分量按目标地址递增顺序记录 \(q/8\) 个写入字节。\(\nu\) 与 \(\theta\) 的类型及项解释见 [Expr 项的解释](../Expr/Term/Term.md#项的解释)与[解释补全](../Expr/Term/Term.md#未解释运算的解释补全)。解释的定义域沿用上述 \(q,v\) 条件。

## 触发逻辑

只有地址源寄存器的项及指令偏移唯一确定写入目标为 Map 元素值，且满足[指令结果的前提](../Expr/Expr.md#指令结果的前提)的指令实例，才进入 MapWrite谓词生成。元素内部偏移由上述地址项与指令偏移确定，所涉及的规范单元由对象布局及访问宽度确定。Map 读取仍采用 [Expr Map 读取](../Expr/寄存器/虚拟映射.md#虚拟映射读写)；MapUpdate helper 的整元素调用观察由 [MapUpdate谓词](MapUpdate谓词.md)维护。

### RV32IMC

Map 来源已确定的 `SB`、`SH`、`SW` 分别以 \(q=8,16,32\) 触发写入生成。合法的 `C.SW`、`C.SWSP` 以 \(q=32\) 处理，目标类别仍由地址源寄存器的项及指令偏移确定。源值项取自该指令执行前的真实源寄存器，源项位宽为 32；固定零寄存器按 [Expr 固定值规则](../Expr/寄存器/真实寄存器.md#固定与只读目标)取源。

### eBPF

Map 来源已确定的普通 `ST`、`STX` 写入按指令大小字段取得机器访问位宽 \(8,16,32,64\)。`ST` 按 [Expr 立即数规则](../Expr/寄存器/真实寄存器.md#常元赋值)取得 64 位源项；`STX` 读取执行前源寄存器的完整 64 位等式，其中 `STX DW` 的两次生成调用及较窄写入的一次调用依[写入宽度与覆盖范围](#写入宽度与覆盖范围)确定。`STORE_REL` 的数值写入部分按 [Expr 访问参数](../Expr/寄存器/单元字段读写.md#访问参数与源项)取得相同来源与位宽；其 release 语义的证明边界见[证明义务](#证明义务)。

原子访问的真实更新值与并发观察尚需对应契约，见[原子写入义务](#证明义务)。

## 生成条件

生成输入包括本次事件身份 \(\varepsilon\)、执行前 Expr 关系 \(E_g\)、已解码指令 \(i\)，以及显式的 \(q,B,n_k,n_v,t_m,\vec k,o,t\)。其中 \(B\in\mathscr F(\mathbb N)\) 是候选覆盖范围，\(\mathscr F\) 是有限子集族；\(n_k,n_v\in\mathbb N\) 分别是目标 Map 布局的完整键字节数与元素值字节数。其余输入的类型见[类型定义](#类型定义)。所有来源校验均使用当前指令写入前的 \(E_g\) 与指令操作数。

成功构造要求：

- \(E_g\) 有效，指令参数合法。
- 地址源寄存器的项与指令偏移唯一确定此次访问的 Map 对象、元素及内部偏移，候选 \(t_m,\vec k,o\) 与该访问对象及[生成分解规则](#写入宽度与覆盖范围)确定的本次观察偏移一致。
- \(n_k,n_v\) 与该对象的布局一致，且 \(\vec k\in\mathrm{BytesTerm}(n_k)\)。
- \(q\) 与指令宽度字段及[生成分解规则](#写入宽度与覆盖范围)确定的本次观察宽度一致，访问采用固定小端字节序。
- \(t\) 是按[触发逻辑](#触发逻辑)从同一执行前关系取得的本次观察源项；分解调用使用完整源项的对应 32 位半部。
- \(B=\operatorname{mapWriteRange}(o,q)\)，且 \(o+q/8\le n_v\)。
- \(B\) 中各字节在 Map 值布局中的规范单元及字段唯一确定；跨单元访问具有既定的分段和组合规则。
- 访问规则所要求的有效性、权限与对齐条件成立。

源项可以含变元或未解释运算，无须在生成时取得具体数值。上述条件只限定部分构造的定义域；从机器访问证明这些条件的义务集中在[证明义务](#证明义务)。

\[
\operatorname{makeMapWritePredicate}
(\varepsilon,E_g,i,q,B,n_k,n_v,t_m,\vec k,o,t)
:=\operatorname{mapWrite}(\varepsilon,t_m,\vec k,o,q,t).
\]

其中 \(\operatorname{makeMapWritePredicate}\) 是上述定义域上的部分构造；\(\varepsilon,E_g,i\) 指定事件及取源语境，\(q,B,n_k,n_v\) 指定访问及布局检查输入，结果保存 \(\varepsilon,t_m,\vec k,o,q,t\) 六个构造分量。

\[
P_i:=\{\operatorname{makeMapWritePredicate}(c):c\in C_i\}.
\]

其中 \(C_i\) 是依[触发逻辑](#触发逻辑)确定的本次机器写入的有序生成输入列表，每个成员 \(c\) 是上述部分构造的完整参数元组；\(P_i\in\mathscr F(\mathrm{MapWrite})\) 为各次成功构造结果的局部观察增量。原生 `STX DW` 的列表先含低半调用，再含高半调用，其余已规定的普通写入含一次调用。该增量与 Map 值的局部 Expr 写入共同发生；混合观察累积与历史接入见[证明义务](#证明义务)。

### 来自 MapLookup 的值引用

写入所用 Map 值引用若来自先前的 MapLookup，地址源寄存器的项须依 [Expr lookup 返回关联](Helper谓词.md#生成的-expr)确定它的引用来源。\(t_m\) 使用该来源对应的 Map 参数项；\(\vec k\) 复用 [MapLookup 观察](MapLookup谓词.md)在查询时保存的完整符号键。写入时不重新读取查询使用的原始键指针所指向的当前字节。

两侧 lookup 的完整符号键均按[调用时的字节读取](Helper谓词.md#调用时的字节读取)冻结：Packet 键缓冲区可保存由 `inputByte` 物化的字节；Stack、Map、Context 键缓冲区仍须已有完整等式。产品 RV32IMC step 在 Meta `maps` 布局确定且完整缓冲区读取成功时，于 lookup 的 helper `args` 尾部直接保存 Term32 冻结键，MapWrite 再按 lookup 事件身份取回该数组。原生 eBPF 的 lookup 尾部保持 Term64；MapWrite 复用同次 lookup 冻结的键值，以规格规定的 Term32 键字节承载。闭字节折叠为 `C32 (c % 256)`；符号字节从冻结的 64 位零扩展项中取回原有的 32 位八位提取项，其余开放字节取保存项的低八位。结构定理由 [CP-Bytes](跨架构谓词.md#cp-bytes-写入字节与冻结尾部)维护。栈地址项保留复制产生的恒等包裹时，按[根与常数偏移的识别](../Expr/Term/solve.md#设计目标)该包裹不改变识别所得的根与常数偏移，冻结仍取到同一栈单元。地址原像上的事件与保存列表的联系由 [MW-O2](#证明义务)闭合。

### 错误类型

已识别为 Map 写入的步骤在下列任一情形下构造无定义，依照 [step 失败处理](../NodeInference/step.md#失败情形)拒绝整个步骤；不生成当前步骤的成功观察或部分写入效果：

- 执行前 Expr 无效，或所需完整源值缺失、不唯一、位宽不符。
- 地址源寄存器的项与指令偏移不能唯一确定 Map 对象、元素或偏移；空 lookup 返回也不提供有效值引用。
- 来自 lookup 的引用来源不能确定，或该来源保存的完整键无法取得。
- 候选键长度与布局不符，或字节项不满足共享字节类型。
- 候选宽度、覆盖范围或布局大小与指令宽度字段、生成分解规则或对象布局不符，或访问形式与固定小端约定不符。
- 覆盖越过元素值边界，或跨单元分段和组合规则缺失。
- 所需访问有效性、权限或对齐条件不能成立。

目标已确定为其他资源的指令由所属规则处理，不进入本构造。

## 数学性质

### 构造与覆盖范围

**命题 MW1（构造唯一性）。** 固定一次构造调用的全部生成输入，且输入属于上述定义域时，生成的 MapWrite谓词唯一，该次调用贡献单元素有限集合。

**证明。** 部分构造直接保存输入的六个分量，未在构造内部选择其他项或事件身份。其结果确定，每次调用贡献的集合只有该元素；机器写入的增量按各次调用结果汇集。\(\square\)

**命题 MW2（范围由宽度确定）。** 对 \(o\in\mathbb N\) 与 \(q\in\{8,16,32,64\}\)，覆盖范围包含恰好 \(q/8\) 个连续字节偏移。在生成条件的布局界限下，这些偏移均位于元素值内部。

**证明。** 范围由从 \(o\) 到 \(o+q/8-1\) 的整数组成；\(q/8\) 是正整数。布局界限保证每个成员小于 \(n_v\)，非负性由 \(o\in\mathbb N\) 保证。\(\square\)

**命题 MW3（动态写入区分）。** 两个 MapWrite谓词的事件身份不同，则其结构不同。

**证明。** 事件身份是构造分量之一，结构相等要求该分量相同。\(\square\)

### Expr 覆写与固定观察

[Expr 按键覆写](../Expr/Expr.md#赋值覆盖全部旧关系)中的键是 Expr 左值。写入一个 Map 值规范单元时，该单元左值的旧完整值关系与旧比较关系被删除，再写入新关系。若实际覆盖的是保存查询键字节的缓冲区单元，同样删除被写左值的旧关系；这与已经保存在 MapWrite 中的元素键数组是不同对象。

**命题 MW4（固定观察不受 Expr 按键删除）。** 给定已经构造的 MapWrite谓词 \(p\)，对 Expr 分量施行其既定按键覆写，不会对 \(p\) 执行删除，也不会改变它的构造分量。在固定 \(\nu,\theta\) 下，\(p\) 的解释保持不变。

**证明。** Expr 更新的输入与输出仅为 Expr 分量；过滤条件针对其关系的左值，MapWrite 不在该函数的定义域内。\(p\) 保存固定的项、键数组及访问位宽，不读取后来改变的真实寄存器或键缓冲区。其解释仅使用保存的分量、固定小端约定及给定的 \(\nu,\theta\)，故结果不变。\(\square\)

这个结论限于 Expr 更新对固定对象的作用。MapWrite 在全状态中按[结构并集](谓词定义.md#结构并集)保留；其与真实写入及历史的对应仍需满足下列义务。

### 跨架构变更观察与生成缺口

M6 的直接写入与完整 Helper 更新、删除使用[统一 CrossMutation](跨架构谓词.md#条件与各类观察)。写入字节按[观察规范化](跨架构谓词.md#观察规范化)从冻结源项和保存的访问位宽取得，字节序固定为小端。谓词提供宽度时，比较结果与环境备用宽度无关；定理见 [CP-Bytes](跨架构谓词.md#cp-bytes-写入字节与冻结尾部)。

两侧 lookup 的冻结键可含 Packet 键缓冲区中由 `inputByte` 物化的字节，这是[调用时的字节读取](Helper谓词.md#调用时的字节读取)的一般取源情形。MapWrite 复用保存列表的事件来源由 [MW-O2](#证明义务)闭合，冻结字节的结构性质由 [CP-Bytes](跨架构谓词.md#cp-bytes-写入字节与冻结尾部)闭合。

原生 eBPF `just_tx` 在非空 lookup 后继执行 Map 元素写入：原始槽 38 的双字读取取得 `r0` 指向元素的值，槽 39 对 `r1` 加一，槽 40 的 `STX DW` 将该值写回元素。未确定的 lookup-null 条件保留两侧，产品 Meta 提供 Map 布局；完整前沿的有限检查要求同一节点保存 Map 项为 `1077412584`、同一写入事件与非空冻结键的两条 MapWrite，偏移分别为 0、4，源项载体均为 32 位，且两条观察各自良构并通过 wire 结构回读。

工程对应：[程序槽数据](../../EBPF/JustTxProgram.lean)、[Step 的取源与调用](../../EBPF/Step.lean)、[Expand 的产品 Meta 与完整前沿检查](../../EBPF/Expand.lean)以及[Memory 的写入分派](../../EBPF/Memory.lean)。`resolveAccess` 将该元素解析为 Map 双字单元，`exprEffects` 的 `.cells` 分支在 Map 单元写入成功时，按地址引用的 lookup 事件身份从执行前谓词取回完整冻结键值，转换为 Term32 键字节。槽 40 的 DW 写入依[生成分解规则](#写入宽度与覆盖范围)提交低半、高半两条 MapWrite，两条均保存 32 位访问宽度并复用同一冻结键，Expr 更新仍写入完整源项；1、2、4 字节写入保持一条观察。布局须匹配，冻结键须非空且长度等于 `keySize`，访问须满足非负偏移、元素值范围及不跨 8 字节单元；缺少生成前提或可用的键字节转换时拒绝 `UndefinedSrc`。保存列表的事件来源定理见 [MW-O2](#证明义务)；规范化处理已生成的观察，字节结构定理见 [CP-Bytes](跨架构谓词.md#cp-bytes-写入字节与冻结尾部)。

2026-10-14 20:20 的历史快照 `/tmp/compare-just-tx.json` 中，两侧冻结键在常元键实例上均为四个零字节；符号键实例则复用同一 Map 项 `1077412584` 与同一组 `extract(0,8)`、`extract(8,8)`、`extract(16,8)`、`extract(24,8)` 切片。符号字节的来源为 `low8(inputByte0(v32:4,add32(v32:4,24)))`；对其拼接与载体转换中的 `or(0,shl(·,0))` 作零恒等剥除后，两侧四个冻结键字节结构相同。一般的保存列表来源由 [MW-O2](#证明义务)给出。

值项中的寄存器名仍有 RV32IMC `real32:10` 与 eBPF `real64:0` 的静态 alpha 差异。该名称对应由跨架构合一替换 `CrossSubst.regs` 处理，不由项规范化擦除；合法重命名与机器值对应仍须具备生成侧依据。

15 个 MapWrite 节点的值项现由[项规范化 R5、R6](跨架构谓词.md#项规范化)闭合规范键。RV32IMC 将 8 字节元素的更新分为偏移 0、4 的两条 32 位观察；eBPF 对一个 64 位值加一，再截取两半。低半覆盖共同 32 位表示的切片由 R5 剥除，高半包含两字来源的进位项由 R6 逐观察规范化。节点 26、34 的现场线对象各有分支及两条写入，有限检查确认两半在 Real 10→0 重命名后 JSON 相等，并经 host 所用合一入口取得唯一完整三对匹配。

上述规范键相等以 R5 的共同 32 位所表示值前提及 R6 的同元素双字来源、机器进位为条件；精确定义与解释定理由 [CP-Q](跨架构谓词.md#cp-q-已实现规则的解释保持)维护。每条观察保存四字节访问宽度，拆分定义与宽度定理由 [CP-Bytes](跨架构谓词.md#cp-bytes-写入字节与冻结尾部)闭合。R5 保留表示宽度小于 32 的冻结键字节切片，R6 的非单射规范键仍使用其来源前提；15 个节点的 host 通过数待重测。

### 证明义务

- **MW-O1（保存宽度与事件生成对应）。** 访问位宽 \(q\) 是保存的构造分量，字节序由固定小端定义给出。须证明真实指令与生成器保存的 \(q\)、偏移和动态身份 \(\varepsilon\) 对应。原生 `STX DW` 的[生成分解](#写入宽度与覆盖范围)使一个机器写入的两半共用 \(\varepsilon\)，每条观察保存 \(q=32\)；机器访问宽度 64 与该有序分解的对应仍需生成侧证明。规范化取得保存宽度和相应字节数的结论由 [CP-Bytes](跨架构谓词.md#cp-bytes-写入字节与冻结尾部)闭合。
- **MW-O2（lookup 冻结键与引用来源，已闭合）。** [RV32IMC/Expr.lean](../../RV32IMC/Expr.lean) 的 `lookupAddress_const`、`lookupAddress_ne_zero` 与 [EBPF/Memory.lean](../../EBPF/Memory.lean) 的 `lookupAddress64_const`、`lookupAddress64_ne_zero` 证明任意常元地址均不能解析为 Map 访问地址，解析成功的源项不等于常元 0。[RV32IMC/Expand.lean](../../RV32IMC/Expand.lean) 的 `mapWriteObservation_frozen` 结合 `mapElementAccess_preimage` 证明生成成功时，地址原像的 lookup 事件在 \(P_g\) 中具有保存同一 Map 项及返回键列表的 lookup 观察。[EBPF/Memory.lean](../../EBPF/Memory.lean) 的同名定理证明该事件的 lookup 保存原始尾列表，返回键恰为该列表经 `mapWriteKeyByte` 的逐项像；每项的低八位结构沿用 [CP-Bytes](跨架构谓词.md#cp-bytes-写入字节与冻结尾部)。[ClassifierExpr/Insn.lean](../../ClassifierExpr/Insn.lean) 的 `lookupKeyAt_tie`、`lookupKeyAt_deterministic`、`lookupKeyAt_expr_update` 和 eBPF 的 `mapWriteKeyAt_deterministic`、`mapWriteKeyAt_expr_update` 证明键只由观察列表与该事件决定，后续 Expr 更新及缓冲区覆写保持该键；`mapWrite_saved_key`、`savedMapKey_expr_update` 证明已构造的观察保留保存列表。别名和指针偏移通过地址原像事件使用同一保存列表，其见证见 [CP-Reg](跨架构谓词.md#cp-reg-查询事件与元素槽)。生成条件保持原有规则，不另要求 lookup-null 分支检查，`just_tx` 写入继续适用。
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
