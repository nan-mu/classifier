# History

## 逐步记录与统一类型

历史是一条路径各步的记录。固定指令序列 \(\mathbf I\) 及其语义语境，使用 [step 的语义状态](step.md#语义状态) \(\mathrm{State}\) 和[路径的位置与方向](路径.md)。普通位置 \(j\) 从 1 开始，其指令为 \(\mathbf I[j-1]\)；\(\mathrm{Exit}\) 是独立的正常结束标记。

\[
\mathrm{Record}_{\mathbf I}
:=\mathrm{Pos}_{\mathbf I}\times\mathrm{Direction}\times\mathrm{Loc}_{\mathbf I}
\times\bigl(\mathscr F(\mathrm{Expression})\times\mathscr F(\mathrm{Observation}_{\mathbf I})\bigr)^\ast.
\]

其中 \(\mathrm{Record}_{\mathbf I}\) 为单步记录类型，\(\mathrm{Pos}_{\mathbf I}\) 为普通指令位置域，\(\mathrm{Direction}\) 为方向域，\(\mathrm{Loc}_{\mathbf I}\) 还含 Exit；\(\mathscr F(X)\) 表示 \(X\) 的有限子集集合，\(X^\ast\) 表示 \(X\) 的有限有序序列，Expression 分量的内部有效性由 [Expression](../Expr/Expr.md#索引)维护。\(\mathrm{Observation}_{\mathbf I}\) 为固定指令序列的[五类观察域](../Predicate/谓词定义.md#类型与结构相等)：Helper 记录外部调用观察，Branch 记录选定方向及其条件，Return 记录最外层正常返回结果，MapWrite 记录 Map 元素内写入，PacketWrite 记录包写入；各类解释入口由同一[观察定义](../Predicate/谓词定义.md#类型与结构相等)维护。

\[
\delta_k=(j_k,d_k,j'_k,\Lambda_k).
\]

其中 \(\delta_k\in\mathrm{Record}_{\mathbf I}\) 是第 \(k\) 步，\(j_k\) 为执行位置，\(d_k\) 为已选方向，\(j'_k\) 为记录的后继位置，\(\Lambda_k\) 为该步已准备出的局部结果序列。

\(\Lambda_k\) 的每个元素为局部结果对 \((\bar{E}_i,\mathcal{O}_i)\)，两个分量的类型分别为 \(\mathscr F(\mathrm{Expression})\) 与 \(\mathscr F(\mathrm{Observation}_{\mathbf I})\)。它们由该步的局部结果保留，右侧项已经取得，局部观察按 Helper、Branch、Return、MapWrite 或 PacketWrite 的所属规则构造。一般指令记录一个效果对。需要补充未记录虚拟寄存器的当前值关系时，依 [step 的后继准备顺序](step.md#准备全部后继状态)先保留输入补充效果，再保留指令效果；多目标更新仍保留为一个整体效果。空序列表示该步没有状态变换。五类效果的记录仍须满足[状态组合的定义域](#状态组合的定义域)。

结构位置与方向说明效果来自哪一步。它们不参与 Expression 覆写或观察累积。记录的相等逐项比较位置、方向、后继位置与局部结果序列；效果对内部沿用各分量的结构相等，五类观察的类别标签和构造分量按[观察结构相等](../Predicate/谓词定义.md#类型与结构相等)比较。

\[
\Delta=(\delta_1,\ldots,\delta_n)\in\mathrm{Record}_{\mathbf I}^{\ast}.
\]

其中 \(\Delta\) 为一条路径的有限逐步记录，\(n=|\Delta|\in\mathbb N\) 为步数；\(n=0\) 时序列为空，同位置的不同次执行仍占据不同的序列项。

给定入口状态 \(\sigma_0\in\mathrm{State}\)，\(\mathrm{WF}_{\mathbf I}(\sigma_0,\Delta)\) 表示下列结构良构条件：

- 入口状态 \(\sigma_0\) 有效：值绑定键唯一、关系位宽正确，观察属于固定 \(\mathbf I\) 的 \(\mathrm{Observation}_{\mathbf I}\)。
- 每步属于上述单步记录类型；相邻记录满足 \(j'_k=j_{k+1}\)，其中 \(1\le k<n\)。因此 Exit 只能作为最后一步的后继位置。
- 每个局部结果有限、位宽正确，完整值绑定键唯一，观察属于固定 \(\mathbf I\) 的 \(\mathrm{Observation}_{\mathbf I}\)。
- 从 \(\sigma_0\) 按记录次序施加效果时，每次组合均在[状态组合的定义域](#状态组合的定义域)内。

这些条件只规定记录及其状态重建的结构有效性。控制流可行性所需的证据见[证明边界与待证义务](#证明边界与待证义务)。

\[
\mathrm{History}_{\mathbf I}
:=\{(\sigma_0,\Delta)\in\mathrm{State}\times\mathrm{Record}_{\mathbf I}^{\ast}
:\mathrm{WF}_{\mathbf I}(\sigma_0,\Delta)\}.
\]

其中 \(\mathrm{History}_{\mathbf I}\) 为统一历史类型，\(\sigma_0\) 为其入口状态，\(\Delta\) 为其有序记录，\(\mathrm{WF}_{\mathbf I}\) 为上述结构良构观察。历史相等采用状态结构相等与序列逐项相等。

\[
\operatorname{history}(\sigma_0,\Delta):=(\sigma_0,\Delta)\in\mathrm{History}_{\mathbf I}.
\]

其中 \(\operatorname{history}\) 是从 \(\mathrm{State}\times\mathrm{Record}_{\mathbf I}^{\ast}\) 到 \(\mathrm{History}_{\mathbf I}\) 的部分构造，定义域恰为满足 \(\mathrm{WF}_{\mathbf I}(\sigma_0,\Delta)\) 的输入；无定义时不返回成功的空历史。

\[
H_N=\operatorname{history}(\sigma_N,\Delta_N).
\]

其中 \(\sigma_N\) 为 NotTaken 侧记录的入口状态，\(\Delta_N\) 为该侧逐步记录，\(H_N\in\mathrm{History}_{\mathbf I}\) 为其历史，构造要求该输入良构。

\[
H_T=\operatorname{history}(\sigma_T,\Delta_T).
\]

其中 \(\sigma_T\) 为 Taken 侧记录的入口状态，\(\Delta_T\) 为该侧逐步记录，\(H_T\in\mathrm{History}_{\mathbf I}\) 为其历史，构造要求该输入良构。

Taken 与 NotTaken 只区分历史在一次合并中的角色，两侧使用同一个类型与接口。合并凭据包含历史记录与其覆盖证据两部分，证据及其适用域由[路径合并接口契约](Jump/路径合并-接口契约.md)维护。

## 状态重建

### 状态组合的定义域

对有效状态 \(\sigma\in\mathrm{State}\) 与单步记录 \(\delta=(j,d,j',\Lambda)\)，\(\sigma\otimes\delta\) 表示按 \(\Lambda\) 的次序施加 [step 的状态变换组合](step.md#状态变换的组合)。Expression 更新与五类观察的结构并集由该节引用的对象规则维护。组合只读取已记录的效果，不调用 step，不重新取源，也不重算指令语义。

此组合是到 \(\mathrm{State}\) 的部分函数。其定义域要求输入状态有效、\(\Lambda\) 的每个效果对类型正确，并且按序组合的每个中间状态和下一效果均满足组合规则的前提；观察均须属于同一 \(\mathrm{Observation}_{\mathbf I}\)。空 \(\Lambda\) 保留输入状态。局部结果位宽错误、值绑定键不唯一、观察不属于 \(\mathrm{Observation}_{\mathbf I}\)，或任一中间组合无定义时，整个 \(\sigma\otimes\delta\) 无定义。重建成功只保证结构组合有定义，指令生成与记录来源仍须证明。

输入补充的记录以其已准备出的值关系作为 Expression 效果，局部观察分量为空；其前提与先后次序由 [Expression](../Expr/Expr.md#未记录虚拟寄存器的取源)和 step 维护。缺失的补充效果须作为记录完整性的证明缺口处理。

### 初态与递推

\[
\sigma^{(0)}=\sigma_0.
\]

其中 \(\sigma_0\in\mathrm{State}\) 是历史 \(H=\operatorname{history}(\sigma_0,\Delta)\) 保存的入口状态，\(\sigma^{(0)}\) 是零步重建状态。该入口可以是路径片段的入口，不限于 create 生成的程序初态。

\[
\sigma^{(k+1)}=\sigma^{(k)}\otimes\delta_{k+1}.
\]

其中 \(0\le k<n\)，\(n=|\Delta|\)，\(\delta_{k+1}\) 是第 \(k+1\) 步记录，\(\sigma^{(k)}\in\mathrm{State}\) 是其执行前重建状态；\(\otimes\) 是上述部分组合，历史良构性保证每次使用有定义。

### 逐步状态与末态

\[
\operatorname{stateAt}(H,k):=\sigma^{(k)}.
\]

其中 \(H=\operatorname{history}(\sigma_0,\Delta)\in\mathrm{History}_{\mathbf I}\)，\(k\in\{0,\ldots,|\Delta|\}\)，\(\sigma^{(k)}\) 为上述递推状态；\(\operatorname{stateAt}\) 在这些 \((H,k)\) 上是到 \(\mathrm{State}\) 的总函数，越界索引无定义。

\[
\operatorname{final}(H):=\sigma^{(n)}.
\]

其中 \(H\in\mathrm{History}_{\mathbf I}\)，\(n=|\Delta|\)，\(\sigma^{(n)}\) 为完成全部记录后的状态；\(\operatorname{final}:\mathrm{History}_{\mathbf I}\to\mathrm{State}\) 是总函数。有限片段也有末态，末态存在不要求最后位置为 Exit。

### 重建的基本性质

**命题 H1（唯一性与有效性）。** 对任意良构历史，各 \(\sigma^{(k)}\) 唯一且有效，\(\operatorname{stateAt}(H,0)=\sigma_0\)，\(\operatorname{stateAt}(H,n)=\operatorname{final}(H)\)。空历史的末态为入口状态。保留同一入口与前 \(k\) 步记录的两份历史，其前 \(k\) 步重建状态分别相同。

**证明。** 对步数归纳。零步由初态定义得到唯一的有效状态。每个局部结果使用既有确定的更新规则，有限序列依次组合仍确定；良构性保证每次组合在定义域内，更新的有效性由所引用的对象规则保持。因此归纳步骤成立。stateAt 与 final 的结论分别由其定义得到。两份历史的入口相同，逐次施加相同效果，即得共同前缀状态相同。\(\square\)

**命题 H2（条件性重建一致）。** 若历史入口状态等于原路径片段的入口状态，逐步保留原路径实际使用的全部准备效果及其顺序，且每步原后继状态正由所引用的状态组合产生，则每个重建状态等于对应的原路径状态。

**证明。** 零步两者均为记录的入口状态。假设第 \(k\) 步前状态相同，第 \(k+1\) 步使用相同的准备效果与相同的组合规则，因确定性得到相同后继状态。对 \(k=0,\ldots,n-1\) 归纳即得结论。\(\square\)

## Expression 差异与观察依赖

Expression 描述值关系与计算结果，比较的两侧不要求产生结构相等的 Expression。\(\mathrm{Observation}_{\mathbf I}\) 的五类语义事实分别为 Helper 的外部调用观察、Branch 的控制流选择与条件、Return 的正常返回结果、MapWrite 的 Map 元素内写入及 PacketWrite 的包写入；构造和解释见[逐步记录类型的观察分量](#逐步记录与统一类型)。

### 有限符号项的递归依赖

有限项的常元、变元和应用结构沿用 [Expression](../Expr/Expr.md#索引)。对位宽集合 \(W\) 中的各 \(w\)，\(\mathrm{Var}_w\) 包含固定输入变元与带动态调用身份的返回值变元。它们按位宽保留身份。

\[
\mathcal A:=\bigsqcup_{w\in W}\mathrm{Var}_w.
\]

其中 \(\mathcal A\) 为带位宽标签的变元集合，\(\bigsqcup\) 为不交并，\(W\) 与 \(\mathrm{Var}_w\) 由 Expression 的项类型维护；下式把每个变元通过其所属位宽的自然嵌入视为 \(\mathcal A\) 中的元素。

\[
\operatorname{dep}_w:\mathrm{Term}_w\longrightarrow\mathscr F(\mathcal A).
\]

其中 \(\mathrm{Term}_w\) 为位宽 \(w\) 的有限项类型，\(\operatorname{dep}_w\) 为到有限变元集合的总函数，其递归规则如下。

\[
\operatorname{dep}_w(C_w(c)):=\varnothing.
\]

其中 \(C_w(c)\) 为值 \(c\) 的位宽 \(w\) 常元，\(\varnothing\) 为空依赖集合。

\[
\operatorname{dep}_w(a):=\{a\}\qquad(a\in\mathrm{Var}_w).
\]

其中 \(a\) 是位宽 \(w\) 的变元叶子，\(\{a\}\subseteq\mathcal A\) 保留其输入身份或调用身份与寄存器标记。

\[
\operatorname{dep}_w\bigl(f(t_1,\ldots,t_r)\bigr)
:=\bigcup_{q=1}^{r}\operatorname{dep}_{w_q}(t_q).
\]

其中 \(f\) 是签名 \((w_1,\ldots,w_r)\to w\) 的形式运算符，\(t_q\in\mathrm{Term}_{w_q}\)，\(r\) 为有限参数个数，\(\bigcup\) 合并各子项的依赖集合；运算符的固定参数保持不变。

项有限，递归严格进入子项，所以此函数有定义、唯一且输出有限。它收集项中出现的变元，允许保守地保留数值上已经抵消的依赖。

**命题 H3（固定解释下的项值保持）。** 设 \(t\in\mathrm{Term}_w\)，两组变元赋值 \(\nu,\nu'\) 在 \(\operatorname{dep}_w(t)\) 上相等。固定同一个解释补全 \(\theta\)，并要求该项各运算的解释是按其显式参数求值的确定函数，则

\[
\left[\!\left[t\right]\!\right]_{\nu,\theta}
=\left[\!\left[t\right]\!\right]_{\nu',\theta}.
\]

其中 \(\left[\!\left[t\right]\!\right]_{\nu,\theta}\in\mathbb B_w\) 为 Expression 的项解释，\(\mathbb B_w\) 为位宽 \(w\) 的位向量集合，\(\nu,\nu'\) 为上述赋值，\(\theta\) 为固定的解释补全。

**证明。** 对有限项结构归纳。常元解释与赋值无关。变元属于自己的依赖集合，故两赋值给出同值。应用项的依赖集合包含每个子项的依赖集合，归纳假设给出全部参数值相同；固定的确定函数对相同参数给出相同结果。\(\square\)

### MapLookup 的显式项依赖

对 \(p=\operatorname{mapLookup}(\varepsilon,t_m,\vec k)\in\mathrm{MapLookup}\)，\(t_m\in\mathrm{Term}_{32}\) 是 Map 参数项，\(\vec k=(k_1,\ldots,k_{L_k})\in\mathrm{BytesTerm}(L_k)\) 是调用时冻结的完整键字节数组；构造与解释见[MapLookup](../Predicate/MapLookup谓词.md#类型定义)。

\[
\operatorname{dep}_{\mathrm{MapLookup}}(p)
:=\operatorname{dep}_{32}(t_m)
\cup\bigcup_{j=1}^{L_k}\operatorname{dep}_{32}(k_j).
\]

其中 \(\operatorname{dep}_{\mathrm{MapLookup}}:\mathrm{MapLookup}\to\mathscr F(\mathcal A)\) 收集 Map 项与每个键字节项中出现的变元；\(L_k=0\) 时字节项的并集为空。每项的依赖有限且数组长度有限，故结果有限。该集合只描述显式项依赖，调用参数的对象与布局、事件身份等联系仍受[H-O3](#完整依赖提取)约束。

固定同一 \(\varepsilon\)、键长度与解释补全 \(\theta\)，若 \(\nu,\nu'\) 在 \(\operatorname{dep}_{\mathrm{MapLookup}}(p)\) 上相等且满足 H3 的确定函数前提，则 H3 分别给出 Map 项及全部键字节项的解释相等。[MapLookup 的事件解释](../Predicate/MapLookup谓词.md#类型定义)按这些显式分量构成，故两组赋值下的事件解释相等。从入口 Expression 差异到这些赋值对应的联系仍须由 H-O3 证明。

### 差异无关性的依据

若入口 Expression 差异在影响任何相关观察之前已被消除，可以判定该差异对所关注的观察无关。判定必须有数学依据，并明确所关注观察和适用范围。例如，在观察解释已证明仅依赖其固定标签、身份与显式参数项时，H3 可以证明这些参数值保持；从入口 Expression 差异到这些参数赋值对应的联系仍需证明。

依赖集合的空缺只有在 H3 的固定解释前提与观察解释对应都成立时才能用于上述判定。完整依赖提取的缺口列在[证明边界与待证义务](#证明边界与待证义务)。

该判定受以下约束：

- 写入一个寄存器，本身不能证明对其旧值的依赖已经消失。例如新绑定 \(r=f(t)\) 中的 \(t\) 若保留旧值依赖，写入后仍然相关；其他寄存器、资源或已构造项也可能保留该依赖。
- Branch、Return、MapWrite 与 PacketWrite 观察的语义同样必须保持，不能只检查外部调用参数。
- 已发生的观察不能仅因不影响后续计算而删除。记录入口已含的观察也参与这一约束。

## 证明边界与待证义务

### 控制流与记录来源

历史重建状态变化，单凭重建成功不能证明替换入口状态后仍遵循同一控制流。记录中的位置与方向属于结构信息。Branch 观察可以作为方向保持的证据；控制流条件的完整覆盖仍需证明，包括所需的条件分支、间接目标、调用返回配对以及最外层正常返回的判定。

**义务 H-O1（记录完整性与来源）。** 为具体记录方式证明每步效果、输入补充及局部次序与原步骤的准备结果一致，并说明记录中的动态身份来源。H2 的前提需由这一对应提供，不能由结构良构性推出。

**义务 H-O2（替换入口的路径保持）。** 对所声明的替换入口域，证明相关控制流条件及目标绑定保持，且记录覆盖该路径所需的全部条件。已有 Branch 观察的解释保持只有在该覆盖证明成立后才能支撑完整的同路径结论。

### 完整依赖提取

**义务 H-O3（入口差异到观察的依赖对应）。** 为采用的 Expression 与 \(\mathrm{Observation}_{\mathbf I}\) 类型建立入口差异、局部结果及观察解释之间的依赖联系，覆盖 Helper、Branch、Return、MapWrite 与 PacketWrite 五类事实，包括 MapLookup 的 Map 参数项与完整键字节项。递归 dep 只处理显式有限项中的变元；资源身份与别名、地址项所指对象、运算符参数、外部调用结果契约、解释补全变化及动态事件身份的影响须有独立依据。结构不能表达所需联系时，应补充相应语义与证明，不能由空依赖集合或一次覆写宣布差异无关。

### 局部结果顺序与重复事件

历史保留步骤次序及每一步 \(\Lambda_k\) 中的局部结果次序。每个 \(\mathcal{O}_i\in\mathscr F(\mathrm{Observation}_{\mathbf I})\) 仍为集合，其内部没有事件先后顺序。五类结构累积不能恢复事件顺序，也不能仅从相邻累积集合之差恢复重复事件；组合定义域见[状态组合的定义域](#状态组合的定义域)。

直接读取各步记录的 \(\mathcal{O}_i\)，可以取得该步已记录的成员及其步骤归属。[Helper 的动态身份规则](../Predicate/Helper谓词.md#类型定义)使不同次调用使用不同身份，因而相同参数的不同调用仍可区分。相同结构成员在一个局部集合中的重复只保留一次；一个效果对内部多个事件的先后不能由该集合恢复。

**义务 H-O4（动态身份与可恢复范围）。** 各事件类型的身份规则须说明重复执行如何区分、身份与具体步骤如何对应，以及由历史究竟能恢复事件出现次数、步骤归属还是更细的顺序。对已丢失的重复次数或局部集合内部顺序，不得声称已经恢复完整事件轨迹。

## 范围外的问题

history 的输入是 not_taken 这段上的 \((E_i,O_i)\) 列表，输出是寄存器列表。一个寄存器进入这份列表，当它在较前的 \(E_i\) 里写过值、又在较后的 \(E_k\) 里再次写值，或者它出现在这些 \(E_i\) 里但所有 \(O_i\) 都没有提到它。实现是 `Node.history`。

Taken推演回到父指令且这次只给出 not_taken 时，用这份列表比较新旧 not_taken 的值绑定差。差里的寄存器都在列表里时，两次 not_taken 的观察生成一致。驱动到这里停止，不再把这份列表交给另一份合并接口。

## 相关文档

- [Expression 的当前内容](../Expr/Expr.md#索引)：架构内部值关系、符号项、局部值效果与覆写规则。
- [观察定义](../Predicate/谓词定义.md)：五类观察域、结构相等、混合观察结构累积及解释与历史对应义务。
- [Helper 各类观察与共同约定](../Predicate/Helper谓词.md#类型定义)：调用观察解释与动态调用身份。
- [Branch观察](../Predicate/Branch谓词.md)：候选方向、条件及其固定源项的解释。
- [Return观察](../Predicate/Return谓词.md)：最外层正常返回结果及其跨位宽对应。
- [MapWrite观察](../Predicate/MapWrite谓词.md)：Map 元素内写入及所需解释参数。
- [PacketWrite观察](../Predicate/PacketWrite谓词.md)：包写入、动态身份与源项解释。
- [step](step.md#状态变换的组合)：局部结果的状态组合规则。
- [路径](路径.md)：位置、方向与逐次执行的结构。
- [路径合并接口契约](Jump/路径合并-接口契约.md)：历史在合并中的角色及覆盖证据。
