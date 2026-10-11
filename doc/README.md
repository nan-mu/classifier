# 数学文档索引

文档中的「定义」「假设」「命题」分别表示模型选择、必要前提与可推导结论。

## 文档归属与阅读次序

1. [位向量与共同数值函数](Expr/待处理.md#位向量与共同数值函数)：Expr 右值使用的数值记号与纯数值函数。
2. [寄存器定义](寄存器定义.md)：四类对象的身份、位宽、值域与相等，只维护定义。
3. 表达式主题见 [Expr 索引](Expr/待处理.md)。
4. 谓词与观察集合主题依次读[类型与结构相等](Predicate/谓词定义.md#类型与结构相等)、[Helper 共同定义](Predicate/Helper谓词.md)、[MapLookup谓词](Predicate/MapLookup谓词.md)、[MapUpdate谓词](Predicate/MapUpdate谓词.md)、[MapDelete谓词](Predicate/MapDelete谓词.md)、[OtherHelper谓词](Predicate/OtherHelper谓词.md)、[Branch谓词](Predicate/Branch谓词.md)、[Return谓词](Predicate/Return谓词.md)、[MapWrite谓词](Predicate/MapWrite谓词.md)、[PacketWrite谓词](Predicate/PacketWrite谓词.md)、[Helper 累积与五类观察累积义务](Predicate/谓词定义.md#观察集合累积与可满足性)、[观察集合与历史顺序](Predicate/谓词定义.md#观察集合与历史顺序)。固定程序的观察域为 \(\mathrm{Predicate}_{\mathbf I}\)：Helper 的外部调用观察、Branch 的选定方向与条件、Return 的最外层正常返回结果、MapWrite 的 Map 元素内写入与 PacketWrite 的包写入分别由各所属正文维护。
5. [路径](NodeInference/路径.md)：指令序号、机器地址、字节偏移与节点引用的区别，以及展开图、方向和执行路径。
6. [create](NodeInference/create.md)：按架构入口契约构造初始语义状态，含 RV32 的入口条件与初始关系。
7. [step](NodeInference/step.md)：step 处理单条指令并准备后继状态，expand 校验入口、建立根节点并调度有限展开。统一的 \(\mathrm{Record}_{\mathbf I}\) 与 \(\mathrm{History}_{\mathbf I}\) 见 [History](NodeInference/History.md#逐步记录与统一类型)，记录涵盖 Helper、Branch、Return、MapWrite 与 PacketWrite 的局部效果；混合观察的组合边界见[History 的状态组合定义域](NodeInference/History.md#状态组合的定义域)。
8. [路径语言与位置消去](NodeInference/Jump/待处理.md#路径语言与位置消去)：含循环路径语言、最小解及行为关系解释。
9. [证明义务-路径合并完备](NodeInference/Jump/证明义务-路径合并完备.md)：精确配置共享判据的完备性及在前提 P1 至 P4 下的有限后续共享性质。
10. [路径合并-接口契约](NodeInference/Jump/路径合并-接口契约.md)：同次分支两侧记录的合并契约，规定后缀复用、特殊循环准入与拒绝的结果保证及证据义务。

每个主题的定义和公式在对应正文中维护，其他正文通过链接引用。

## 比较问题

比较的对象与约束见 [Expr 的比较关系](Expr/待处理.md#比较关系)。赋值覆写见[关系集合按键覆写](Expr/待处理.md#关系集合按键覆写)。后继与历史条件见[节点的比较指令处理](NodeInference/Jump/待处理.md)。

- [Expr 的比较关系](Expr/待处理.md#比较关系)：值与约束角色、符号含义、解释、部分判定和补关系。
- [节点的比较指令处理](NodeInference/Jump/待处理.md)：RV32/eBPF 取源、各指令两侧 Expr、方向选择及历史保存。

## 证明之间的依赖

符号项的类型与纯数值全函数假设给出闭项求值的良定义性。solve 的解释保持性随后支撑指令符号值与数值公式的一致性。值绑定唯一性与严格覆写性质支撑初态、局部效果和状态更新的结构有效性。

局部处理终止及有限候选假设支撑有预算展开的终止与有限性。当前追加构造的边由已有节点引用指向新引用，因而展开图无环；有限性与无环性共同推出正常返回历史集合有限。同位置到达的精确配置共享判据及其条件性后续一致性见[证明义务-路径合并完备](NodeInference/Jump/证明义务-路径合并完备.md)，共享后的完整历史解释仍需证明。这些结构结论本身不证明局部效果符合真实指令语义。

路径消去证明针对图上的全部有限路径。将其解释为实际行为，需要边关系、条件测试与调用返回配对的语义对应；使用近似摘要时还需独立证明摘要可靠。

## 当前证明边界

以下结论已经在本文档体系中给出定义层面的证明：

- 闭项求值与 solve 的性质见[符号项求值与常量折叠](Expr/待处理.md#符号项求值与常量折叠)。单个 Expr 的解释保持见[表达式定义](Expr/待处理.md#关系解释)。
- 严格覆写的结构性质与更新代数见[关系集合按键覆写](Expr/待处理.md#结构性质)。
- 比较的互补方向见[比较关系](Expr/待处理.md#位宽与补关系)。指令生成与历史条件见[比较指令处理](NodeInference/Jump/待处理.md)。既有 Helper 谓词累积的性质见[观察集合累积与可满足性](Predicate/谓词定义.md#观察集合累积与可满足性)。
- 局部值效果的类型与纯数值子域解释保持见[局部值效果的类型与解释保持](Expr/待处理.md#局部值效果的类型与解释保持)。低位写回的高位清零见[真实寄存器低位视图与写回](Expr/待处理.md#真实寄存器低位视图与写回)。固定与只读值保持见[真实寄存器赋值](Expr/待处理.md#真实寄存器赋值)。链接目标类别见[跳转链接值赋值](Expr/待处理.md#跳转链接值赋值)。多目标读取见[多目标更新与同一执行前关系](Expr/待处理.md#多目标更新与同一来源)。原子数值规则的旧值返回见[原子数值更新与旧值返回](Expr/待处理.md#旧值返回性质)。
- 对象身份见[寄存器定义](寄存器定义.md)。字段性质见[单元字段读写](Expr/待处理.md#字段覆盖性质)。包拼接性质见[包字节读写](Expr/待处理.md#拼接与重叠性质)。分类与局部效果性质见[指令局部效果的前提](Expr/待处理.md#来源与结构性质)。
- 初态关系的结构性质与代数可满足性见[create 的 RV32 初态性质](NodeInference/create.md#初态及其性质)。
- OtherHelper 生成的唯一性与参数齐备见[OtherHelper谓词](Predicate/OtherHelper谓词.md#数学性质)，动态调用区分见[Helper 共同性质](Predicate/Helper谓词.md#数学性质)；返回更新的有限性、位宽与 lookup 关联的结构有效性见[辅助调用结果](Expr/待处理.md#辅助调用结果)。
- 在局部终止与有限候选假设下，展开的终止、有限性及当前追加构造的无环性见[展开的终止与结构性质](NodeInference/step.md#展开的终止与结构性质)。返回历史的有限性见[正常返回历史](NodeInference/step.md#正常返回历史)。
- 位置消去的路径保持、查询语言的消去顺序无关性及循环语言方程的最小解见[路径语言与位置消去](NodeInference/Jump/待处理.md)。
- 精确配置共享判据的完备性由配置相等给出；在前提 P1 至 P4 下的一步一致性、有限深度后续一致性与共享安全性见[证明义务-路径合并完备](NodeInference/Jump/证明义务-路径合并完备.md)。

以下问题仍需定义或证明：

- Stack、Map 与 Packet 访问的资源身份、范围、权限与对齐条件和访问有效性之间的语义联系，仍须定义或证明；MapWrite 与 PacketWrite 已规定写入观察的构造及生成前提。当前 \(\mathrm{Predicate}_{\mathbf I}\) 包含 Helper、Branch、Return、MapWrite 与 PacketWrite，类型及各类解释入口见[类型与结构相等](Predicate/谓词定义.md#类型与结构相等)。
- 在累积条件下判定可行性、检测矛盾及约束推理的可靠性仍须定义或证明；现有规则见[累积不等于可行性求解](Predicate/谓词定义.md#累积不等于可行性求解)。
- helper 调用与写入的动态身份已有局部构造要求，其他事件身份、完整轨迹与顺序观察规则仍须定义，当前边界见[观察集合与历史顺序](Predicate/谓词定义.md#观察集合与历史顺序)及[History 动态身份义务](NodeInference/History.md#局部效果顺序与重复事件)。
- Branch、Return、MapWrite、PacketWrite 及混合观察集合的累积规则、定义域、入口合法域与历史接入仍须规定，见[五类观察累积义务](Predicate/谓词定义.md#观察集合累积与可满足性)。既有 Helper [结构累积](Predicate/谓词定义.md#结构并集)的集合性质不能代替这些规则；现有局部命题不能直接推出资源访问正确或完整行为等价。
- 地址向虚拟单元归约的正确性、跨单元一致性及访问有效性的证明。[Expr 分类前提](Expr/待处理.md#指令局部效果的前提)将唯一绑定和有效访问列为前提，不自动证明具体访问满足它们。
- 外部调用结果、寄存器变化与调用返回配对。各 helper 的具体返回契约、资源变化与调用安全性，以及七种类型以外的外部调用谓词，仍须定义或证明。
- 两种指令集的入口对应仍须定义或证明；跨指令集的输入、返回位宽与 Helper、Branch、Return、MapWrite、PacketWrite 观察对应仍须定义，类型及解释见[五类观察域](Predicate/谓词定义.md#类型与结构相等)，返回结果的对应见[跨架构返回值比较](Predicate/Return谓词.md#跨架构返回值比较)。
- 任意循环摘要的可靠性，以及有限退出以外的观察语义。
- 精确共享所依赖的具体规则外延性与闭合性、动态身份与名称的一致性、共享后的完整历史解释及无限行为对应，见[仍待证明的义务](NodeInference/Jump/证明义务-路径合并完备.md#仍待证明的义务)。

## 记号约定

寄存器 Reg 的定义集中在[寄存器文档](寄存器定义.md)中维护。Term、Rel 与 Expr 的定义集中在 [Expr 目录](Expr/待处理.md)中维护。固定指令序列 \(\mathbf I\) 的五类谓词域 \(\mathrm{Predicate}_{\mathbf I}\) 集中在 [谓词定义](Predicate/谓词定义.md)中维护。共同数值函数集中在[位向量文档](Expr/待处理.md#位向量与共同数值函数)中维护。原始指令 Insn、语义状态、节点和有限展开集中在[step](NodeInference/step.md)中维护；统一逐步记录与历史类型见 [History](NodeInference/History.md#逐步记录与统一类型)，按入口契约构造初始语义状态的接口见[create](NodeInference/create.md)。各值规则使用所给位宽与符号提升记号；初态文档只增加入口假设；代数文档中的加、乘和星号表示路径或行为组合。

集合并集、顺序组合、寄存器覆写和观察合并具有不同定义，不能因符号相近而互换。未定义、已证明不可行、正常返回与预算不足也分别保留其数学含义。
