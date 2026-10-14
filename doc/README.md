# 数学文档索引

文档中的「定义」「假设」「命题」分别表示模型选择、必要前提与可推导结论。

## 文档归属与阅读次序

create、step、history、merge 与合并步使用数学契约；create 的入口假设和 step 的指令规则按目标架构给定。产品 create/step 的 RV32IMC 归属与模块构建图见[工程模块与迁移](NodeInference/路径合并FFI.md#工程模块与迁移)，跨架构研究与证明限度见[语义范围与证据边界](NodeInference/路径合并FFI.md#语义范围与证据边界)。数学定义和公式由以下所属正文维护，FFI 与现有实现差异由工程文档维护。

1. [位向量](Expr/Term/位向量.md)与[共同数值函数](Expr/Term/数值函数.md)：Expr 右值使用的数值记号与纯数值函数。
2. [寄存器定义](寄存器定义.md)：五类对象的身份、位宽、值域与相等，只维护定义。
3. 表达式主题见 [Expr 索引](Expr/Expr.md#索引)。
4. 谓词与观察集合主题依次读[类型与结构相等](Predicate/谓词定义.md#类型与结构相等)、[Helper 共同定义](Predicate/Helper谓词.md)、[MapLookup谓词](Predicate/MapLookup谓词.md)、[MapUpdate谓词](Predicate/MapUpdate谓词.md)、[MapDelete谓词](Predicate/MapDelete谓词.md)、[OtherHelper谓词](Predicate/OtherHelper谓词.md)、[Branch谓词](Predicate/Branch谓词.md)、[Return谓词](Predicate/Return谓词.md)、[MapWrite谓词](Predicate/MapWrite谓词.md)、[PacketWrite谓词](Predicate/PacketWrite谓词.md)、[五类观察结构累积及解释义务](Predicate/谓词定义.md#观察集合累积与可满足性)、[观察集合与历史顺序](Predicate/谓词定义.md#观察集合与历史顺序)、[跨架构谓词](Predicate/跨架构谓词.md)。固定程序的观察域为 \(\mathrm{Predicate}_{\mathbf I}\)：Helper 的外部调用观察、Branch 的选定方向与条件、Return 的最外层正常返回结果、MapWrite 的 Map 元素内写入与 PacketWrite 的包写入分别由各所属正文维护；跨架构规范观察与相等由 CrossPred 的所属正文维护。
5. [路径](NodeInference/路径.md)：指令序号、机器地址、字节偏移与不透明节点引用的区别，以及方向。
6. [create](NodeInference/create.md)：按目标架构构造初始语义状态，含 RV32 的入口条件与初始关系；RV32IMC 产品入口的实现对应见[工程模块与迁移](NodeInference/路径合并FFI.md#工程模块与迁移)。
7. [数学 step](NodeInference/step.md)：接收指令序列、当前指令序号与执行前状态，返回候选的局部语义增量；调用方按既有规则施加组合，其归属[尚待讨论](NodeInference/step.md#状态变换的组合)。统一的 \(\mathrm{Record}_{\mathbf I}\) 与 \(\mathrm{History}_{\mathbf I}\) 见 [共同 History](NodeInference/History.md#逐步记录与统一类型)，记录涵盖 Helper、Branch、Return、MapWrite 与 PacketWrite 的局部结果；混合观察的组合边界见[History 的状态组合定义域](NodeInference/History.md#状态组合的定义域)。RV32IMC 产品 step 的接口差异见[工程边界](NodeInference/路径合并FFI.md#共同接口与实现边界)。
8. [证明义务-路径合并完备](NodeInference/Jump/证明义务-路径合并完备.md)：精确配置共享判据的完备性及在前提 P1 至 P4 下的有限后续共享性质。
9. [共同路径合并契约](NodeInference/Jump/路径合并-接口契约.md)：同次分支两侧记录的 merge 契约，规定后缀复用、特殊循环准入与拒绝的结果保证及证据义务。
10. [共同分支合并处理](NodeInference/分支合并处理.md)：一次条件分支的推进顺序、merge-step 与结果处置。PathMerge 的精确配置比较单 String 导出、线协议、运行诊断及证据边界见[路径合并FFI](NodeInference/路径合并FFI.md)。
11. [跨架构比较](NodeInference/跨架构比较.md)：[跨架构谓词](Predicate/跨架构谓词.md)的判断、规范 JSON、位置覆盖和控制流对应；既有七类结构诊断的线协议及其实现偏差单独保留，结构结论不建立行为等价。

每个主题的定义和公式在对应正文中维护，其他正文通过链接引用。

## 比较问题

比较的对象与约束见 [Expr 的比较关系](Expr/Expr.md#比较关系)。赋值覆写见[关系集合按键覆写](Expr/Expr.md#关系集合按键覆写)。后继与历史条件见[比较指令处理](NodeInference/Jump/待处理.md#比较指令处理)。

- [Expr 的比较关系](Expr/Expr.md#比较关系)：值与约束角色、符号含义、解释、部分判定和补关系。
- [比较指令处理](NodeInference/Jump/待处理.md#比较指令处理)：RV32/eBPF 取源、各指令两侧 Expr、方向选择及历史保存。

## 证明之间的依赖

符号项的类型与纯数值全函数假设给出闭项求值的良定义性。solve 的解释保持性随后支撑指令符号值与数值公式的一致性。值绑定唯一性与严格覆写性质支撑初态、\(\sigma_i=(E_i,P_i)\) 和状态更新的结构有效性，其中 \(E_i\) 是 Expr 分量，\(P_i\) 是谓词分量。

精确配置共享判据及其条件性后续一致性见[证明义务-路径合并完备](NodeInference/Jump/证明义务-路径合并完备.md)，共享后的完整历史解释仍需证明。该判据本身不证明 \(\sigma_i\) 符合真实指令语义。

## 当前证明边界

以下结论已经在本文档体系中给出定义层面的证明：

- 闭项求值与 solve 的性质见[solve 的化简与求值](Expr/Term/solve.md#solve-的化简与求值)。单个 Expr 的解释保持见[表达式定义](Expr/Expr.md#关系解释)。
- 严格覆写的结构性质与更新代数见[关系集合按键覆写](Expr/Expr.md#结构性质)。
- 比较的互补方向见[比较关系](Expr/Expr.md#位宽与补关系)。指令生成与历史条件见[比较指令处理](NodeInference/Jump/待处理.md)。五类观察结构累积的集合性质见[观察集合累积与可满足性](Predicate/谓词定义.md#观察集合累积与可满足性)。
- 局部值效果的类型与纯数值子域解释保持见[局部值效果的类型与解释保持](Expr/Expr.md#局部值效果的类型与解释保持)。低位写回的高位清零见[真实寄存器低位视图与写回](Expr/寄存器/真实寄存器.md#真实寄存器低位视图与写回)。固定与只读值保持见[真实寄存器赋值](Expr/寄存器/真实寄存器.md#真实寄存器赋值)。链接目标类别见[跳转链接值赋值](Expr/寄存器/真实寄存器.md#跳转链接值赋值)。多目标读取见[多目标更新与同一执行前关系](Expr/Expr.md#多目标更新与同一来源)。原子数值规则的旧值返回见[原子数值更新与旧值返回](Expr/寄存器/原子数值更新与旧值返回.md#旧值返回性质)。
- 对象身份见[寄存器定义](寄存器定义.md)。字段性质见[单元字段读写](Expr/寄存器/单元字段读写.md#字段覆盖性质)。包拼接性质见[包字节读写](Expr/寄存器/包字节.md#拼接与重叠性质)。分类与 \(\sigma_i\) 的性质见[指令结果的前提](Expr/Expr.md#来源与结构性质)。
- 初态关系的结构性质与代数可满足性见[create 的 RV32 初态性质](NodeInference/create.md#初态及其性质)。
- OtherHelper 生成的唯一性与参数齐备见[OtherHelper谓词](Predicate/OtherHelper谓词.md#数学性质)，动态调用区分见[Helper 共同性质](Predicate/Helper谓词.md#数学性质)；返回更新的有限性、位宽与 lookup 关联的结构有效性见[Helper 谓词的性质](Predicate/Helper谓词.md#数学性质)。
- 精确配置共享判据的完备性由配置相等给出；在前提 P1 至 P4 下的一步一致性、有限深度后续一致性与共享安全性见[证明义务-路径合并完备](NodeInference/Jump/证明义务-路径合并完备.md)。

以下问题仍需定义或证明：

- Stack、Map、Context 与 Packet 访问的资源身份、范围、权限与对齐条件和访问有效性之间的语义联系，仍须定义或证明；MapWrite 与 PacketWrite 已规定写入观察的构造及生成前提。当前 \(\mathrm{Predicate}_{\mathbf I}\) 包含 Helper、Branch、Return、MapWrite 与 PacketWrite，类型及各类解释入口见[类型与结构相等](Predicate/谓词定义.md#类型与结构相等)。
- 在累积条件下判定可行性、检测矛盾及约束推理的可靠性仍须定义或证明；现有规则见[累积不等于可行性求解](Predicate/谓词定义.md#累积不等于可行性求解)。
- helper 调用与写入的动态身份已有局部构造要求，其他事件身份、完整轨迹与顺序观察规则仍须定义，当前边界见[观察集合与历史顺序](Predicate/谓词定义.md#观察集合与历史顺序)及[History 动态身份义务](NodeInference/History.md#局部结果顺序与重复事件)。
- 五类混合观察的结构累积已规定；入口语义合法性、各类解释与实际步骤和历史的对应仍须证明，见[观察解释与历史义务](Predicate/谓词定义.md#观察集合累积与可满足性)。这些集合性质与现有局部命题不能直接推出资源访问正确或完整行为等价。产品生成覆盖与缺口见[五类观察的实现对应](NodeInference/路径合并FFI.md#五类观察的实现对应)。
- 指令操作数所确定的访问对象与实际访问对象的一致性、跨单元一致性及访问有效性的证明。[Expr 指令结果的前提](Expr/Expr.md#指令结果的前提)要求访问对象唯一确定且访问有效，不自动证明具体访问满足它们。
- helper 的 ABI 返回项与 lookup 关联已由[Helper 结果规则](Predicate/Helper谓词.md#生成的-expr)定义；这些项与真实外部调用结果的可靠对应、调用后的资源变化及安全性仍须证明或补全契约。内部调用的寄存器变化与调用返回配对，以及既有 helper 编号模型以外的外部调用观察，仍须定义或证明。
- 任意循环摘要的可靠性，以及有限退出以外的观察语义。
- 精确共享所依赖的具体规则外延性与闭合性、动态身份与名称的一致性、共享后的完整历史解释及无限行为对应，见[仍待证明的义务](NodeInference/Jump/证明义务-路径合并完备.md#仍待证明的义务)。

## 记号约定

寄存器 Reg 的定义集中在[寄存器文档](寄存器定义.md)中维护。Term、Rel 与 Expr 的定义集中在 [Expr 目录](Expr/Expr.md#索引)中维护。固定指令序列 \(\mathbf I\) 的五类谓词域 \(\mathrm{Predicate}_{\mathbf I}\) 集中在 [谓词定义](Predicate/谓词定义.md)中维护。共同数值函数集中在[位向量文档](Expr/Term/数值函数.md#共同数值函数)中维护。原始指令 Insn 见[指令序列](NodeInference/路径.md#指令序列与程序位置)，语义状态见[step](NodeInference/step.md#语义状态)；统一逐步记录与历史类型见 [History](NodeInference/History.md#逐步记录与统一类型)，构造初始语义状态的接口见[create](NodeInference/create.md)。各值规则使用所给位宽与符号提升记号；初态文档只增加入口假设。

集合并集、顺序组合、寄存器覆写和观察合并具有不同定义，不能因符号相近而互换。未定义、已证明不可行与正常返回也分别保留其数学含义。
