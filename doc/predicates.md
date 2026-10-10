# Predicate：比较、返回与 helper 调用观察

本文定义比较条件、返回值观察与 helper 调用观察，说明指令如何生成它们、状态如何累积它们，以及如何从 helper Predicate 取得返回 Expr。访问观察与完整外部调用契约仍须独立规定。

位向量、Term、Expr 与关系符号采用[共同数学基础](common-math.md)第 1、4、6 节的定义；Reg 的身份采用[寄存器文档](registers.md)。本文的命题由所列定义与假设推导，不额外声称已经完成形式化证明。

## 1. 观察类型

### 1.1 类型与结构相等

令 \(W=\{32,64\}\)。观察域定义为带标签的不交并：

\[
\boxed{
\mathrm{Predicate}
=\mathrm{Cmp}_{32}\sqcup\mathrm{Ret}\sqcup\mathrm{Helper}_{32},
\qquad
\mathrm{Cmp}_{32}=\mathrm{Rel}_{32}\times\mathrm{Term}_{32}\times\mathrm{Term}_{32},
\qquad
\mathrm{Ret}=\bigsqcup_{w\in W}\mathrm{Term}_w.
}
\]

分别记为 \(\operatorname{cmp}(\bowtie,t_a,t_b)\)、\(\operatorname{ret}(t_w)\) 与 \(\operatorname{helper}(\varepsilon,h,\vec t)\)。helper 类别、参数个数及事件身份在第 6 节定义。比较条件的两个源项均为 32 位；返回观察保留值项的位宽。低位关系的参数满足 \(1\le q\le32\)。64 位比较观察不在本定义中。

两个 Predicate 结构相等，当且仅当它们的类别与各字段分别相同；项的位宽、运算符、参数与变元身份均参与比较，helper 还比较调用事件身份与 helper 类型。数学上等价的条件不必结构相等。例如，未另行归约的 \(\operatorname{cmp}(=,t_a,t_b)\) 与 \(\operatorname{cmp}(=,t_b,t_a)\) 可以是不同观察。

状态中的观察分量为有限集合

\[
\mathcal P\in\mathscr F(\mathrm{Predicate}).
\]

这里的集合相等使用上述结构相等，不以逻辑等价为商关系。

### 1.2 与 Expr 的区别

Expr \((r_w,\bowtie,t_w)\) 将当前寄存器与值项建立关系；Predicate 比较已经取得的两个源项、记录一个返回项，或记录一次 helper 调用。Predicate 没有供后续覆写的寄存器关系键。

数值比较可以生成值为 0 或 1 的 Expr，而不生成分支观察。反之，条件分支可以生成 Predicate，而不写寄存器。Expr 中出现关系符号也不自动产生相同的 Predicate。

## 2. 解释与部分判定

### 2.1 比较条件的真值

给定变元赋值 \(\nu\)，纯数值项采用共同数学中的解释。若项包含包输入或外部结果等未解释运算，还须给定一个解释补全 \(\theta\)，为这些运算指定同位宽的值函数。以下真值命题均在同一个 \((\nu,\theta)\) 下陈述，不由补全的存在推断具体访问或调用已经有效。

\[
\boxed{
\left[\!\left[\operatorname{cmp}(\bowtie,t_a,t_b)\right]\!\right]_{\nu,\theta}
=\widehat{\bowtie}
\bigl(\left[\!\left[ t_a\right]\!\right]_{\nu,\theta},
\left[\!\left[ t_b\right]\!\right]_{\nu,\theta}\bigr).
}
\]

比较在 32 位位向量上进行：无符号关系比较位模式对应的非负整数，有符号关系采用二进制补码解释。低位比较与位测试使用共同数学第 6.2 节的截取规则。

### 2.2 返回值的观察

返回观察的解释是带位宽的值记录：

\[
\left[\!\left[\operatorname{ret}(t_w)\right]\!\right]_{\nu,\theta}
=\bigl(\mathsf{return},w,\left[\!\left[ t_w\right]\!\right]_{\nu,\theta}\bigr).
\]

它没有布尔真值，不参与分支条件的合取。返回一个尚不能数值求出的符号项仍可构成返回观察；这与缺少返回值项不同。32 位与 64 位返回观察也不能仅因数值相同就直接视为相等，跨架构比较还需指定观察对应。

### 2.3 可判定与未知

设 \(D_w(t)\in\mathbb B_w\cup\{\bot\}\) 为部分数值求值，\(\bot\) 表示未取得确定数值。常元返回其值，普通输入变元与真实寄存器变元均返回 \(\bot\)；纯数值运算在全部实参已求值时应用其数值函数，否则返回 \(\bot\)；未解释运算返回 \(\bot\)。此求值不使用 \(\nu\) 或 \(\theta\)。

共同数学第 5 节的全求值与 solve 以纯数值假设 A 为前提。对含未解释运算的项，按相同的整项折叠原则扩展为

\[
\operatorname{solve}_w(t)=
\begin{cases}
C_w(a),&FV(t)=\varnothing\ \land\ D_w(t)=a\in\mathbb B_w,\\
t,&\text{其他情况}.
\end{cases}
\]

该扩展在纯数值子域上与原定义一致，未求得数值的闭项保留原项。本文以下的 solve 均采用此扩展。定义比较判定：

\[
\operatorname{decide}\bigl(\operatorname{cmp}(\bowtie,t_a,t_b)\bigr)
=
\begin{cases}
\widehat{\bowtie}(a,b),&D_{32}(\operatorname{solve}(t_a))=a\ \land\ D_{32}(\operatorname{solve}(t_b))=b,\\
\bot,&\text{其他情况}.
\end{cases}
\]

无变元并不保证所有项可求值：包含未解释运算的闭项仍可得到 \(\bot\)。未知不能替换为零或假。上述规则不利用累积条件求解，也不额外使用代数恒等式；即使两个未知源项结构相同，也不能仅凭这条求值规则判定其相等条件。

返回观察与 helper 调用观察不适用这个布尔判定，不能把它们理解为判定失败的比较条件。

## 3. 指令如何生成 Predicate

### 3.1 条件分支

设执行前状态为 \(\sigma=(\mathcal E,\mathcal P)\)。从同一快照取得分支源项，并令

\[
t_a=\operatorname{solve}(\operatorname{src}_a(\mathcal E)),
\qquad
t_b=\operatorname{solve}(\operatorname{src}_b(\mathcal E)).
\]

两种方向的局部观察分别为

\[
\boxed{
\mathcal P_{\mathrm{Taken}}=\{\operatorname{cmp}(\bowtie,t_a,t_b)\},
\qquad
\mathcal P_{\mathrm{NotTaken}}=\{\operatorname{cmp}(\overline{\bowtie},t_a,t_b)\}.
}
\]

关系补满足 \(\widehat{\overline{\bowtie}}=\neg\widehat{\bowtie}\)。若本次比较判定为真，只生成 Taken 候选；为假，只生成 NotTaken 候选；未知则生成两个候选。确定方向仍保留该方向的比较观察。每个保留候选都要求其后继有定义；缺少源项或后继绑定不等于该方向已被证明不可行。

这里的方向选择只使用本次源项判定，不从 \(\mathcal P\) 推导可行性。RV32IMC 的指令与关系对应见[值函数第 5.2 节](rv32imc-expr-value-functions.md#52-条件两侧)。

**命题 P1（互补方向）。** 对固定的 \(t_a,t_b\) 和任一解释补全 \((\nu,\theta)\)，Taken 与 NotTaken 的比较条件恰有一个为真。

**证明。** 两源项在该解释下具有确定值，两个条件的真值分别为 \(b\) 与 \(\neg b\)。布尔值与其否定恰有一个为真。\(\square\)

此命题只划分本次条件，不证明完整路径可行，也不证明两个方向的目标均有效。

### 3.2 最外层返回

设返回规则已经识别最外层正常返回，并在局部 Expr 更新后取得返回项 \(t_w\)。该候选的局部观察为

\[
\boxed{\mathcal P_i=\{\operatorname{ret}(\operatorname{solve}(t_w))\}.}
\]

普通节点记录执行前状态，Exit 记录返回步骤完成后的状态及此观察。程序内部返回与最外层正常返回须由控制规则区分；未知跳转不能直接产生返回观察。若返回项未定义，则该步骤无成功结果，不能生成空观察后宣称正常返回。

### 3.3 其他局部效果

未选取观察的算术赋值、普通传值及跳转可以取 \(\mathcal P_i=\varnothing\)。已绑定的 helper 调用按第 6 节生成调用观察与返回 Expr；普通访问和其他外部调用仍须独立定义。空局部观察仅表示所用规则未增加观察，不证明没有副作用，也不证明访问或调用满足全部有效性条件。

## 4. 累积与状态更新

### 4.1 结构并集

对第 1 节的观察域，合并定义为

\[
\boxed{\operatorname{mergePredicate}(\mathcal P,\mathcal P_i)
=\mathcal P\cup\mathcal P_i.}
\]

同一观察重复出现时只保留一次，补关系不因相互矛盾而删除。返回与 helper 观察也采用同一规则。不同次 helper 调用具有不同事件身份，因此类型与参数相同也不会被去重；重复合并同一次调用的观察仍只保留一次。

局部状态更新因此为

\[
\boxed{\sigma'=
\bigl(\operatorname{updateExpr}(\mathcal E,\mathcal E_i),
\mathcal P\cup\mathcal P_i\bigr).}
\]

不同分支候选分别从同一个输入状态更新；它们的观察集合不在汇合位置自动合并。Expr 按关系键覆写，Predicate 按结构累积，这两种操作具有不同含义。

**命题 P2（有限性与累积性质）。** 若 \(\mathcal P,\mathcal Q,\mathcal R\) 有限，则它们的合并仍有限，且

\[
\begin{gathered}
\mathcal P\subseteq\mathcal P\cup\mathcal Q,
\qquad \mathcal P\cup\varnothing=\mathcal P,
\qquad \mathcal P\cup\mathcal P=\mathcal P,\\
\mathcal P\cup\mathcal Q=\mathcal Q\cup\mathcal P,
\qquad (\mathcal P\cup\mathcal Q)\cup\mathcal R
=\mathcal P\cup(\mathcal Q\cup\mathcal R).
\end{gathered}
\]

**证明。** 合并元素来自两个有限集合。对任一观察 \(p\)，其属于合并结果当且仅当属于任一输入集合；逐式展开成员关系即可得到包含、单位元、幂等、交换与结合性质。\(\square\)

这些结论针对有限集合，不规定任何顺序表示的排列相等，也不证明完整指令更新可交换。

### 4.2 已取得的源项不随寄存器覆写改变

**命题 P3（源项固定）。** 若观察已由源项构成，则之后覆写取得这些项的寄存器不会改变此观察及其在同一 \((\nu,\theta)\) 下的解释。此结论也适用于 helper 调用时取得的参数项。

**证明。** 观察包含的是构造时取得的有限项，不是查询当前寄存器的操作。状态更新只替换 Expr 键并向观察集合加入元素，不修改旧项。其结构以及固定赋值下的解释因此保持不变。\(\square\)

这不保证两次读取同一寄存器得到相同的条件；两次检查可以取得不同项。

### 4.3 累积不等于可行性求解

为区分观察与路径可行性，可定义比较分量的路径公式

\[
\Phi_{\mathcal P}(\nu,\theta)
=\bigwedge_{\operatorname{cmp}(\bowtie,t_a,t_b)\in\mathcal P}
\left[\!\left[\operatorname{cmp}(\bowtie,t_a,t_b)\right]\!\right]_{\nu,\theta}.
\]

空合取为真；返回与 helper 调用观察不出现在此合取中。在给定允许的解释补全集合下，若存在 \((\nu,\theta)\) 使 \(\Phi_{\mathcal P}\) 为真，则称该比较分量可满足。

**命题 P4（同源互补条件不可同时满足）。** 若 \(\mathcal P\) 包含 \(\operatorname{cmp}(\bowtie,t_a,t_b)\) 及 \(\operatorname{cmp}(\overline{\bowtie},t_a,t_b)\)，则其比较分量不可满足。

**证明。** 由命题 P1，合取包含 \(b\land\neg b\)，在任一允许的解释下均为假。\(\square\)

合并规则仍接受这样的集合；不可满足性的数学结论不等于展开规则已经检测并删除该路径。不同检查时刻若源项不同，也不能只凭关系符号互补就套用命题 P4。

## 5. 示例与历史顺序

设执行前 \(r_{32}=V_{32}(\xi)\)，并选择无符号小于 10 的方向。令 \(v=V_{32}(\xi)\)，得到

\[
p_1=\operatorname{cmp}(<_u,v,C_{32}(10)).
\]

随后赋值 \(r_{32}\leftarrow\operatorname{ADD}_{32}^{\star}(v,C_{32}(1))\)，记新项为 \(t\)。再次检查同一寄存器并选择大于等于 10 的方向，再以该寄存器最外层返回，最终观察为

\[
\mathcal P=\{p_1,\operatorname{cmp}(\ge_u,t,C_{32}(10)),\operatorname{ret}(t)\}.
\]

第一个观察仍比较 \(v\)，第二个比较 \(t\)。例如 \(\nu(\xi)=9\) 时，两次条件均成立，返回值为 10；它们不是同源互补条件。

最终集合本身不保存事件顺序。没有事件身份的比较与返回观察重复产生时，集合不发生变化，不能仅由相邻集合差恢复重复事件。第 6 节的 helper 观察带有唯一调用身份，可以区分调用次数；调用顺序仍由执行路径及逐次快照表达。访问顺序或逐次输出还须定义相应事件与观察序列。

## 6. helper 调用 Predicate 与返回 Expr

### 6.1 helper 类型与参数寄存器

本节采用 32 位分派约定：\(a_0=\mathrm{Real}_{32}(10)\) 保存 helper 编号，\(a_j=\mathrm{Real}_{32}(10+j)\)（\(1\le j\le5\)）保存附加参数，返回寄存器为 \(r_{\mathrm{ret}}=a_0\)。这是指定调用约定，不将原生 eBPF 的参数位置与此约定混同。

类型集合 \(H\) 由以下七个带名称的类型组成。编号函数 \(\operatorname{id}:H\to\mathbb B_{32}\) 与参数个数 \(n:H\to\mathbb N\) 定义为：

- `BPF_FUNC_MAP_LOOKUP_ELEM`：编号 1，参数 \((a_1,a_2)\)，\(n=2\)。
- `BPF_FUNC_MAP_UPDATE_ELEM`：编号 2，参数 \((a_1,a_2,a_3,a_4)\)，\(n=4\)。
- `BPF_FUNC_MAP_DELETE_ELEM`：编号 3，参数 \((a_1,a_2)\)，\(n=2\)。
- `BPF_FUNC_KTIME_GET_NS`：编号 5，无附加参数，\(n=0\)。
- `BPF_FUNC_TRACE_PRINTK`：编号 6，参数 \((a_1,a_2,a_3,a_4,a_5)\)，\(n=5\)。
- `BPF_FUNC_CSUM_DIFF`：编号 28，参数 \((a_1,a_2,a_3,a_4,a_5)\)，\(n=5\)。
- `BPF_FUNC_XDP_ADJUST_TAIL`：编号 65，参数 \((a_1,a_2)\)，\(n=2\)。

这里的参数个数不包含编号寄存器 \(a_0\)。时钟类型也必须读取 \(a_0\)，但不要求 \(a_1,\ldots,a_5\) 已定义。

为保留确定未知编号的兜底结果，\(H\) 另含 \(\operatorname{unsupported}(k)\)，其中 \(k\in\mathbb B_{32}\setminus\{1,2,3,5,6,28,65\}\)，规定其编号为 \(k\)、\(n=0\)。它不是七种已支持 helper 的额外契约。

### 6.2 从调用前关系生成观察

对有效的 \(E_g\)，定义部分源项取得操作

\[
\operatorname{arg}_{32}(E_g,r)=t
\iff r\in\mathrm{Reg}_{\mathrm{Real},32}
\ \land\ (r=t)\in E_g
\ \land\ t\in\mathrm{Term}_{32}.
\]

要求对应完整等式唯一。只有低位关系或不等式不满足这个要求；Stack、Map、Packet 标记也不能替代所要求的真实参数寄存器。参数项可以是符号项，不要求数值可求。

设当前指令已被绑定为 helper 分派调用。令 \(\varepsilon\) 为本次动态调用的唯一身份：不同调用步骤取不同身份，循环中再次执行同一指令位置也不复用旧身份。同一候选的观察及结果项使用同一个 \(\varepsilon\)。定义

\[
\mathrm{Helper}_{32}
=\bigsqcup_{h\in H}
\bigl(\mathcal I_{\mathrm{call}}\times\{h\}\times\mathrm{Term}_{32}^{n(h)}\bigr).
\]

从调用前同一快照取得 \(t_0=\operatorname{arg}_{32}(E_g,a_0)\)，并要求

\[
D_{32}(\operatorname{solve}(t_0))=\operatorname{id}(h).
\]

再逐一取得 \(t_j=\operatorname{solve}(\operatorname{arg}_{32}(E_g,a_j))\)，\(1\le j\le n(h)\)。成功时

\[
\boxed{
\operatorname{makeHelperPredicate}(\varepsilon,E_g)
=p=\operatorname{helper}(\varepsilon,h,(t_1,\ldots,t_{n(h)})),
\qquad \mathcal P_i=\{p\}.
}
\]

编号未知、所需等式缺失或位宽不符时，这条构造规则无定义；不能仅生成一个空参数的调用观察。未被该类型使用的参数不参与校验。七种类型以外的确定编号采用独立的未支持类型观察，无附加参数，其返回投影为 \(C_{32}(2^{32}-1)\)；该兜底不提供相应 helper 的调用契约。

这一校验只保证类型已确定、参数齐备且项位宽正确。它不证明参数地址可访问、Map 对象存在、键有效或调用成功；这些条件属于资源绑定及具体 helper 契约。

### 6.3 观察解释与结果接口

调用观察解释为事件记录，而不是布尔条件：

\[
\left[\!\left[\operatorname{helper}(\varepsilon,h,\vec t)\right]\!\right]_{\nu,\theta}
=\bigl(\mathsf{helper},\varepsilon,h,
\left[\!\left[\vec t\right]\!\right]_{\nu,\theta}\bigr),
\]

其中向量解释逐项进行。事件身份区分具体调用，\(h\) 记录 helper 类型，参数项记录调用前取得的值。

从 Predicate 生成 Expr 的数学接口分为类型投影、参数投影、结果项与返回赋值：

\[
\begin{aligned}
\operatorname{helperKind}(p)&=h,\\
\operatorname{helperArgs}(p)&=\vec t,\\
\operatorname{helperResult}_{32}(p)&=\operatorname{solve}(F_{\varepsilon,h}(C_{32}(\operatorname{id}(h)),\vec t)),\\
\operatorname{helperExpr}(p)&=\{r_{\mathrm{ret}}=\operatorname{helperResult}_{32}(p)\}
\cup\operatorname{helperMapExpr}(p).
\end{aligned}
\]

\(F_{\varepsilon,h}\) 是带调用身份的未解释形式运算符，项签名为 \(\mathrm{Term}_{32}^{1+n(h)}\to\mathrm{Term}_{32}\)，数值解释的签名为 \(\mathbb B_{32}^{1+n(h)}\to\mathbb B_{32}\)。它的第一个实参是已确定类型的编号常元，因此即使 \(n(h)=0\) 也不需要零元运算符；这不增加待读取的参数寄存器。结果由解释补全 \(\theta\) 提供数值含义，部分求值仍返回未知。不同事件即使类型与实参相同，也不要求结果相同。

每种 helper 可以分别细化 \(F_{\varepsilon,h}\) 的结果契约；在未给定契约时，不用常元零、调用前的 \(a_0\) 或其他参数替代结果。checksum 的返回投影取结果低 16 位，其他已支持类型保留完整 32 位结果。Map lookup 的附加接口定义为

\[
\operatorname{helperMapExpr}(p)=
\begin{cases}
\{m_{\varepsilon,0}=R_{32}^{\varepsilon}(r_{\mathrm{ret}})\},&h=\mathrm{MAP\_LOOKUP},\\
\varnothing,&\text{其他类型}.
\end{cases}
\]

其中左侧是 \([0,4)\) 区间的虚拟 Map 标记，右侧是本次返回时刻的真实寄存器变元。该变元的赋值由本次返回结果契约约束。此接口及后续访问边界见[寄存器文档第 5.2 节](registers.md#52-map-lookup-的返回位置与虚拟寄存器)。

本次 helper 的寄存器值投影只写 \(r_{\mathrm{ret}}\)。调用指令自身的链接 Expr 另由控制规则产生，并与此更新组合。这个范围不构成对资源内容或调用约定下其他机器寄存器的完整保持证明；Map update/delete、包长度变化及其他外部副作用仍须另给契约。

### 6.4 局部性质

**命题 H1（生成的唯一性与参数齐备）。** 在有效 \(E_g\)、既定调用绑定及固定 \(\varepsilon\) 下，成功生成的 helper Predicate 唯一，并具有恰好 \(n(h)\) 个 32 位参数项。

**证明。** 编号求值确定，七个编号互异，因此 \(h\) 唯一。完整等式的键唯一使每个参数项唯一，solve 是确定的；构造逐一取得所需的 \(n(h)\) 个项。\(\square\)

**命题 H2（返回更新的有限性与位宽）。** 对生成成功的 \(p\)，\(\operatorname{helperExpr}(p)\) 含真实返回键，lookup 另含一个虚拟 Map 键；集合有限、位宽匹配且键唯一，覆写不改变其余 Expr 键。

**证明。** 结果项与真实寄存器变元均为 32 位。lookup 的两个左侧分别属于 Real 与 Map，键互异；其他类型只有返回键。覆写结论由共同数学的定义得到。此处仅证明所选值投影的结构性质。\(\square\)

**命题 H3（动态调用区分）。** 若 \(\varepsilon\ne\varepsilon'\)，则 \(\operatorname{helper}(\varepsilon,h,\vec t)\ne\operatorname{helper}(\varepsilon',h,\vec t)\)，两观察在集合合并后均保留。

**证明。** 事件身份是结构相等的一部分，两观察不同；并集包含两者。\(\square\)

## 7. 后续定义与证明边界

现有规则明确了比较、返回与 helper 调用观察、参数校验、返回 Expr、源项固定和结构累积。以下问题仍须另行设计或证明：

- Stack、Map 与 Packet 访问应观察哪些资源身份、范围、权限与对齐条件，以及访问有效性如何与分类前提联系。
- 各 helper 的具体返回契约、资源变化与调用安全性，以及七种类型以外的外部调用观察。
- 64 位比较观察的类型与解释，以及 eBPF 条件向观察的对应。
- 在累积条件下判定可行性、检测矛盾及约束推理的可靠性。
- 除 helper 调用身份以外的事件身份、完整轨迹和顺序观察规则。
- 跨指令集的输入、返回位宽与其他观察对应。

扩展观察域时，须同时给出新观察的解释、生成规则与合并规则。第 4 节的集合性质不能代替这些定义；现有局部命题也不能直接推出资源访问正确或完整行为等价。
