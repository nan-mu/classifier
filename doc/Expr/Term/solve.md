# solve 的化简与求值

## 设计目标

每条指令规则从[输入补充后的同一写入前关系](../Expr.md#未记录虚拟寄存器的取源)取得源项，经符号提升构造右侧项。\(\operatorname{solve}_w\) 把右侧项化成更简的等价形，使三类后续运算可算且形状统一：

- **判定**：比较 Expr 的两端需要取得确定数值，见[部分判定](../Expr.md#部分判定)。
- **识别**：栈槽与包偏移的绑定要求项呈根与常数偏移的合成形状。该识别对恒等包裹透明：由 \(ID_w(a)=a\)（见[共同数值函数](数值函数.md#算术)）可知，\(ID_w(t)\) 与 \(t\) 给出相同的根与常数偏移。
- **去重**：比较约束按结构相等去重，同一语义形状应收敛到同一种写法。

\(\operatorname{solve}_w:\mathrm{Term}_w\to\mathrm{Term}_w\) 位宽保持，在有限项上全定义；它不引入新变元，不承担路径约束求解。

化简由下列规则确定，规则给出唯一结果。零化与单位元规则（R5、R6）以及化简的最终深度属于当前约定，调整时重证幂等性与解释保持性即可。

## 变元出现集合

\(FV(t)\) 是项 t 的变元出现集合。
\[
FV(C_w(c))=\varnothing,
\qquad FV(V_w(\xi))=\{V_w(\xi)\},
\qquad
FV(f(t_1,\ldots,t_n))=\bigcup_{j=1}^{n}FV(t_j).
\]
真实寄存器变元满足 \(FV(R_w^{\varepsilon}(r))=\{R_w^{\varepsilon}(r)\}\)。

**引理 2（有限性）。** 每个项的 \(FV\) 都是有限集合。

**证明。** 对项结构归纳。常元对应空集，变元对应单元素集合；有限个子项的有限集合之并仍有限。\(\square\)

## 闭项求值

\(FV(t)=\varnothing\) 的项称为闭项。在[假设 A](Term.md#叶子与运算符)的纯数值子域上，\(\operatorname{eval}_w\) 将 w 位闭项求值为同位宽数值。
\[
\operatorname{eval}_w:
\{t\in\mathrm{Term}_w:FV(t)=\varnothing\}\to\mathbb B_w,
\]
常元 \(C_w(c)\) 的求值结果为 c。
\[
\operatorname{eval}_w(C_w(c))=c,
\]
应用项的求值结果由 \(\widehat f\) 作用于各输入位宽 \(w_j\) 的子项结果得到。
\[
\operatorname{eval}_w(f(t_1,\ldots,t_n))
=\widehat f\bigl(\operatorname{eval}_{w_1}(t_1),\ldots,
\operatorname{eval}_{w_n}(t_n)\bigr).
\]
**命题 3（闭项求值良定义）。** 每个纯数值闭项具有唯一的同位宽求值结果。

**证明。** 闭项中不出现变元，故其叶子均为常元。对项结构归纳，子项的结果唯一且满足输入位宽；\(\widehat f\) 的确定性、全定义性与输出签名给出唯一的同位宽结果。项结构有限，递归求值结束。\(\square\)

含未解释资源或调用运算的项采用[部分求值](#部分求值与未解释运算)，其闭项未必具有确定数值。

## 化简规则

设 \(t\in\mathrm{Term}_w\)。令 \(\operatorname{norm}_w\) 按 R2 至 R6 处理当前根及这些规则暴露的加法脊，其他子树保持原项；先消去遇到的 R5、R6 形状，再收集加项并按 R4 重建。化简先对输入作 R1，规范化后再对整个结果作一次 R1：

\[
\operatorname{solve}_w(t):=
\operatorname{foldClosed}_w\bigl(\operatorname{norm}_w(\operatorname{foldClosed}_w(t))\bigr).
\]

最后一次整项折叠可以求值由零化或单位元消去后暴露出的闭结果，仍不在开放树内任意递归折叠闭子项。规则内的常数属于 \(\mathbb B_w\)，\(D_w\) 见[部分求值与未解释运算](#部分求值与未解释运算)。

**R1 闭项折叠。** 中间函数 \(\operatorname{foldClosed}_w:\mathrm{Term}_w\to\mathrm{Term}_w\) 只检查整项。含变元时保持整项，随后仍可应用 R2 至 R6；其中的闭子项不单独折叠。
\[
\boxed{
\operatorname{foldClosed}_w(t):=
\begin{cases}
C_w(a),&FV(t)=\varnothing\ \land\ D_w(t)=a\in\mathbb B_w,\\
t,&FV(t)\ne\varnothing\ \lor\ D_w(t)=\bot.
\end{cases}}
\]

**R2 加法脊归并。** 沿相同位宽的 ADD 节点与右侧为常元的 SUB 节点收集加项；其余子树作为完整非恒等加项保留，不递归化简其内部闭子项。常数项相加后按 \(M_w\) 归一化。
\[
\mathrm{ADD}\bigl(\mathrm{ADD}(V_{32}(\xi),C_{32}(16)),C_{32}(4)\bigr)
\longrightarrow
\mathrm{ADD}\bigl(V_{32}(\xi),C_{32}(20)\bigr).
\]

**R3 减法转加法。** \(\mathrm{SUB}(t,C_w(c))\) 化为 \(\mathrm{ADD}(t,C_w(M_w(2^w-c)))\)。右侧非常元的减法不展开为加法；结构相同的两端仍由 R5 处理。

**R4 规范次序。** 加法脊内的非恒等加项按[项的全序](#项的全序)排列，常数项置于末位，再按左结合重写为二元 ADD。于是 \(\mathrm{ADD}(C_{32}(4),V_{32}(\xi))\) 与 \(\mathrm{ADD}(V_{32}(\xi),C_{32}(4))\) 化为同一形状。

**R5 零化。** 两端结构相同的相消项化为零常元。
\[
\mathrm{SUB}(t,t)\longrightarrow C_w(0),
\qquad
\mathrm{XOR}(t,t)\longrightarrow C_w(0).
\]

**R6 单位元消去。** 常元为单位元时消去该项。
\[
\begin{aligned}
\mathrm{ADD}(t,C_w(0))&\longrightarrow t, &
\mathrm{OR}(t,C_w(0))&\longrightarrow t, &
\mathrm{XOR}(t,C_w(0))&\longrightarrow t,\\
\mathrm{SHL}(t,C_w(0))&\longrightarrow t, &
\mathrm{LSHR}(t,C_w(0))&\longrightarrow t, &
\mathrm{ASHR}(t,C_w(0))&\longrightarrow t,\\
\mathrm{AND}(t,C_w(2^w-1))&\longrightarrow t, &
\mathrm{MULLO}(t,C_w(1))&\longrightarrow t. &&
\end{aligned}
\]

**R7 满域投影消去。** 位域取整段、低位视图宽度与项位宽相同、零扩展或符号扩展的输入输出位宽相同时，投影可消去。该条为可选规则。

未列出形状的应用项保留原样，包括未解释运算（包输入与外部调用结果）与含变元的位运算，例如 \(\mathrm{AND}(V_{32}(\xi),C_{32}(2^{32}-16))\) 保持形式。化简不使用分配律，不合并不同变元的项，不做掩码合并，也不使用位级恒等式。多目标取源与应用顺序见[多目标更新与同一执行前关系](../Expr.md#多目标更新与同一来源)。

## 项的全序

R4 需要一个在有限项上确定且可判定的全序 \(\preceq\)，依次比较：

1. 位宽：32 位在 64 位之前。
2. 同位宽时按构造：常元、输入变元、寄存器变元、应用项。同位宽常元按其非负数值排列。
3. 输入变元按名称的自然数序。真实寄存器变元依次比较调用身份、寄存器类别与静态标记；类别序为 Real、Stack、Map、Packet、Context，合法真实寄存器变元只使用 Real。
4. 应用项先比较运算标签，再比较该运算全部原始语义参数，最后按实参列表作字典序递归比较，空列表在非空列表之前。参数使用自然数序，位宽参数使用其位数。

运算标签的递增顺序为 ADD、SUB、MULLO、UDIV、UREM、SDIV、SREM、MULH、MULHU、MULHSU、SELECTEQ、NEG、ID、AND、OR、XOR、SHL、LSHR、ASHR、LTU、LTS、LOW、EXTRACT、ZEXT、SEXT、BSWAP、externalResult、inputByte、mergeLow。参数按各运算签名顺序比较，除法包含位宽与除零结果，外部结果包含事件及 lane；排序保留原始参数，不作跨架构擦除。

该全序只依赖项的结构，与解释 \(\nu,\theta\) 无关。

## 符号提升

\(f^\star\) 是形式运算符 f 的符号提升，将应用项交给 \(\operatorname{solve}_w\)。
\[
f^\star(t_1,\ldots,t_n)
=\operatorname{solve}_w(f(t_1,\ldots,t_n)).
\]
已命名数值函数 \(G\) 的符号提升为 \(G^\star\)，例如 ADD 与 \(\mathrm{ADD}^\star\)。

## 部分求值与未解释运算

\(D_w(t)\in\mathbb B_w\cup\{\bot\}\) 是部分数值求值，\(\bot\) 表示未取得确定数值。求值不使用 \(\nu\) 或 \(\theta\)。

- 常元返回其值。
- 普通输入变元与真实寄存器变元均返回 \(\bot\)。
- 纯数值运算在全部实参已求值时应用其数值函数，否则返回 \(\bot\)。
- 未解释运算返回 \(\bot\)。

R1 以 \(D_w\) 为判据：只有闭项且 \(D_w(t)\) 取得数值时才折为常元，其余输入交给后续规则。在纯数值子域上这与[闭项求值](#闭项求值)的 \(\operatorname{eval}_w\) 一致。

## 幂等性

**命题 5。** 对任意项 \(t\in\mathrm{Term}_w\)，化简满足幂等性。
\[
\operatorname{solve}_w(\operatorname{solve}_w(t))
=\operatorname{solve}_w(t).
\]
**证明。** 加法脊内常数已合并并置于末位，非恒等项的次序与结合方向固定，规则暴露范围内的相消项和单位元项已消去。若规范化结果闭合且可求值，最后一次整项 R1 将其折成规范常元；否则第二次 R1 仍取得相同的未定结果。未暴露的子树保持原项，第二次规范化只会再次收集同一有序加项及同一模常数，再次重建得到原结果。故第二次 solve 不变。若启用可选 R7，还须证明投影消去后的结果满足同一规范形条件。\(\square\)

Lean 的 `ClassifierExpr.solve_idempotent` 对任意原始 `Term` 证明命题 5，`ClassifierExpr.solve_width` 证明位宽保持，`ClassifierExpr.solve_support` 证明输出变元属于输入变元集合。这三个定理不要求输入良构；坏签名输入由 `solve` 原样保留。良构输入的良构保持由 `foldClosed_wellFormed`、`normalizeAlgebra_wellFormed` 和末次 `foldClosed_wellFormed` 组合得到，`normalizeAlgebra_idempotent` 的前提为输入 `wellFormed=true`。这些定理位于 [Term.lean](../../../ClassifierExpr/Term.lean)，均已通过 Lean kernel。

## 解释保持性

**引理 6。** 对纯数值闭项 t，\(\left[\!\left[ t\right]\!\right]_\nu=\operatorname{eval}_w(t)\)，且结果与 \(\nu\) 无关。

**证明。** 对闭项结构归纳。常元情形直接成立；应用情形对每个子项使用归纳假设，再代入同一个 \(\widehat f\)。\(\square\)

**命题 7。** 对任意良构项 \(t\in\mathrm{Term}_w\)、同位宽变元赋值 \(\nu\) 与满足[完整解释补全](Term.md#未解释运算的解释补全)的 \(\theta\)，化简保持项的解释。
\[
\left[\!\left[\operatorname{solve}_w(t)\right]\!\right]_{\nu,\theta}
=\left[\!\left[ t\right]\!\right]_{\nu,\theta}.
\]
**证明。** R1 由[闭项求值](#闭项求值)与常元解释得到，未取得数值时该步骤保持原项。R2 与 R4 由 \(\mathrm{ADD}\) 在 \(\mathbb B_w\) 上的交换律与结合律、以及 \(M_w\) 的幂等性得到。R3 由 \(M_w(a-c)=M_w(a+M_w(2^w-c))\) 得到。R5 的两个相同子项在完整补全下均有同一个值 \(a\)，再由 \(\mathrm{SUB}(a,a)=0\) 与 \(\mathrm{XOR}(a,a)=0\) 得到。R6 由各自的数值定义得到。未列出形状的应用项保持原项。\(\square\)

若外部解释允许缺失值，命题 7 的等式一般不成立。令 \(e\) 为缺少 \(\theta\) 解释的外部结果项，则严格部分解释对 \(\mathrm{SUB}(e,e)\) 返回 `none`，R5 化简后 \(C_w(0)\) 的解释为 `some 0`。因此，完整补全上的数值等式与任意部分 `Option` 求值结果相等是两个不同命题。

命题 7 的 Lean 对应为 [SolvePreservation.lean](../../../ClassifierExpr/SolvePreservation.lean) 导出的 `ClassifierExpr.solve_interpret`：对任意 `ν : Var → Nat`、`θ : ExternalInterpretation` 和 `t : Term`，在 `θ.Total` 与 `t.wellFormed=true` 下，`interpretTerm ν θ (solve t) = interpretTerm ν θ t`。它覆盖开放项及完整 R1 至 R6，已通过 Lean kernel。R2 至 R6 的一般保持定理为同一文件中的 `ClassifierExpr.normalizeAlgebra_interpret`，使用相同前提；R1 的 `ClassifierExpr.foldClosed_interpret` 对任意部分环境已成立。文件内 `SolvePreservation` 命名空间维护辅助证明，两个保持定理实际导出在 `ClassifierExpr` 命名空间。

Lean 的 `θ.Total` 只要求外部函数处处返回某个自然数，节点解释再按载体取模；它比数学完整补全的字节值域条件弱，见 [Term 的解释补全](Term.md#未解释运算的解释补全)。数值代数引理见 [NumericProofs.lean](../../../ClassifierExpr/NumericProofs.lean) 的 `ADD_assoc`、`ADD_comm`、`SUB_eq_ADD_NEG`、`SUB_self`、`XOR_self` 及相应单位元定理。可选 R7 不在上述已证规则范围内。化简不声称完备：语义等价而规范形不同的项仍视为不同项。

