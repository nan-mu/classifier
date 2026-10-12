# Term

## 叶子与运算符

采用[寄存器定义](../../寄存器定义.md)的位宽集合 \(W\)。对 \(w\in W\)，\(\Xi_w\) 是变元名称集合；\(\mathrm{Var}_w\) 是变元集合。
\[
\mathrm{Var}_w=\{V_w(\xi):\xi\in\Xi_w\}
\sqcup\{R_w^{\varepsilon}(r):r\in\mathrm{Reg}_{\mathrm{Real},w},\ \varepsilon\in\mathcal I_{\mathrm{call}}\}.
\]
常元表示确定值。\(V_w(\xi)\) 表示固定的符号输入。\(R_w^{\varepsilon}(r)\) 表示指定调用返回时刻由真实寄存器承载的值；\(\mathcal I_{\mathrm{call}}\) 是动态调用身份集合，见[lookup 关联规则](../../Predicate/Helper谓词.md#生成的-expr)。两类变元不交，后者的身份包括事件及完整寄存器标记。同名但位宽不同的变元是不同元素。普通输入变元不查询后续可变的寄存器。未定义寄存器不自动对应一个新变元。

对 \(n\in\mathbb N_{>0}\) 及 \(w_1,\ldots,w_n,w\in W\)，\(f\) 是形式运算符，\(\widehat f\) 是对应的数值解释。
\[
f\in\mathrm{Op}_{(w_1,\ldots,w_n)\to w},
\qquad
\widehat f:\prod_{j=1}^{n}\mathbb B_{w_j}\to\mathbb B_w.
\]
**假设 A（纯数值解释）。** 每个 \(\widehat f\) 都是确定的全函数。指令立即数、运算宽度或固定字节序可作为运算符参数。未给定的外部资源或调用结果不满足这一假设，不能仅凭常元实参被解释成确定返回值。

## 有限项与类型

\(\mathrm{Term}_w\) 是常元 \(C_w(c)\)、变元 \(V_w(\xi),R_w^{\varepsilon}(r)\) 与运算符应用生成的有限项集合。
\[
t_w::=C_w(c)\mid V_w(\xi)\mid R_w^{\varepsilon}(r)\mid f(t_{w_1},\ldots,t_{w_n}).
\]
函数应用必须与输入、输出位宽签名一致。常元、变元是叶子，应用记录运算结构。8 位或 16 位的辅助数值步骤可合成为输出为 32 位或 64 位的运算符，无需引入新的 Term 位宽。

## 项的解释

\(\nu_w:\mathrm{Var}_w\to\mathbb B_w\) 是变元赋值族，\(\left[\!\left[t\right]\!\right]_\nu\) 是项 t 在该赋值下的解释。
\[
\left[\!\left[ C_w(c)\right]\!\right]_\nu=c,
\qquad
\left[\!\left[ V_w(\xi)\right]\!\right]_\nu=\nu_w(V_w(\xi)),
\]
应用项 \(f(t_1,\ldots,t_n)\) 的解释由数值函数 \(\widehat f\) 作用于各子项的解释得到。
\[
\left[\!\left[ f(t_1,\ldots,t_n)\right]\!\right]_\nu
=\widehat f(\left[\!\left[ t_1\right]\!\right]_\nu,\ldots,
\left[\!\left[ t_n\right]\!\right]_\nu).
\]
真实寄存器变元 \(R_w^{\varepsilon}(r)\) 的解释同样取自 \(\nu_w\)。
\[
\left[\!\left[R_w^{\varepsilon}(r)\right]\!\right]_\nu
=\nu_w(R_w^{\varepsilon}(r)).
\]
该赋值由相应调用结果契约约束，不取后续可变的寄存器赋值 \(\rho_w(r)\)。

## 未解释运算的解释补全

含包输入或外部结果等未解释运算的项还须给定解释补全 \(\theta\)，为这些运算指定同位宽的值函数。项解释为 \(\left[\!\left[t\right]\!\right]_{\nu,\theta}\)。应用项仍按上述递归规则解释，只将未解释运算的数值函数取自 \(\theta\)。

关系与观察的解释以固定的 \((\nu,\theta)\) 为前提。补全的存在不保证访问或调用有效。部分求值见[部分求值与未解释运算](solve.md#部分求值与未解释运算)。

