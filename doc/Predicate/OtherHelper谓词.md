# OtherHelper谓词

## 类型定义

令 \(H_{\mathrm{other}}\) 为 \(H\) 中除 `BPF_FUNC_MAP_LOOKUP_ELEM`、`BPF_FUNC_MAP_UPDATE_ELEM`、`BPF_FUNC_MAP_DELETE_ELEM` 以外的类型，包含未支持类型。OtherHelper 保存统一载体宽度的 ABI 参数向量：

\[
\mathrm{OtherHelper}:=
\bigcup_{h\in H_{\mathrm{other}},\,w\in\{32,64\}}
\bigl(\mathcal I_{\mathrm{call}}\times\{h\}\times
\mathrm{Term}_{w}^{n(h)}\bigr).
\]

其中 \(\mathcal I_{\mathrm{call}}\) 为动态调用身份集合，\(\{h\}\) 为 helper 类型的单元素集合，\(\times\) 为笛卡尔积，\(\mathrm{Term}_{w}^{n(h)}\) 为长度恰好是 \(n(h)\) 的同宽有限符号项向量集合。\(w\) 由[调用约定](Helper谓词.md#类型定义)确定；空向量不额外携带位宽标签。

令 \(\vec t=(t_1,\ldots,t_{n(h)})\) 为参数向量，其中每个 \(t_j\in\mathrm{Term}_w\)；参数个数为零时向量为空。OtherHelper 的元素记作 \(\operatorname{helper}(\varepsilon,h,\vec t)\)，其中 \(h\in H_{\mathrm{other}}\)；其调用身份、类型及参数向量均参与结构相等。

调用身份、helper 类型及参数位置见[Helper 共同约定](Helper谓词.md#类型定义)，\(\nu,\theta\) 见[解释参数](Helper谓词.md#解释参数)；\(\mathsf{helper}\) 为事件的类别标签。

OtherHelper 解释为事件记录：

\[
\left[\!\left[\operatorname{helper}(\varepsilon,h,\vec t)\right]\!\right]_{\nu,\theta}
:=\bigl(\mathsf{helper},\varepsilon,h,
\left[\!\left[\vec t\right]\!\right]_{\nu,\theta}\bigr),
\]

其中向量解释逐项进行。事件身份区分具体调用，\(h\in H_{\mathrm{other}}\) 记录 helper 类型，参数项记录调用前取得的值。

## 触发逻辑

### RV32IMC

满足[共同调用触发条件](Helper谓词.md#触发逻辑)且分派类型属于 \(H_{\mathrm{other}}\) 时，选择 OtherHelper。

### eBPF

满足[原生 eBPF 调用触发条件](Helper谓词.md#ebpf)且立即数选择的类型属于 \(H_{\mathrm{other}}\) 时，选择 OtherHelper。参数数量与取源按[共同规则](Helper谓词.md#生成条件)处理；时钟及未支持类型均为空参数向量。

## 生成条件

[共同参数取源](Helper谓词.md#生成条件)成功且 \(h\in H_{\mathrm{other}}\) 时，生成 \(\operatorname{helper}(\varepsilon,h,\vec t)\)。局部观察集合按[共享生成器](Helper谓词.md#生成条件)生成。

### 错误类型

适用[共同错误与拒绝规则](Helper谓词.md#错误类型)。

## 数学性质

**命题 H1（OtherHelper 生成的唯一性与参数齐备）。** 在有效 \(E_g\)、既定调用约定、固定调用指令及固定 \(\varepsilon\) 下，若所选类型属于 \(H_{\mathrm{other}}\)，则成功生成的 OtherHelper 谓词唯一，并具有恰好 \(n(h)\) 个所选载体宽度 \(w\) 的参数项。

**证明。** 已命名编号互异，未支持类型由其确定编号给出，因此 \(h\) 唯一。完整等式的键唯一使每个参数项唯一，solve 是确定的；构造逐一取得所需的 \(n(h)\) 个项。\(\square\)

动态调用区分见[命题 H3](Helper谓词.md#数学性质)。

### 跨架构其他调用

OtherHelper 的规范结果保存 helper 编号及规范参数列表，规则见[观察规范化](跨架构谓词.md#观察规范化)。M6 的调用身份擦除由 `cross_helper_event` 证明，参数中的常元、包裹和外部结果依[项规范化](跨架构谓词.md#项规范化)处理。原始调用与规范结果分别使用各自的相等判据，其联系受[判断范围](跨架构谓词.md#判断范围)约束。

## 相关文档

- [Helper 生成的 Expr](Helper谓词.md#生成的-expr)
- [检查源项与访问对象](../NodeInference/step.md#检查源项与访问对象)
- [指令参数与规则定义域](../NodeInference/step.md#局部规则的合法域)
- [solve 的化简与求值](../Expr/Term/solve.md#solve-的化简与求值)
- [Term与项解释](../Expr/Term/Term.md#term)
- [Helper 共同约定与生成器](Helper谓词.md)：分派参数、调用身份及共享生成条件。
