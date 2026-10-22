# MapUpdate观察

## 类型定义

MapUpdate 的元素记作 \(\operatorname{mapUpdate}(\varepsilon,t_m,\vec k,\vec v,t_f)\)，其类型为：

\[
\mathrm{MapUpdate}:=\bigsqcup_{w\in\{32,64\},\,(L_k,L_v)\in\mathbb N^2}
\bigl(\mathcal I_{\mathrm{call}}\times\mathrm{Term}_{w}
\times\mathrm{BytesTerm}_w(L_k)\times\mathrm{BytesTerm}_w(L_v)
\times\mathrm{Term}_{w}\bigr).
\]

其中 \(\varepsilon\) 为调用身份，\(t_m\in\mathrm{Term}_{w}\) 为 Map 参数项，\(\vec k\in\mathrm{BytesTerm}_w(L_k)\) 与 \(\vec v\in\mathrm{BytesTerm}_w(L_v)\) 分别为冻结键、值字节数组，\(t_f\in\mathrm{Term}_{w}\) 为调用时提交的 flags 项。\(w\) 是[调用约定](Helper谓词.md#类型定义)的载体宽度，\(L_k,L_v\) 来自同一已知 Map 布局；长度标签由数组长度确定，位宽标签由各项确定。

MapUpdate 解释为更新调用事件：

\[
\llbracket\operatorname{mapUpdate}(\varepsilon,t_m,\vec k,\vec v,t_f)
\rrbracket_{\nu,\theta}
:=(\mathsf{mapUpdate},\varepsilon,\llbracket t_m\rrbracket_{\nu,\theta},
\llbracket\vec k\rrbracket_{\nu,\theta},
\llbracket\vec v\rrbracket_{\nu,\theta},
\llbracket t_f\rrbracket_{\nu,\theta}).
\]

其中 \(\mathsf{mapUpdate}\) 为更新调用标签，\(\varepsilon\) 为调用身份，Map 与 flags 项解释为 \(w\) 位值，键和值数组分别解释为 \(L_k,L_v\) 个字节；\(\nu,\theta\) 是[Helper 解释](Helper谓词.md#解释参数)的赋值与补全。此事件描述调用时提交的参数，本身不证明更新成功。返回项由[共同结果规则](Helper谓词.md#生成的-expression)确定；更新成功及资源修改的语义契约仍为[义务 H-U](#数学性质)。

## 触发逻辑

### RV32IMC

满足[RV32 分派器触发条件](Helper谓词.md#rv32imc)且编号确定为 2 时，选择更新类别。四个 ABI 参数依次提供 Map 参数项、键缓冲区地址项、值缓冲区地址项及 flags 项；参数位置与载体见[共同约定](Helper谓词.md#类型定义)。

### eBPF

满足[原生 eBPF 调用触发条件](Helper谓词.md#ebpf)且立即数编号为 2 时，选择更新类别。四个 ABI 参数的意义与 RV32 相同；取源及返回效果按[共同规则](Helper谓词.md#生成条件)处理。

## 生成条件

[共同参数取源](Helper谓词.md#生成条件)成功后，令 \(t_m=t_1\)、\(t_f=t_4\)，其中 \(\mathcal L,w\) 是共同规则给定的布局与载体。完整事件要求 \(t_m\) 唯一指向的 Map 对象布局给出键、值字节长度 \(L_k(t_m;\mathcal L)\)、\(L_v(t_m;\mathcal L)\)，且地址项 \(t_2,t_3\) 指向的对象分别满足所需长度的读取条件。从同一 \(\bar{E}_g\) 分别读取：

\[
(\vec k,\vec v):=
\bigl(\operatorname{readBytes}(\bar{E}_g,t_2,L_k(t_m;\mathcal L),\mathcal L,w),
\operatorname{readBytes}(\bar{E}_g,t_3,L_v(t_m;\mathcal L),\mathcal L,w)\bigr).
\]

其中 \(\vec k\in\mathrm{BytesTerm}_w(L_k(t_m;\mathcal L))\)、\(\vec v\in\mathrm{BytesTerm}_w(L_v(t_m;\mathcal L))\) 为完整键和值数据；\(t_2,t_3\) 为调用前的缓冲区地址项。两个读取均有定义时生成完整事件 \(\operatorname{mapUpdate}(\varepsilon,t_m,\vec k,\vec v,t_f)\)。冻结语义见[调用时的字节读取](Helper谓词.md#调用时的字节读取)。

### 错误类型

Map 参数与键读取的精化错误沿用[MapLookup 错误类型](MapLookup谓词.md#错误类型)。以下值读取错误也使完整字节事件无定义；精化与 ABI 调用成功的边界见[共同生成条件](Helper谓词.md#生成条件)：

- 调用时 Map 对象布局的值长度不能确定。
- 值缓冲区的内存读取依据不足。
- 任一所需值字节项缺失或不能满足字节项类型。

## 数学性质

定义域内的 MapUpdate 生成唯一：MapLookup 的唯一性论证分别用于键和值的读取，完整参数等式唯一确定 \(t_m,t_f\)。保存键和值的保持性见[命题 H4](Helper谓词.md#数学性质)。调用与实际参数的一致性仍为[义务 H-B](Helper谓词.md#数学性质)。

**证明义务 H-U（更新结果与资源变化）。** 既有 helper 语义尚未给出 update 成功契约及对已有 Map 关系的完整修改规则；须在其归属处建立这些契约并证明与真实调用一致。

## 相关文档

- [Helper 生成的 Expression](Helper谓词.md#生成的-expression)：返回结果与尚未完成的资源变化契约。
- [虚拟映射读写](../Expr/寄存器/虚拟映射.md#虚拟映射读写)：架构内部 Map 内容关系。
- [Helper 共同约定](Helper谓词.md#类型定义)：分派参数位置、调用身份、字节项数组及解释参数。
