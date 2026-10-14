# MapDelete谓词

## 类型定义

MapDelete 的元素记作 \(\operatorname{mapDelete}(\varepsilon,t_m,\vec k)\)，其类型为：

\[
\mathrm{MapDelete}:=\bigsqcup_{w\in\{32,64\},\,L_k\in\mathbb N}
\bigl(\mathcal I_{\mathrm{call}}\times\mathrm{Term}_{w}
\times\mathrm{BytesTerm}_w(L_k)\bigr).
\]

其中 \(\varepsilon\) 为调用身份，\(t_m\in\mathrm{Term}_{w}\) 为 Map 参数项，\(\vec k\in\mathrm{BytesTerm}_w(L_k)\) 为冻结键；\(w\) 是[调用约定](Helper谓词.md#类型定义)的载体宽度，\(L_k\) 来自已知 Map 布局。长度标签由数组长度确定，位宽标签由 Map 项及字节项确定。删除调用的完整字节事件按查询调用对称取得，不含值数组或 flags。

MapDelete 解释为删除调用事件：

\[
\llbracket\operatorname{mapDelete}(\varepsilon,t_m,\vec k)
\rrbracket_{\nu,\theta}
:=(\mathsf{mapDelete},\varepsilon,\llbracket t_m\rrbracket_{\nu,\theta},
\llbracket\vec k\rrbracket_{\nu,\theta}).
\]

其中 \(\mathsf{mapDelete}\) 为删除调用标签，\(\varepsilon\) 为调用身份，Map 参数项解释为 \(w\) 位值，冻结键解释为 \(L_k\) 个字节；\(\nu,\theta\) 是[Helper 解释](Helper谓词.md#解释参数)的赋值与补全。返回项由[共同结果规则](Helper谓词.md#生成的-expr)确定；删除成功及资源变化的语义契约仍为[义务 H-D](#数学性质)。

## 触发逻辑

### RV32IMC

满足[RV32 分派器触发条件](Helper谓词.md#rv32imc)且编号确定为 3 时，选择删除类别。前两个 ABI 参数分别提供 Map 参数项与键缓冲区地址项；参数位置与载体见[共同约定](Helper谓词.md#类型定义)。

### eBPF

满足[原生 eBPF 调用触发条件](Helper谓词.md#ebpf)且立即数编号为 3 时，选择删除类别。前两个 ABI 参数的意义与 RV32 相同；取源及返回效果按[共同规则](Helper谓词.md#生成条件)处理。

## 生成条件

[共同参数取源](Helper谓词.md#生成条件)成功后，令 \(t_m=t_1\)、\(L_k=L_k(t_m;\mathcal L)\)，其中 \(\mathcal L,w\) 是共同规则给定的布局与载体。完整事件要求 \(t_m\) 唯一指向的 Map 对象布局给出键字节长度 \(L_k\)，且键地址项 \(t_2\) 指向的对象满足该长度的读取条件。\(\vec k=\operatorname{readBytes}(E_g,t_2,L_k,\mathcal L,w)\) 有定义时，生成 \(\operatorname{mapDelete}(\varepsilon,t_m,\vec k)\)。键的冻结与后续覆写行为见[调用时的字节读取](Helper谓词.md#调用时的字节读取)。

### 错误类型

MapDelete 的 Map 参数、布局与键读取采用[MapLookup 错误类型](MapLookup谓词.md#错误类型)，发生其中任一错误时完整字节事件的精化无定义；其与 ABI 调用成功的边界见[共同生成条件](Helper谓词.md#生成条件)。

## 数学性质

定义域内的 MapDelete 生成唯一：其 Map 参数所指对象、布局与键读取使用 MapLookup 的唯一性论证，删除类别标签确定。保存键的保持性见[命题 H4](Helper谓词.md#数学性质)。调用与实际参数的一致性仍为[义务 H-B](Helper谓词.md#数学性质)。

**证明义务 H-D（删除结果与资源变化）。** 既有 helper 语义尚未给出 delete 成功契约及对已有 Map 关系的完整修改规则；须在其归属处建立这些契约并证明与真实调用一致。

## 相关文档

- [Helper 生成的 Expr](Helper谓词.md#生成的-expr)：删除结果与尚未完成的资源变化契约。
- [寄存器标记的身份](../寄存器定义.md#寄存器定义)：Map 对象、条目及单元身份。
- [Helper 共同约定](Helper谓词.md#类型定义)：分派参数位置、调用身份、字节项数组及解释参数。
