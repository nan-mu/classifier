# MapUpdate谓词

## 类型定义

MapUpdate 的元素记作 \(\operatorname{mapUpdate}(\varepsilon,t_m,\vec k,\vec v,t_f)\)，其类型为：

\[
\mathrm{MapUpdate}:=\bigsqcup_{(L_k,L_v)\in\mathbb N^2}
\bigl(\mathcal I_{\mathrm{call}}\times\mathrm{Term}_{32}
\times\mathrm{BytesTerm}(L_k)\times\mathrm{BytesTerm}(L_v)
\times\mathrm{Term}_{32}\bigr).
\]

其中 \(\varepsilon\) 为调用身份，\(t_m\) 为 32 位 Map 参数项，\(\vec k\) 与 \(\vec v\) 分别为长度 \(L_k,L_v\) 的冻结键、值字节数组，\(t_f\in\mathrm{Term}_{32}\) 为调用时提交的 flags 项。\(L_k,L_v\) 来自同一已知 Map 布局，长度标签由数组长度确定。

MapUpdate 解释为更新调用事件：

\[
\llbracket\operatorname{mapUpdate}(\varepsilon,t_m,\vec k,\vec v,t_f)
\rrbracket_{\nu,\theta}
:=(\mathsf{mapUpdate},\varepsilon,\llbracket t_m\rrbracket_{\nu,\theta},
\llbracket\vec k\rrbracket_{\nu,\theta},
\llbracket\vec v\rrbracket_{\nu,\theta},
\llbracket t_f\rrbracket_{\nu,\theta}).
\]

其中 \(\mathsf{mapUpdate}\) 为更新调用标签，\(\varepsilon\) 为调用身份，Map 与 flags 项解释为 32 位值，键和值数组分别解释为 \(L_k,L_v\) 个字节；\(\nu,\theta\) 是[Helper 解释](Helper谓词.md#解释参数)的赋值与补全。此事件描述调用时提交的参数，本身不证明更新成功。成功结果及修改如何反映到 Expr 关系仍归[既有 helper 语义](Helper谓词.md#生成的-expr)及其未完成契约。

## 触发逻辑

### RV32IMC

满足[共同调用触发条件](Helper谓词.md#触发逻辑)且分派编号确定为 2 时，选择 MapUpdate。调用参数位置仍为 \((a_1,a_2,a_3,a_4)\)，分别提供 Map 参数项、键缓冲区地址项、值缓冲区地址项及 flags 项。

### eBPF

适用[共同 eBPF 定义域](Helper谓词.md#ebpf)。

## 生成条件

[共同参数取源](Helper谓词.md#生成条件)成功后，令 \(t_m=t_1\)、\(t_f=t_4\)。调用时 \(t_m\) 唯一指向的 Map 对象布局须给出键、值字节长度 \(L_k(t_m)\)、\(L_v(t_m)\)，且地址项 \(t_2,t_3\) 指向的对象分别满足所需长度的读取条件。生成时从同一 \(E_g\) 分别读取：

\[
(\vec k,\vec v):=
\bigl(\operatorname{readBytes}(E_g,t_2,L_k(t_m)),
\operatorname{readBytes}(E_g,t_3,L_v(t_m))\bigr).
\]

其中 \(\vec k\in\mathrm{BytesTerm}(L_k(t_m))\)、\(\vec v\in\mathrm{BytesTerm}(L_v(t_m))\) 为完整键和值数据；\(t_2,t_3\) 为调用前的缓冲区地址项。两个读取均有定义时生成 \(\operatorname{mapUpdate}(\varepsilon,t_m,\vec k,\vec v,t_f)\)。冻结语义见[调用时的字节读取](Helper谓词.md#调用时的字节读取)。

### 错误类型

Map 参数与键读取的错误沿用[MapLookup 错误类型](MapLookup谓词.md#错误类型)。另有以下值读取错误时，构造无定义，按[共同拒绝规则](Helper谓词.md#错误类型)处理：

- 调用时 Map 对象布局的值长度不能确定。
- 值缓冲区的内存读取依据不足。
- 任一所需值字节项缺失或不能满足字节项类型。

## 数学性质

定义域内的 MapUpdate 生成唯一：MapLookup 的唯一性论证分别用于键和值的读取，完整参数等式唯一确定 \(t_m,t_f\)。保存键和值的保持性见[命题 H4](Helper谓词.md#数学性质)。调用与实际参数的一致性仍为[义务 H-B](Helper谓词.md#数学性质)。

**证明义务 H-U（更新结果与资源变化）。** 既有 helper 语义尚未给出 update 成功契约及对已有 Map 关系的完整修改规则；须在其归属处建立这些契约并证明与真实调用一致。

## 相关文档

- [Helper 生成的 Expr](Helper谓词.md#生成的-expr)：返回结果与尚未完成的资源变化契约。
- [虚拟映射读写](../Expr/寄存器/虚拟映射.md#虚拟映射读写)：架构内部 Map 内容关系。
- [Helper 共同约定](Helper谓词.md#类型定义)：分派参数位置、调用身份、字节项数组及解释参数。
