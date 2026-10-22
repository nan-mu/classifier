# MapLookup观察

## 类型定义

MapLookup 的元素记作 \(\operatorname{mapLookup}(\varepsilon,t_m,\vec k)\)，其类型为：

\[
\mathrm{MapLookup}:=\bigsqcup_{w\in\{32,64\},\,L_k\in\mathbb N}
\bigl(\mathcal I_{\mathrm{call}}\times\mathrm{Term}_{w}
\times\mathrm{BytesTerm}_w(L_k)\bigr).
\]

其中 \(\varepsilon\in\mathcal I_{\mathrm{call}}\) 为调用身份，\(t_m\in\mathrm{Term}_{w}\) 为调用时的 Map 参数项，\(\vec k\in\mathrm{BytesTerm}_w(L_k)\) 为冻结键；\(w\) 是[调用约定](Helper谓词.md#类型定义)的载体宽度，\(L_k\) 是已知 Map 布局的键字节长度。长度标签由数组长度确定，位宽标签由 Map 项及字节项确定。Map 对象身份使用[寄存器标记的身份](../寄存器定义.md#寄存器定义)，调用参数唯一指向该对象是完整字节事件的生成条件。

MapLookup 解释为查询调用事件：

\[
\llbracket\operatorname{mapLookup}(\varepsilon,t_m,\vec k)
\rrbracket_{\nu,\theta}
:=(\mathsf{mapLookup},\varepsilon,\llbracket t_m\rrbracket_{\nu,\theta},
\llbracket\vec k\rrbracket_{\nu,\theta}).
\]

其中 \(\mathsf{mapLookup}\) 为查询事件标签，\(\varepsilon\) 区分动态调用，Map 参数项解释为 \(w\) 位值，冻结键按[字节数组解释](Helper谓词.md#字节项数组)解释为 \(L_k\) 个字节；\(\nu,\theta\) 是[Helper 解释](Helper谓词.md#解释参数)的赋值与补全。

## 触发逻辑

### RV32IMC

满足[RV32 分派器触发条件](Helper谓词.md#rv32imc)且编号确定为 1 时，选择查询类别。前两个 ABI 参数分别提供 Map 参数项与键缓冲区地址项；参数位置与载体见[共同约定](Helper谓词.md#类型定义)。

### eBPF

满足[原生 eBPF 调用触发条件](Helper谓词.md#ebpf)且立即数编号为 1 时，选择查询类别。前两个 ABI 参数分别提供 Map 参数项与键缓冲区地址项；取源、可选冻结键及返回关联按[共同规则](Helper谓词.md#生成条件)处理。

## 生成条件

[共同参数取源](Helper谓词.md#生成条件)成功后，令 \(t_m=t_1\)，\(L_k=L_k(t_m;\mathcal L)\)，其中 \(\mathcal L,w\) 是共同规则给定的布局与载体。调用时 \(t_m\) 唯一指向的 Map 对象布局须给出键字节长度 \(L_k\)，且键地址项 \(t_2\) 指向的对象须满足该长度的读取条件。\(\vec k=\operatorname{readBytes}(\bar{E}_g,t_2,L_k,\mathcal L,w)\) 有定义时，生成完整事件 \(\operatorname{mapLookup}(\varepsilon,t_m,\vec k)\)。键的冻结与后续覆写行为见[调用时的字节读取](Helper谓词.md#调用时的字节读取)。调用的返回效果按[lookup 返回关联](Helper谓词.md#生成的-expression)处理。

### 错误类型

除[共同错误](Helper谓词.md#错误类型)外，下列任一情形使完整字节事件的精化无定义，其与 ABI 调用成功的边界见[共同生成条件](Helper谓词.md#生成条件)：

- Map 参数不能唯一确定所指向的 Map 对象。
- 调用时 Map 对象布局的键长度不能确定。
- 键缓冲区的内存读取依据不足。
- 任一所需字节项缺失或不能满足字节项类型。

## 数学性质

固定共同输入后，定义域内的 MapLookup 生成唯一：Map 参数唯一指向的对象布局确定 \(L_k\)，键地址项所指缓冲区的布局与访问规则及完整源等式确定每个字节投影，既有 solve 是确定的，因此 \(\vec k\) 和构造结果唯一。保存键的保持性见[命题 H4](Helper谓词.md#数学性质)。读取与真实查询参数的一致性仍为[义务 H-B](Helper谓词.md#数学性质)。

## 相关文档

- [lookup 返回关联](Helper谓词.md#生成的-expression)：返回项与 Map 关联。
- [寄存器标记的身份](../寄存器定义.md#寄存器定义)：Map 对象、条目及单元身份。
- [Helper 共同约定](Helper谓词.md#类型定义)：分派参数位置、调用身份、字节项数组及解释参数。
