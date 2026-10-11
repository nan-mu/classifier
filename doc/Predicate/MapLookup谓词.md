# MapLookup谓词

## 类型定义

MapLookup 的元素记作 \(\operatorname{mapLookup}(\varepsilon,t_m,\vec k)\)，其类型为：

\[
\mathrm{MapLookup}:=\bigsqcup_{L_k\in\mathbb N}
\bigl(\mathcal I_{\mathrm{call}}\times\mathrm{Term}_{32}
\times\mathrm{BytesTerm}(L_k)\bigr).
\]

其中 \(\varepsilon\in\mathcal I_{\mathrm{call}}\) 为调用身份，\(t_m\in\mathrm{Term}_{32}\) 为调用时的 Map 参数项，\(\vec k\in\mathrm{BytesTerm}(L_k)\) 为冻结键；\(L_k\) 是已知 Map 布局的键字节长度。长度标签由数组长度确定。Map 对象身份使用[资源身份](../寄存器定义.md)，其唯一绑定是生成条件。

MapLookup 解释为查询调用事件：

\[
\llbracket\operatorname{mapLookup}(\varepsilon,t_m,\vec k)
\rrbracket_{\nu,\theta}
:=(\mathsf{mapLookup},\varepsilon,\llbracket t_m\rrbracket_{\nu,\theta},
\llbracket\vec k\rrbracket_{\nu,\theta}).
\]

其中 \(\mathsf{mapLookup}\) 为查询事件标签，\(\varepsilon\) 区分动态调用，Map 参数项解释为 32 位值，冻结键按[字节数组解释](Helper谓词.md#字节项数组)解释为 \(L_k\) 个字节；\(\nu,\theta\) 是[Helper 解释](Helper谓词.md#解释参数)的赋值与补全。

## 触发逻辑

### RV32IMC

满足[共同调用触发条件](Helper谓词.md#触发逻辑)且分派编号确定为 1 时，选择 MapLookup。调用参数位置仍为 \((a_1,a_2)\)，分别提供 Map 参数项与键缓冲区地址项。

### eBPF

适用[共同 eBPF 定义域](Helper谓词.md#ebpf)。

## 生成条件

[共同参数取源](Helper谓词.md#生成条件)成功后，令 \(t_m=t_1\)，\(L_k=L_k(\Gamma,t_m)\)。长度有定义且 \(\vec k=\operatorname{readBytes}(\Gamma,E_g,t_2,L_k)\) 有定义时，生成 \(\operatorname{mapLookup}(\varepsilon,t_m,\vec k)\)。键的冻结与后续覆写行为见[调用时的字节读取](Helper谓词.md#调用时的字节读取)。查询结果及关联仍按[既有 lookup 语义](../Expr/待处理.md#lookup-返回关联)处理。

### 错误类型

除[共同错误](Helper谓词.md#错误类型)外，下列任一情形使构造无定义，并按既有规则拒绝本次处理、保留当前图：

- Map 参数不能唯一绑定到 Map 对象。
- 已绑定 Map 的键长度不能确定。
- 键缓冲区的内存读取依据不足。
- 任一所需字节项缺失或不能满足字节项类型。

## 数学性质

固定共同输入后，定义域内的 MapLookup 生成唯一：唯一对象布局确定 \(L_k\)，唯一资源归约及完整源等式确定每个字节投影，既有 solve 是确定的，因此 \(\vec k\) 和构造结果唯一。保存键的保持性见[命题 H4](Helper谓词.md#数学性质)。读取与真实查询参数的一致性仍为[义务 H-B](Helper谓词.md#数学性质)。

## 相关文档

- [lookup 返回关联](../Expr/待处理.md#lookup-返回关联)：返回项与 Map 关联。
- [资源身份](../寄存器定义.md)：Map 对象、条目及单元身份。
- [Helper 共同约定](Helper谓词.md#类型定义)：分派参数位置、调用身份、字节项数组及解释参数。
