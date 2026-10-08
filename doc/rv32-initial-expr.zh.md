# RV32 初态 Expr

本文定义 XDP 镜像第一条 RV32 指令执行前的 Expr 有限集合。Reg、Term、常元、变元、符号运算及覆写操作均沿用 `common-math.md`。调用输入满足已有的有效性约定；上下文采用标准 `xdp_md` 布局。

## 1. 入口值

以下各项属于 \(\mathrm{Term}_{32}\)：

| 项 | 含义 |
|---|---|
| \(t_{\mathrm{ctx}}\) | 上下文对象的起始地址 |
| \(t_{\mathrm{data}}\) | 输入包的起始地址 |
| \(t_{\mathrm{len}}\) | 输入包的字节长度 |
| \(t_{\mathrm{sp}}\) | 镜像入口的栈指针值 |
| \(t_{\mathrm{return}}\) | 镜像返回包装器的位置，即汇编标签 `1:` 的地址 |
| \(t_{\mathrm{frame}}\) | 包装器保存区 `XDP_FRAME` 的起始地址 |
| \(t_{\mathrm{entry}}\) | 包装器调用镜像时使用的 `entry` 值 |

已知的入口值使用常元 \(C_{32}(c)\)；符号输入使用固定名称的变元 \(V_{32}(\xi)\)。变元表示本次入口的固定值，不引用执行过程中变化的寄存器。相同来源复用同一个项。

包的结束地址项定义为

\[
t_{\mathrm{end}}
=\mathrm{ADD}_{32}^{\star}
\bigl(t_{\mathrm{data}},t_{\mathrm{len}}\bigr).
\]

令 \(\iota_{\mathrm{wifi}}\in\mathbb B_{32}\) 为固定常量 `IFINDEX_WIFI` 的值，使用 \(C_{32}(\iota_{\mathrm{wifi}})\) 表示接口编号。它是定义的常量参数。

## 2. 真实寄存器初态

寄存器编号和 ABI 别名使用同一标识。例如 `sp` 与 `x2` 指向同一个 \(\mathrm{Real}_{32}\) 元素。令

\[
R_s=\{\mathrm{s0},\ldots,\mathrm{s11}\}.
\]

对 \(r\in R_s\cup\{\mathrm{gp},\mathrm{tp}\}\)，令 \(t_r\in\mathrm{Term}_{32}\) 表示调用环境提供的入口值。值未知时使用各自的固定输入变元。

将下表的每一项写成完整等式 \((\mathrm{Real}_{32}(r),=,t)\)，这些等式组成 \(\mathcal E_{\mathrm{base}}\)。

| 寄存器 \(r\) | 右侧项 \(t\) |
|---|---|
| `zero` | \(C_{32}(0)\) |
| `ra` | \(t_{\mathrm{return}}\) |
| `sp` | \(t_{\mathrm{sp}}\) |
| `t0` | \(t_{\mathrm{sp}}\) |
| `t1` | \(t_{\mathrm{return}}\) |
| `t2` | \(t_{\mathrm{frame}}\) |
| `a0` | \(t_{\mathrm{ctx}}\) |
| \(r\in R_s\cup\{\mathrm{gp},\mathrm{tp}\}\) | \(t_r\) |

这些关系取自已经执行完的调用包装器。因此，`t0` 与 `sp` 共用入口 SP 项，`t1` 与 `ra` 共用返回地址项。镜像自身的序言尚未执行，不提前将 `s0` 设为 `sp`。

令 \(r_{\mathrm{entry}}\) 为包装器中承载 `entry` 操作数的寄存器；它满足该调用的寄存器约束。调用写入 `ra`，其他承载 `entry` 的寄存器保留其值。真实寄存器初态为

\[
\mathcal E_{\mathrm{real},0}=
\begin{cases}
\mathcal E_{\mathrm{base}},
&r_{\mathrm{entry}}=\mathrm{ra},\\[2pt]
\operatorname{updateExpr}\!\left(
\mathcal E_{\mathrm{base}},
\{(\mathrm{Real}_{32}(r_{\mathrm{entry}}),=,t_{\mathrm{entry}})\}
\right),
&r_{\mathrm{entry}}\ne\mathrm{ra}.
\end{cases}
\]

这里使用已有的覆写规则：若 `entry` 占用保存寄存器，对应入口等式改为 \(t_{\mathrm{entry}}\)，不保留两个完整定义。未被上述构造定义的真实寄存器不加入初态；读取缺失源项时仍按共同规则拒绝。

## 3. XDP 上下文初态

标准 `xdp_md` 包含六个连续的 32 位字段。其初值由给出的 `XdpMd::from_buf` 确定：

| 索引 \(j\) | 字段 | 字节偏移 \(4j\) | 初值项 \(u_j\) |
|---|---|---|---|
| 0 | `data` | 0 | \(t_{\mathrm{data}}\) |
| 1 | `data_end` | 4 | \(t_{\mathrm{end}}\) |
| 2 | `data_meta` | 8 | \(C_{32}(0)\) |
| 3 | `ingress_ifindex` | 12 | \(C_{32}(\iota_{\mathrm{wifi}})\) |
| 4 | `rx_queue_index` | 16 | \(C_{32}(0)\) |
| 5 | `egress_ifindex` | 20 | \(C_{32}(0)\) |

令 \(\alpha_{\mathrm{ctx},j}\in\mathcal I_{\mathrm{Stack}}\) 标识调用栈中上下文对象的第 j 个 32 位槽；六个标识互不相同。它们是已有虚拟栈寄存器的标识，不增加 Reg 类型。入口绑定将地址项

\[
\mathrm{ADD}_{32}^{\star}
\bigl(t_{\mathrm{ctx}},C_{32}(4j)\bigr)
\]

对应的字段访问解释为 \(\mathrm{SW}(\alpha_{\mathrm{ctx},j})\) 的访问。该绑定由既有 Predicate 语义承载；Expr 只保存槽的值关系。

上下文初态为

\[
\boxed{
\mathcal E_{\mathrm{ctx},0}
=\left\{
\bigl(\mathrm{SW}(\alpha_{\mathrm{ctx},j}),=,u_j\bigr)
:j\in\{0,\ldots,5\}
\right\}.
}
\]

表中的 \(u_j\) 是定义这些等式的书写方式，不另存为一份字段状态。镜像修改字段时，覆写相应 Expr；入口项 \(t_{\mathrm{data}},t_{\mathrm{len}}\) 仍表示原始输入。

## 4. 最终初态

\[
\boxed{
\mathcal E_0
=\mathcal E_{\mathrm{real},0}
\cup\mathcal E_{\mathrm{ctx},0}
\in\mathscr F(\mathrm{Expr}).
}
\]

两部分分别使用 Real 与 Stack 标记，不互相覆盖。每个已定义标记有一个完整的 32 位值等式。镜像尚未初始化的局部栈槽不补零；包和 Map 的访问继续按共同语义处理。

入口节点直接使用这个 \(\mathcal E_0\) 和已有的入口 Predicate 集合。节点与路径定义保持不变。上述参数、表格和集合构造足以确定 Lean4 中的初态构造函数，无需增加第三份运行状态。

依据：给出的调用包装器与 `XdpMd::from_buf`；上下文字段布局采用 [Linux UAPI 的 `struct xdp_md`](https://github.com/torvalds/linux/blob/master/include/uapi/linux/bpf.h)。
