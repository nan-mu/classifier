# SMT 与路径谓词设计

本目录规定机器码标注、路径谓词、QF_BV 目标生成和认证变换之间的边界。它与
`docs/Theorem/` 同级，但职责不同：

- `docs/Theorem/` 描述 T0--T5 各阶段的功能；
- `docs/SMT/` 描述这些阶段共同使用的谓词 IR 和证明接口；
- `rocq/` 承载最终的形式化定义与定理。

这些文件同时记录目标设计和明确标注的已实现边界。当前 `prefixgen/pathgen`
使用结构化 Prefix；后续 T1--T5 仍有历史字符串实现。QF_BV 已实现通用
寄存器/assert 子集，以及 fixture 专用、显式契约约束的 XDP 逻辑区域解释器；
其余效果必须返回 `Unsupported`，不能另建一套宽松语义。

## 固定处理顺序

```text
对象文件/可执行映像
  -> 提取并切分机器码
  -> 为机器指令填充基础 Prefix
  -> T0 展开路径并添加 assert
  -> T1 将物理栈地址归一为 wsN
  -> T1.3 认证并否定不可达路径
  -> T2--T5 添加或删除阶段谓词
  -> 目标生成器把 Prefix 转为 QF_BV
  -> CoqQFBV 检查匹配边的反例公式
  -> 路径族 assert 行为双射证据
```

机器码提取结果固定为：

```rust
type BpfRawProgram = Vec<u64>;
type Rv32RawProgram = Vec<U32OrU16>;
```

Rocq 中对应为 `seq RV64` 和 `seq U32OrU16`。填充基础谓词后，两种 ISA 都采用
同一个外形：

```text
Insn = (machine, Prefix)
Path = sequence Insn
```

`machine` 保存原始编码，`Prefix` 是挂在该编码上的有序不可变谓词序列。

## 不变量

- 原始机器码在 T0--T5 中不得被覆盖或重新编码。
- Predicate 创建后不可修改；阶段变换只能添加或删除完整 Predicate。
- 所有语义立即数都是定宽 bit-vector，不使用无界自然数或整数。
- BPF 与 RV32 的物理寄存器不直接比较；两边的栈统一归一为 `wsN`。
- lookup 来源寄存器必须精确，是否为空由路径 assert 单独表达。
- 目标生成器只读 Prefix，不重新解码机器码或解析自由格式文本。
- 只有认证后端确认的 `UNSAT` 才能支持等价边、删除谓词或否定路径。
- 不支持的指令、别名或内存语义必须返回 `Unsupported`/`Unknown`，不能弱化。

## 第一版范围

第一版覆盖无量词定宽寄存器运算、规范栈槽、路径 assert，以及具有显式契约的
packet、map 和 helper 状态。第一版不覆盖一般循环、并发、volatile、未知
helper 或无法界定的任意内存。

## 文档索引

- [机器码预处理与基础 Prefix](preprocess.md)
- [谓词与 Insn IR](predicate-ir.md)
- [证明义务与求解器后端](solver-backend.md)
- [T1.3 不可达路径剪枝](t1.3.md)
