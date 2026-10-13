# 路径合并FFI

## 共同接口与实现边界

create 的入口假设与 step 的指令规则按目标架构给定，具体入口项见[create](create.md)。数学 step、history、merge 与运行时驱动的 merge-step 使用共同的状态、位置和历史契约；指令的局部规则仍由各所属正文规定。产品 create/step 与预算展开归 RV32IMC，实现与研究限度见[语义范围与证据边界](#语义范围与证据边界)。

数学 step 的语义输入与[局部推理接口](step.md#输入)一致，为 \((\mathbf I,j,\sigma_g)\)：\(\mathbf I\) 是指令序列，\(j\) 是从 1 开始的当前指令序号，\(\sigma_g\) 是执行前状态。已解码指令实例及其位置、控制目标绑定须满足该接口的前提；程序编码数组、Meta 和额外身份参数属于具体产品的工程接口。状态组合的数学归属仍见[状态变换的组合](step.md#状态变换的组合)，history 的构造与良构域见[统一历史类型](History.md#逐步记录与统一类型)。

现有 [RV32IMC/Expand.lean](../../RV32IMC/Expand.lean) 的 `lean_rv32_expand_step` 接收程序编码数组、`metaJson`、`event`、`j` 以及 Expr、Predicate 字符串，并在 `RV32IMC.prepareAll` 中组合后继状态。该产品接口与上述数学 step 的局部增量契约仍有差异；导出名称与行为保持不变。程序解码、静态绑定和额外身份参数的处理不得据此成为数学 step 的输入。

共同 merge FFI 只比较已经取得的完整配置。外部运行时负责 step 推进、状态组合、历史保存及[合并步](分支合并处理.md#合并步merge-step)调度。

## 工程模块与迁移

U3 按职责拆分库、模块与命名空间，入口与构建目标一一对应：

- [ClassifierExpr.lean](../../ClassifierExpr.lean) / `ClassifierExpr`：共享表达式表示与操作，模块为 [Bits](../../ClassifierExpr/Bits.lean)、[Reg](../../ClassifierExpr/Reg.lean)、[Numeric](../../ClassifierExpr/Numeric.lean)、[Op](../../ClassifierExpr/Op.lean)、[Term](../../ClassifierExpr/Term.lean)、[Expr](../../ClassifierExpr/Expr.lean)、[Virtual](../../ClassifierExpr/Virtual.lean)、[Direction](../../ClassifierExpr/Direction.lean)、[Insn](../../ClassifierExpr/Insn.lean)、[Parse](../../ClassifierExpr/Parse.lean)、[Render](../../ClassifierExpr/Render.lean)、[Ffi](../../ClassifierExpr/Ffi.lean)。渲染仅依赖表达式对象，不导入路径模块。
- [PathMerge.lean](../../PathMerge.lean) / `PathMerge`：[Path](../../PathMerge/Path.lean) 维护位置、候选、节点、边与状态组合，[Merge](../../PathMerge/Merge.lean) 维护线协议精确配置比较。两者显式导入并使用 ClassifierExpr 类型。
- [RV32IMC.lean](../../RV32IMC.lean) / `RV32IMC`：[Initial](../../RV32IMC/Initial.lean)、[Expr](../../RV32IMC/Expr.lean)、[Expand](../../RV32IMC/Expand.lean) 分别承载产品入口、指令值规则与 create/step 导出；预算、工作队列与图快照驱动移入 [Budget](../../RV32IMC/Budget.lean)。RV32IMC 按所需对象导入 ClassifierExpr 与 PathMerge.Path，不以 PathMerge.Merge 作为聚合入口。
- [EBPF.lean](../../EBPF.lean) / `EBPF`：保留 [Insn](../../EBPF/Insn.lean)、[Encode](../../EBPF/Encode.lean)、[Expr](../../EBPF/Expr.lean)、[Initial](../../EBPF/Initial.lean) 与 [Step](../../EBPF/Step.lean) 的解码、表达式、入口及 `EBPF.ebpfStep` 语义。已有入口构造接收上下文与栈指针的 64 位常元或变元，将其分别绑定到 \(r_1\) 与 \(r_{10}\)，并取空谓词集合；未初始化寄存器没有入口等式。实现覆盖范围与研究限度见[语义范围与证据边界](#语义范围与证据边界)。

旧聚合库及其目录整体撤除，不保留兼容导入、命名空间别名或 umbrella；Demo 及其唯一 RV32 示例检查一并撤除。EBPF 的旧展开模块由 Step 替代，产品库入口按上述职责导入。

FFI 符号的迁移如下：

- `lean_expand_merge` 的 C 名称和 String ABI 保留，Lean 实现归 PathMerge，签名见[String 导出](#string-导出)。
- `lean_rv32_expand_create`、`lean_rv32_expand_step` 以及既有 RV32 C 名称保留；[RegisterFfi](../../RV32IMC/RegisterFfi.lean) 的 `lean_rv32_register_effects` 保留。
- ClassifierExpr.Ffi 的五个纯数值导出改为 `classifier_expr_add32`、`classifier_expr_sub32`、`classifier_expr_and32`、`classifier_expr_tq32`、`classifier_expr_divu32`，仅替换旧导出的前缀，参数、结果与行为的 ABI 保持不变。`lean_virtual_cell_access`、`lean_virtual_packet_access` 保留。

[lakefile.lean](../../lakefile.lean) 的 Lean 构建目标为 `ClassifierExpr`、`PathMerge`、`RV32IMC`、`EBPF`；显式构建命令为 `lake build ClassifierExpr PathMerge RV32IMC EBPF`。server 目标取得 ClassifierExpr、PathMerge、RV32IMC 的共享库 facet 后构建 Rust 服务。受保护的 tooling 绑定与链接顺序由 Cursor 适配；U3 切换后的服务证据须在重新链接后取得，见[U3 重新链接后的 live 复查](#u3-重新链接后的-live-复查)。

数学位置继续从 1 开始，Lean 的 PathMerge.Path 与 RV32IMC.Budget 继续使用从零开始的数组下标；此表示差异有意保持，线协议换算见[请求对象](#请求对象)。现有 `.audit/poscheck.py` 的源码清单仍指向迁移前路径，其缺失文件跳过行为不能检验新模块的位置表示；清单维护属于后续维护工作。

## String 导出

Lean 导出符号及签名为：

```lean
@[export lean_expand_merge]
def PathMerge.exportExpandMerge (requestJson : String) : String
```

实现归属 [PathMerge/Merge.lean](../../PathMerge/Merge.lean)，经 [PathMerge.lean](../../PathMerge.lean) 暴露。`PathMerge.ExactMerge.select (requestJson : String) : Except String (Nat × Nat)` 完成校验与选择，成功时依次给出 NotTaken 后缀入口引用和 Taken 节点引用。

`lean_expand_merge` 使用 Lean 运行时 ABI：输入为一个 Lean `String`，结果为携带 JSON 的 Lean `String`。这些字符串不直接作为 C 的空终止字符串传入。

调用是无状态的精确配置比较，不接收 `insns`、`metaJson`、程序长度或 `jb`，不解码指令、不建立程序绑定、不识别条件分支。它不调用 step，不管理预算、工作队列或历史，也不生成新的语义状态。状态解析复用 [ClassifierExpr/Parse.lean](../../ClassifierExpr/Parse.lean) 的 `ClassifierExpr.parseSemStateJson`。

## 请求对象

`requestJson` 是单个 JSON 对象。必填字段及表示如下：

```json
{
  "observationModel": "FiveClass",
  "requiredObservations": ["Helper", "Branch", "Return", "MapWrite", "PacketWrite"],
  "taken": {
    "id": 42,
    "loc": "3",
    "exprs": [],
    "predicates": []
  },
  "notTaken": [
    {
      "id": 17,
      "loc": "3",
      "exprs": [],
      "predicates": []
    }
  ]
}
```

该对象展示线协议字段，不提供分支来源或后缀覆盖证明。

- `observationModel` 接受 `"FiveClass"` 与既有 `"HelperOnly"`。`requiredObservations` 必填且为字符串数组；FiveClass 下只接受 `"Helper"`、`"Branch"`、`"Return"`、`"MapWrite"`、`"PacketWrite"`，HelperOnly 下仍只接受 `"Helper"`，空数组有效。未知模型或不在声明域内的要求均拒绝。HelperOnly 是旧调用方的声明标签，不是状态投影：任一标签下都解析、保留并比较全部五类已提供观察。声明所需类别不能证明调用方提供了该类全部应有观察。
- `taken` 为单个已到达配置；`notTaken` 为按调用方复用优先级排列的非空后缀入口配置数组。空候选数组以 `EmptyNotTaken` 拒绝。
- 每个配置的 `id` 是自然数形式的不透明运行时节点引用。同一请求中全部配置的 `id` 必须互异；它们不表示指令序号、地址或记录长度。
- `loc` 使用当前共同表示：普通位置为非负十进制整数的字符串，存储从零开始的指令数组下标，例如 `"3"` 对应数学文档中的第 4 条指令；正常结束为 `"exit"`。共同 merge 校验其表示并比较解析后的位置，不校验程序范围；运行时负责该位置属于共同程序的位置域。不同节点可以有相同 `loc`，重复到达仍由 `id` 区分。
- `exprs`、`predicates` 都是数组，表示该配置已施加全部局部更新后的全局状态。普通位置保存待执行指令的执行前状态，`"exit"` 保存最终状态。数学 step 的候选局部增量须先按既有规则组合。现有 step String 导出的后继状态行为见[实现边界](#共同接口与实现边界)。

### Expr 的表示

Expr 行沿用共享解析与渲染格式，例如：

```json
{"reg":"real32:10","rel":"eq","term":"v32:1"}
```

`reg`、`rel`、`term` 均为字符串，分别按 `parseReg`、`parseRel`、`parseTerm` 解析。缺少 `role` 时，完整 `eq` 行进入值绑定分量，其余关系进入约束分量。约束行可以显式给出 `"role":"constraint"`，其中包括 `eq` 约束；值绑定与 `eq` 约束保留不同角色，不能混同。其他显式 `role` 值拒绝。

共同状态检查包括：

- 共享寄存器表示须有效，位宽只支持 32 与 64；Packet 寄存器当前只支持 32 位。寄存器与右侧项的位宽须相同，值绑定须使用完整 `eq`。
- 值绑定键必须唯一，约束分量不得含结构重复项。重复值键或重复约束行是无效输入，不通过去重修复。
- 关系的低位宽度参数须大于零且不超过寄存器位宽。项检查递归覆盖全部子项：常元在位宽范围内，寄存器变元引用有效的真实寄存器，应用项满足运算符的参数个数、位宽和固定参数范围。

共同 merge 不施加入口寄存器赋值策略或 x0 求零检查，也不限制为某一目标架构的状态。共享 AST 当前的 `externalResult` 和 `inputByte` 应用仍限 32 位；这些表示限制由共同项检查保留，不构成目标指令的调用或内存语义验证。

### 共同 Predicate JSON

五类 Predicate 的共享线协议由 [ClassifierExpr.Insn](../../ClassifierExpr/Insn.lean)、[Parse](../../ClassifierExpr/Parse.lean) 与 [Render](../../ClassifierExpr/Render.lean)实现；数学构造及各类解释由[谓词定义](../Predicate/谓词定义.md#类型与结构相等)所链接的正文维护。

```json
{"kind":"helper","event":8,"helperId":5,"args":["v32:1"]}
{"kind":"branch","position":4,"dir":"taken","width":32,"cond":{"lhs":"v32:1","rel":"ltu","rhs":"10"}}
{"kind":"ret","width":64,"term":"v64:2"}
{"kind":"mapWrite","event":9,"mapWidth":64,"map":"v64:3","key":["1","v32:4"],"offset":0,"sourceWidth":32,"source":"v32:5"}
{"kind":"packetWrite","event":10,"packet":2,"offset":0,"width":32,"source":"v32:6"}
```

这些是五个独立 JSON 对象示例；`predicates` 数组可混合包含它们。`ret` 是 Return 的 wire 标签，`return`、`for`、`cmp` 等旧名或未知标签拒绝。Helper 的字段和既有项字符串保持原状。

- Helper：`event` 为自然数调用身份；`helperId` 为小于 `2^32` 的自然数；`args` 为默认按 32 位解析的项字符串数组，各参数必须为良构 Term32。共同 merge 不按编号检查目标专属参数个数或调用契约，空参数数组有效。
- Branch：`position` 是从 1 开始的自然数指令序号，必须大于零；与 `loc` 的零基字符串表示分别处理。`dir` 仅接受 `"taken"` 与 `"notTaken"`。`width` 指定两个条件项的相同载体位宽；`cond.lhs`、`cond.rhs` 为项字符串，`cond.rel` 为关系字符串，关系的比较宽度须在载体范围内。共享校验不验证程序上界、该位置是否确为条件分支或方向与机器指令的对应。
- Return：`width` 为完整返回项载体位宽，`term` 必须解析为该位宽的良构项。共同校验不识别最外层返回。
- MapWrite：`event` 为写入事件身份，`mapWidth`、`sourceWidth` 分别指定 Map 项与完整源项的载体位宽，`map`、`source` 为项字符串。`key` 是按顺序保存的 Term32 字符串数组，长度参与结构比较，常量键字节须小于 256；符号键项的字节取值、完整冻结来源和与对象布局匹配仍是语义义务。`offset` 为元素值内的自然数字节偏移。
- PacketWrite：`event` 为写入事件身份，`packet` 为自然数包资源身份，`offset` 为相对包起点的自然数字节偏移；`width` 为完整源项的载体位宽，`source` 为项字符串。一次多字节存储仍只产生一个事件，实际访问宽度另由指令和记录提供。

各位宽字段仅接受 JSON 数字 `32` 或 `64`，并须与实际项位宽一致。两类写入的事件和偏移允许零。所有项均递归检查 AST 的常量范围、寄存器变元、运算符签名、参数个数与宽度；所有必填字段均检查类型。`predicateWellFormed` 提供这一结构检查，不提供资源有效性、动态身份唯一性或指令语义的证明。

Lean 的 `Cond` 以 `lhs`、`rel`、`rhs` 存储条件，载体取自 `lhs.width`；`Predicate` 保存上述五类构造，列表承载全局与局部观察。直接构造这些 Lean 值并不自动满足数学良构域；不经 JSON 的调用方须保证与 `predicateWellFormed` 相同的结构条件及所属规则的语义前提。`PathMerge.applyLocal` 只检查 Expr 键和位宽并作结构累积，不证明 Predicate 生成可靠性。P2 的集合性质是数学正文的证明，尚无对应的混合累积、指令观察覆盖或完整 History 保持的 Lean 定理。


新类项字符串的裸常量继承字段位宽；嵌套常量载体与上下文不同则使用 `c32:n` 或 `c64:n`。应用结果载体与上下文不同可用 `t32(term)` 或 `t64(term)`。投影与扩展的跨载体应用显式保留输入位宽：`lowq/v`、`extracto,len/v`、`bswapq/v`，以及 `zextq/w/v`、`sextq/w/v`，其中 `v` 是输入载体，`w` 是输出载体。例如 `zext8/64/32(v32:1)` 保留 32 位输入和 64 位结果。载体相同时保留既有短写法。Helper 与 Expr 的渲染格式未改变。

`predicates` 允许重复同结构成员。结构累积保留已有列表次序，再依局部列表次序追加尚未出现的成员；精确合并仅比较集合成员，不比较排列或重复次数。参数和键数组的内部顺序仍参与每个观察的相等。列表排列、集合相等及有序 History 记录是三种不同的比较范围。

### 五类观察的实现对应

RV32IMC 产品 step 的成功增量及状态组合遵循下列覆盖；共享构造和 wire 能表示一个类，不表示该类全部机器生成条件已有实现或证明。

- Helper 的调用身份和 ABI 前缀参数继续沿用既有生成；`externalResult` 仍使用 `[helperId, map, keyPtr]`。当 Meta `maps` 提供对应 `mapId` 的 `keySize`/`valueSize`，且键指针经栈上 `readStackBytes` 可读时，lookup 的 helper `args` 在 ABI 前缀后追加冻结键字节（`Term32`，常量 `< 256`）。无布局或读取失败时 `args` 仍仅为 ABI 前缀，不伪造键。
- Branch 覆盖 `BEQ`、`BNE`、`BLT`、`BGE`、`BLTU`、`BGEU`、`C.BEQZ`、`C.BNEZ` 的每个保留方向；取同一执行前关系的两端 solve 后完整项，Taken 使用原关系，NotTaken 使用补关系。`position` 为运行时数组下标加一，原 Expr 比较约束继续保留；确定比较保留一侧时也生成该侧观察。
- Return 在 `JALR x0,0(ra)` 或 `C.JR ra` 经已有绑定识别为外层 Exit 后，读取执行前关系中 `a0` 的完整 32 位项。程序内返回不生成 Return；完整项缺失拒绝。Exit 的写后完整项检查仍保留，两个时点与实际返回结果的一致性仍需证明。
- PacketWrite 覆盖 Expr 实际选定为 Packet 的 `SB`、`SH`、`SW`、`C.SW`、`C.SWSP`。资源选择沿用 Stack、Map、Packet 的既有优先级；能取得包别名不改变已选定的 Stack 存储，正常对齐的 `C.SWSP` 通常走 Stack。选定 Packet 后取得 `PacketAccess` 的资源身份与偏移，并保存 Expr 字节拆分使用的同一完整源项，生成一个事件。绑定层以 `Option NodeId` 接收真实执行前节点引用；产品 `inferStep` 与 `rv32Snapshot` 传入来源节点身份，无身份时拒绝 `UndefinedSrc`。局部效果与观察一起组合，后续字节覆写保留旧事件。
- MapWrite 在 lookup 观察已带冻结键、Meta 布局匹配且元素内偏移加访问宽度不超过 `valueSize` 时，对 Expr 选定为 Map 的 `SB`/`SH`/`SW`/`C.SW` 发射一条观察（写入事件为当前节点身份，`map`/`key`/`offset`/`source` 取自 lookup 与执行前源寄存器）。缺冻结键、缺布局或越界时拒绝 `UndefinedSrc`；不得只提交 Map Expr 写入。低层 Expr 的 Map 数值切片仍可在观察拒绝前存在于 value step，但不构成产品成功。包侧键缓冲区冻结与 MW-O* 证明义务仍未关闭。

Packet 与 Map 的源项载体宽度不决定窄存储宽度 \(q\)；wire 未添加 \(q\)、字节序或覆盖范围。写入事件与这些属性的关联、访问有效性、别名一致性、真实节点身份的动态区分、历史恢复以及名称外延性仍须依[各类数学义务](../Predicate/谓词定义.md#观察集合累积与可满足性)证明。EBPF 的现有有限 step 切片未接入这次 RV32IMC 的观察生成扩展，不能据 wire 的 64 位支持声称 eBPF 指令覆盖。



## 比较规则

通过全部请求与配置有效性检查后，按 `notTaken` 的数组次序寻找首个与 `taken` 相等的配置。`PathMerge.ExactMerge.sameConfig` 比较位置、Expr 值绑定集合、Expr 约束集合和五类混合观察集合；运行时节点引用不参与配置相等。互补的比较 Expr 仍参与约束集合比较，当前状态的更新遵守[赋值覆盖全部旧关系](../Expr/Expr.md#赋值覆盖全部旧关系)。

项 AST 的相等由返回等式证明或不等式证明的 `DecidableEq` 判定，Expr、Cond 与五类 Predicate 沿用该结构相等。各集合通过双向成员检查比较，不比较 JSON 字符串或渲染文本。集合排列与 Predicate 重复成员不影响结果；约束的重复拒绝规则仍适用。

项的构造、位宽、寄存器身份、运算符及其固定参数、关系、Expr 角色与五类观察的全部构造分量均参与结构相等。改变 Branch 位置、方向或条件，Return 项，MapWrite 事件、Map 项、键、偏移或源项，PacketWrite 事件、资源、偏移或源项，均阻止精确匹配。项、调用参数及键数组按次序比较。不作代数等价求解、名称重命名、投影或差异豁免；HelperOnly 标签也不能放宽这些比较。一个请求内全部配置须有效，全部节点引用须互异，不能因较早候选匹配而忽略后续无效输入。

## 结果与调用方动作

找到首个精确匹配时，返回：

```json
{"status":"merged","scope":"ExactConfig","reuseFrom":17,"taken":42}
```

`reuseFrom` 是被选中的 NotTaken 后缀入口节点引用，`taken` 是本次 Taken 节点引用。结果不附带改写状态；调用方保存匹配关系，并在[证据边界](#语义范围与证据边界)内决定后缀共享。两侧已有状态、前缀与逐步记录保持各自归属。

拒绝表示为：

```json
{"status":"reject","reason":"InsufficientEvidence","detail":"NoExactConfigMatch"}
```

合法配置均不精确匹配，包括位置不同，使用 `InsufficientEvidence` 与 `NoExactConfigMatch`。无效 JSON、字段错误、引用重复、位置表示无效、状态无效及不支持的观察要求均返回 `InsufficientEvidence`。

`detail` 的输入诊断标签为：

- `InvalidRequestJSON:<解析错误>`；`MissingOrInvalidField:<字段名>`。
- `UnsupportedObservationModel:<模型>`；`UnsupportedRequiredObservation:<类别>`。
- `InvalidLocation:<配置标签>` 报告位置字符串无法解析为普通非负下标或 `exit`。
- `InvalidSnapshot:<配置标签>` 报告共享状态解析、寄存器表示、位宽、Expr 角色或键唯一性检查失败。
- `InvalidTerm:<配置标签>` 报告 Expr 递归项或关系参数检查失败；`InvalidPredicate:<配置标签>` 报告已识别类的字段、位宽、递归 AST、关系或构造合法性检查失败。
- `UnsupportedPredicateKind:<配置标签>:<类别>`；`DuplicateNodeId`；`EmptyNotTaken`。

配置标签为 `taken` 或 `notTaken[k]`，其中 `k` 是从零开始的候选数组下标。`InvalidRequestJSON` 的后缀保留 Lean JSON 解析器给出的错误文字。嵌套字段的类型错误按实际失败的校验阶段报告，诊断不承诺枚举同一请求的全部错误。

运行时取得证据不足结果后，仍有可推进的 Taken 待处理配置则继续 step 并重新比较；无待处理配置则保留拒绝依据。调度及记录保留见[合并步](分支合并处理.md#合并步merge-step)。

## 语义范围与证据边界

`scope:"ExactConfig"` 只保证所提供配置在当前五类结构表示中完整相等。该结果是[精确配置共享判据 D3](Jump/证明义务-路径合并完备.md#配置执行前缀与后续行为)的结构比较结果；表示覆盖与数学构造的差异见[五类观察的实现对应](#五类观察的实现对应)，语义解释与后缀引用许可还需要以下证据。

Architecture-Agnostic 是待非 RV32 产品目标建立后检验的研究假设，不是已证明的跨 ISA 验证器性质。ClassifierExpr 共享对象与 PathMerge 的线协议比较不提供目标中立的 create/step 验证门面。现有 EBPF 仅有有限 ALU、入口与 EXIT 的可执行切片及局部行为检查，没有共享预算驱动或与 RV32 对称的展开产品目标；该切片不构成 RV32 产品能力对等或跨 ISA 等价证据。包与上下文访问、资源契约、helper 调用和内部调用返回仍在该 EBPF 可执行切片范围之外。

- 运行时须保证位置有效、相同程序与固定语义语境、同一次分支的两侧来源、配置真实到达及可复用后缀的归属。共同 merge 的结构检查不证明这些事实。
- 完整数学 `Merged(M)` 仍要求 [e_N](Jump/路径合并-接口契约.md#输入) 的 NotTaken 后缀适用性与完整行为覆盖、`e_T` 的 Taken 记录有效性及到达覆盖，以及 [e_M](Jump/路径合并-接口契约.md#mergedm) 的全称精确复用、前缀连接和后缀引用适用性。此 String 请求不传入或产生这些证明，不得把 `status:"merged"` 当作完整 `Merged(M)` 凭据。
- 全部应有观察的生成与保存仍需证明，空数组相等及 FiveClass 声明不能证明观察齐备。同一次分支的 Taken 与 NotTaken 谓词保留不同方向和条件；后续 Expr 覆写不删除这些观察，因而即使 Expr 汇合也不能据此放宽五类精确相等。没有新类观察的旧 HelperOnly 捕获只能证明其已提供状态的比较结果。
- 不同 Expr 或观察的更宽共享仍须完成差异依赖、投影行为保持及覆盖义务，见[未决义务](Jump/路径合并-接口契约.md#未决义务)。有限后续一致性仍以 [P1 至 P4](Jump/证明义务-路径合并完备.md#充分性前提) 为前提：共同语境与良构相等、局部结果外延性、后继准备外延性与闭合性、有限局部结果均须成立。动态调用及写入身份如何同时满足外延性与不同动态步骤的区分要求，仍是[动态身份与名称的模型冲突](Jump/证明义务-路径合并完备.md#仍待证明的义务)；[History 的 H-O1 至 H-O4](History.md#证明边界与待证义务)还要求记录来源、路径保持、完整依赖与事件可恢复范围的对应。实际指令语义、共享后的完整历史与无限行为仍须各自证明。
- 结构不相等只否定精确配置判据，不能作为更宽行为等价的反例。数学拒绝原因中的 `Counterexample` 须有明确否定范围的已证反例；当前导出不产生该结果。
- 特殊循环仅由满足 `Admit(W)` 及 `e_F` 的 `Escape(W)` 获得许可，见[数学契约](Jump/路径合并-接口契约.md#escapew)。精确匹配、比较失败或回返到分支位置均不建立该准入；当前导出不返回 `Escape`，不生成循环凭据。
- [PathMerge/Merge.lean](../../PathMerge/Merge.lean) 的项、Cond 与 Predicate 相等判定使用携带等式或不等式证明的 `DecidableEq`。`#guard` 与 `PathMerge.runMergeChecks` 覆盖有限 wire 回归，包括混合重排与重复成员成功、各类构造字段差异拒绝、全部候选有效性和旧声明标签不投影。`mergeJustDropOverwriteCheck` 与 `mergeComplementaryOverwriteCheck` 是不含新类观察的旧表示缩减实例，只检验 Expr 覆写前后及互补约束；不能作为新 Branch 累积后的汇合依据。这些实例不建立 P1 至 P4、完整 `Merged(M)` 或一般指令语义正确性。[MergeCheck.lean](../../MergeCheck.lean) 提供 `lake env lean --run MergeCheck.lean` 入口；实际执行结果由对应验证记录提供。

## just_drop 实际菱形诊断
以下历史诊断均沿用当时未生成新类观察的捕获与报告，不作为五类生成扩展后的 live 复用结论；新版本复查需保留完整混合观察，并以严格相等预期拒绝仍有互补 Branch 成员的两侧。


以下指令标签 `j11` 至 `j18` 使用捕获图与线协议的零基数组下标；例如 `j11` 对应数学规格中的第 12 条指令。节点编号仅标识这次捕获，复查时须按指令和分支来源重新定位。

捕获的 `just_drop.elf` 图中，节点 12 位于 `loc:"11"`，执行 `BEQ a2,a3,12`。此前 `a3` 的完整值为 `43144`。两个方向的记录为：

- 外层 Taken：节点 `12 → 13 → 20 → 23 → 27 → 30`；节点 13 从 `loc:"14"` 开始执行。
- 外层 NotTaken：节点 `12 → 14 → 16 → 19 → 21 → 25 → 28 → 31`；`j12` 执行 `ADDI a3,zero,129`，随后节点 16 在 `j13` 执行嵌套的 `BNE a2,a3,26`。其中到达节点 19 的是该嵌套分支的 NotTaken 方向。

两条记录都经过 `j14` 的 `ADDI a2,a1,18`。该赋值覆盖以 `a2` 为左值的旧值绑定与旧约束；共同的其他关系继续保留。具体比较结果如下：

1. 节点 20 与 21 位于 `loc:"15"`，即 `j15` 的 `BLTU a0,a2,80` 执行前。两份状态仅 `real32:13` 的完整值绑定不同：分别为 `43144` 与 `129`。清除 `a2` 旧约束已发生，剩余的 `a3` 值差异仍阻止精确匹配。
2. 沿所捕获的两个 NotTaken 后继，节点 27 与 28 位于 `loc:"17"`。两侧都已执行 `j16` 的 `LHU a2,16(a1)`，`a3` 仍分别为 `43144` 与 `129`。
3. `j17` 的 `ADDI a3,zero,18` 写入相同完整值，得到节点 30 与 31，均位于 `loc:"18"`。此时两份完整 Expr 状态按比较规则相等，`predicates` 均为空；共同的两条 `a0` 无符号下界约束仍在状态中。因此相等来自既有指令更新后的完整状态，不来自删去所有约束。

已提供的受控 Lean 重放记录以真实外层方向设置 `taken` 为节点 30、`notTaken` 的候选为节点 31，返回：

```json
{"reuseFrom":31,"scope":"ExactConfig","status":"merged","taken":30}
```

该结果表明现有 oracle 已准许这对可达状态的精确匹配，无需降低 Expr、约束或 Helper 观察的相等要求。空 Helper 观察的证明范围仍受[语义范围与证据边界](#语义范围与证据边界)限制。

仅有 `loc:"17"` 的两份状态，不能证明 `a3` 差异对后续观察无关。该 String 请求未携带指令序列、后缀或依赖证明，无法从请求中排除后续读取 `a3` 并据此产生不同 Helper 观察的程序。实际 `j17` 写回后的完整状态可供精确比较；预先掩去差异则属于尚未取得行为保持证明的放宽。

### 修复前的外层候选覆盖记录

以下记录来自 Cursor 修复 nested-frame handoff 之前的源码重放。当时按捕获图中的真实后继调用 `Agenda.take_ready(1)` 与 `on_successors`，观察 merge 端口收到的节点引用；该端口固定返回拒绝，以保留后续推进。修复前，外层分支的唯一调用记录为：

```text
REQUEST jb=12 taken=13 candidates=[14, 16]
FRAME jb=12 cb=12 phase=Closed
```

此处 `jb=12` 是数学规格的 1 基位置，`cb=12` 是节点引用，两者恰好同值。当时将节点 13 和候选节点 14、16 的完整状态另行送入 Lean oracle，得到：

```json
{"detail":"NoExactConfigMatch","reason":"InsufficientEvidence","status":"reject"}
```

修复前的外层 frame 未比较节点 30 与 31；嵌套分支后的后继没有接续外层候选归属。该记录保留历史故障的定位依据，不描述当前 `schedule.rs`。

### 当前 nested-frame handoff

Cursor 已修正外层嵌套候选归属；已提供的 Cursor 调度测量表明，节点 30 与 31 能进入外层 merge-step。当前源码的对应处理如下：

- [schedule.rs](../../tooling/server/src/driver/schedule.rs) 的 `Agenda::on_successors` 先取得父节点所属的外层 NotTaken 与 Taken frame。出现嵌套的 Taken/NotTaken 对时，外层 NotTaken 仍继承嵌套 NotTaken 根及之后的 `Ok` 后继，将它们接入 `pending_not_taken` 与 `not_taken_candidates`；外层 Taken 继承相应 Taken 根。嵌套 Taken 的阻塞调度由新 frame 承担，不挂到外层 NotTaken 待处理集合。
- `Agenda::open_branch` 建立嵌套 frame，`Agenda::try_merge_at_tip` 从所属 frame 的 `not_taken_candidates` 取得完整配置并交给 merge 端口。外层 NotTaken 沿 `19 → 21 → 25 → 28 → 31` 推进时，候选归属由上述接续保留。
- 同一文件的 `nested_branch_continues_outer_not_taken_candidates` 回归源码包含节点 31 属于外层候选、外层转入 `OpenTaken`、取得 `Reuse { taken:30, reuse_from:31 }` 的断言。该回归使用固定 verdict 与缩减后继图，源码断言的存在不表示本次已经执行测试，也不代表真实 Lean 请求已获得成功响应。
- [merge.rs](../../tooling/server/src/driver/merge.rs) 的 `MergePort::try_merge_configs` 将调度器提供的完整配置包装为 HelperOnly 请求；[engine.rs](../../tooling/server/src/engine.rs) 的 `ExpandSession::apply_merge_effects` 应用成功结果，写入 `mergeReuseFrom` 并添加 `dir:"reuse"` 边。API 快照中的对应字段由 [expand.rs](../../tooling/server/src/expand.rs) 导出为 `merge_reuse_from`。

Cursor 的 handoff 测量、受控 Lean 重放与上述只读源码证据分别支持调度接续、30/31 精确匹配和结果应用路径。后续真实 HTTP 测量的版本归属与结果见[U2 live 测量](#u2-live-测量)；捕获图本身不确定进程链接的源码版本。完整语义义务见[语义范围与证据边界](#语义范围与证据边界)。

### U2 live 测量

Cursor 提供的 U2 live 报告 `.omp/u2-tooling-live-report.md` 记录：在 `agent/lean4-front` 的 `05671e3` 之后，服务经 `cargo build -p server` 链接当时的 Lean 共享库，端口为 8798，预算为 1024。该报告的真实镜像测量为：

- `just_drop.elf`：`status:"complete"`，`fuel:906`，`work:0`，`nodes:130`，`edges:130`，`reuse:1`；复用边为 `49 → 22`，`dir:"reuse"`。报告中的较早 MERGE_TRACE 记录 `jb=12 taken=49 loc=18 cands=[...,22,...] -> merged`。
- `merge_try.elf`：`status:"complete"`，`fuel:981`，`work:0`，`nodes:49`，`edges:48`，`reuse:0`。该报告将结果归于 HelperOnly 下的 `NoExactConfigMatch`，调度完成而没有精确配置汇合；该镜像不要求放宽 ExactConfig。

这些是 U3 切换前的有限 live 测量，不是 U3 服务测试结果。节点 49/22 与前述历史捕获的 30/31 属于不同运行，不得互换引用；新的复查须按实际镜像、位置和分支来源定位。

### U3 重新链接后的 live 复查

1. Cursor 先适配 tooling 绑定与链接顺序，将服务重新链接到 U3 的 ClassifierExpr、PathMerge、RV32IMC 共享库；随后按[服务端接口](../../tooling/server/README.md)通过 `POST /api/session` 分别上传真实 `just_drop.elf` 与 `merge_try.elf` 的 `image_b64`，对各会话执行 `POST /api/session/<id>/run` 并保留返回快照。只设置显示名称而省略镜像仍使用默认镜像。按实际指令位置和边的方向定位两侧到达，保留完整 `exprs`、`predicates`、后继边及本次节点引用；`merge_try.elf` 使用自身的指令和分支来源，不沿用 just_drop 的下标或节点引用。
2. 对重新捕获状态构造完整请求，比较对应 `loc:"15"`、`loc:"17"` 与 `loc:"18"` 的配置对。Taken 与 NotTaken 标签须遵守外层分支的真实来源，不得只抽取 `a3` 行代替完整状态。旧 U3 空观察记录在最终覆写后曾匹配；五类生成扩展后，只要保留不同 Branch 成员，即使 `loc:"18"` 的 Expr 相等仍应返回 `NoExactConfigMatch`，不能丢弃观察重现旧成功。
3. 跟踪重新链接后服务的外层 frame 候选集合、每次实际交给 merge 端口的完整请求及原始响应，核对镜像、状态来源、可复用后缀归属与最终阶段。just_drop 按新捕获定位 `loc:"18"` 的真实比较；merge_try 按其实际汇合配置核对。源码重放结果、Cursor handoff 测量、受控 Lean 成功及切换前 U2 测量不能替代 U3 的 live 请求响应证据。
4. 对两个 `/run` 返回快照分别检查 `dir:"reuse"` 边和节点的 `merge_reuse_from` 引用，确认匹配响应被应用为保留各自前缀的后缀引用，并检查该复用范围的重复后缀是否停止展开。只有真实请求、原始响应及引用动作均被观察到，才能报告 live 复用成功。

这些复查只检验有限捕获及接口行为；完整五类观察、后缀覆盖、动态身份、完整历史连接与无限行为的证明义务继续由[语义范围与证据边界](#语义范围与证据边界)维护。
