# Classifier

基于 Lean 的指令符号表达式与有预算展开项目。`ClassifierExpr` 提供寄存器、符号项、表达式和 wire 类型。`PathMerge` 比较 HelperOnly 的 ExactConfig。`RV32IMC` 提供 RV32 解码、值转换和有预算展开。`EBPF/` 提供有限解码、ALU 值转换、入口和局部 step。

## 文档入口

完整阅读路线见 [文档索引](doc/README.md)。

- [寄存器定义](doc/寄存器定义.md)、[Expr](doc/Expr/表达式阅读索引.md)与 [Predicate](doc/Predicate/谓词阅读索引.md)：对象定义、关系生成和观察规则。
- [位向量与数值函数](doc/Expr/位向量与共同数值函数.md)：共同数值基础。
- [节点推理](doc/NodeInference/节点推理阅读索引.md)：推理入口、各判断步骤、展开模型与证明。
- [RV32 初态描述](doc/RV32初态描述.md)：入口条件与初始关系。共同指令规则按问题放在 Expr、Predicate 和 NodeInference 中。
- [代数程序分析](doc/NodeInference/路径语言与位置消去.md)：路径表达式与语义解释的研究说明。

## 启动调试界面

在仓库根目录运行：

```bash
lake run dev
```

Lake 构建 Lean 和服务端、安装前端依赖，然后启动 API 和 Vite。打开 <http://127.0.0.1:5173>，按 Ctrl-C 停止服务。默认 API 地址为 <http://127.0.0.1:8788>。

服务接口见 [服务端](tooling/server/README.md)，界面操作与独立启动方式见 [前端](tooling/web/README.md)。

界面接受 xpost 的 Compact XDP ELF。默认使用 `tooling/fixtures/just_tx.elf`
（来自 `/Volumes/SSD/bs/build/just_tx/just_tx.elf`）。
服务端通过 `xpost-elf` 提取代码镜像、程序基址和 helper dispatcher 地址。
Lean 识别 helper 调用，生成 Helper 观察与返回表达式并继续展开。
RV32 走 32 位分派器约定；原生 eBPF `call imm` 走独立的 64 位约定。
Map 布局可由 Meta `maps` 提供（just_tx 与 RV32 AOT map 行共用）。

## 构建与检查

以下命令在仓库根目录运行。

Lean 工具链版本由 `lean-toolchain` 指定；本地需安装 Lean/Lake、Rust/Cargo、Node.js/npm 和 Python 3。
Rust 服务端还依赖相邻 `../xpost/xpost-elf` 和它的 `xpost-macros` 库。

```bash
lake build
lake test
```

`lake build` 构建 Lean 库、服务端和前端。`lake test` 运行 Rust 测试、前端构建和实际 API 检查。

## 工作区布局

- `ClassifierExpr/`：数学值对象、wire 类型与解析。
- `PathMerge/`：路径与 HelperOnly ExactConfig 合并。
- `RV32IMC/`：RV32 解码、展开、预算，以及 create 和 step。
- `EBPF/`：有限解码、ALU 值转换、入口和局部 step。
- `tooling/`：Rust/Cargo 工作区、前后端、FFI 绑定、启动工具与测试镜像。组件说明见 [工具工作区](tooling/README.md)。
- `doc/`：数学定义、推导、证明与研究文档。

代理约束分两个 harness。Cursor（`tooling/`）见 [.cursor/AGENTS.md](.cursor/AGENTS.md)；omp（`doc/` 与 Lean4）见本地 `.omp/AGENTS.md`。构建产物和本地代理记录由 `.gitignore` 管理。
