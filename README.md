# Classifier

基于 Lean 的指令符号表达式与有预算展开项目。`CommonMath` 提供共享的寄存器、符号项、表达式和展开模型；`RV32IMC` 提供 RV32 指令解码与表达式转换。eBPF 的值函数说明见文档，相关源码位于 `EBPF/`。

## 文档入口

完整阅读路线见 [文档索引](doc/README.md)。

- [共同数学定义](doc/common-math.md)：共享对象、语义状态、路径和展开算法。
- [RV32IMC 值函数](doc/rv32imc-expr-value-functions.md)与 [RV32 初态](doc/rv32-initial-expr.zh.md)：指令规则和入口约定。
- [eBPF 值函数](doc/ebpf-expr-value-functions.md)：eBPF 规则及待定边界。
- [代数程序分析](doc/algebraic-program-analysis.zh.md)：路径表达式与语义解释的研究说明。

## 启动调试界面

在仓库根目录运行：

```bash
lake run dev
```

Lake 构建 Lean 和服务端、安装前端依赖，然后启动 API 和 Vite。打开 <http://127.0.0.1:5173>，按 Ctrl-C 停止服务。默认 API 地址为 <http://127.0.0.1:8788>。

服务接口见 [服务端](tooling/server/README.md)，界面操作与独立启动方式见 [前端](tooling/web/README.md)。

## 构建与检查

以下命令在仓库根目录运行。

Lean 工具链版本由 `lean-toolchain` 指定；本地需安装 Lean/Lake、Rust/Cargo、Node.js/npm 和 Python 3。

```bash
lake build
lake test
```

`lake build` 构建 Lean 库、服务端和前端。`lake test` 运行 Rust 测试、前端构建和实际 API 检查。

## 工作区布局

- `CommonMath/`：架构无关的数学对象与展开实现。
- `RV32IMC/`、`EBPF/`：指令集相关源码。
- `tooling/`：Rust/Cargo 工作区、前后端、FFI 绑定、启动工具与测试镜像。组件说明见 [工具工作区](tooling/README.md)。
- `doc/`：规范、实现说明与研究文档。

开发代理的约束与 Lean 工作交接方式见 [AGENTS.md](AGENTS.md)。构建产物和本地代理记录由 `.gitignore` 管理。
