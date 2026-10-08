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
cargo xtask demo
```

启动器构建 Lean、启动 API 和 Vite，并安装前端依赖。打开 <http://127.0.0.1:5173>，按 Ctrl-C 停止服务。默认 API 地址为 <http://127.0.0.1:8788>。

服务接口见 [debug_server](debug_server/README.md)，界面操作与独立启动方式见 [debug_web](debug_web/README.md)。

## 构建与检查

Lean 工具链版本由 `lean-toolchain` 指定；本地需安装 Lean/Lake、Rust/Cargo 和 Node.js/npm。

```bash
lake build
lake build RV32IMC
cargo test -p lean_binding
cargo test -p debug_server
npm --prefix debug_web ci
npm --prefix debug_web run build
```

## 工作区布局

- `CommonMath/`：架构无关的数学对象与展开实现。
- `RV32IMC/`、`EBPF/`：指令集相关源码。
- `lean_binding/`：Lean 导出函数的 Rust 绑定。
- `debug_server/`、`debug_web/`：调试 API 与图形界面。
- `xtask/`：工作区启动工具。
- `doc/`：规范、实现说明与研究文档。
- `esp32c3.bin`：调试用 XDP 镜像。

开发代理的约束与 Lean 工作交接方式见 [AGENTS.md](AGENTS.md)。构建产物和本地代理记录由 `.gitignore` 管理。
