# 工具工作区

[项目入口](../README.md) · [文档索引](../doc/README.md)

`tooling` 包含 Lean 项目的前后端、Rust FFI 绑定和开发工具。Lean 源码与 `.lake` 构建产物位于仓库根目录。Cargo 工作区与构建产物位于 `tooling`。

## 启动应用

在仓库根目录运行：

```bash
lake run dev
```

Lake 构建 Lean 和服务端、安装前端依赖，然后启动 API 和 Vite。打开 <http://127.0.0.1:5173>。API 默认监听 <http://127.0.0.1:8788>。按 Ctrl-C 停止两个服务。

## 构建与检查

在仓库根目录运行：

```bash
lake build
lake test
```

API 检查脚本启动临时服务，验证 demo 和 ESP32-C3 会话的创建、单步、运行及读取结果，结束后停止服务。脚本需要 Python 3。

## 组件

- [server](server/README.md) 提供 Lean 驱动的展开会话 API。
- [web](web/README.md) 显示指令、表达式和展开图。
- `lean-binding` 将 Lean 导出函数接入 Rust，Rust 模块名为 `lean_binding`。
- `scripts/dev.py` 管理开发服务进程的启动和停止，由 Lake 调用。
- `fixtures/esp32c3.bin` 是服务端嵌入的 XDP 镜像，也是 `RV32IMC/Esp32c3Program.lean` 的生成输入。

项目命令统一由根目录的 `lakefile.lean` 定义。
