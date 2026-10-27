# Classifier

Classifier 取同一份 XDP C 的两份编译结果。一份是 eBPF 字节码。另一份是 ESP32-C3 上的 RV32IMC XDP ELF。它先做有预算的符号展开，再对照展开得到的观察。已经实现的目标是 RV32IMC，ABI 为 `ilp32`，没有 FPU。

eBPF 检查器在自己的模型里给出 Safe(E)。本仓库对照的是两边的选定观察。由观察一致得到 Safe(R) 还缺的对应写在 [证明义务](doc/证明义务.md)。

许可证是 [MIT](LICENSE)。

## 安装依赖

`lean-toolchain` 指定 Lean 4.29.0。用 [elan](https://github.com/leanprover/elan) 安装这个版本的 Lean 和 Lake。另外安装 Rust、Cargo、Node.js、npm 和 Python 3。

Compact XDP ELF 由 `tooling/vendor/xpost-elf` 读取。

## 启动界面

在仓库根目录运行：

```bash
lake run dev
```

Lake 构建 Lean 库和服务端，安装前端依赖，然后启动 API 和 Vite。打开 <http://127.0.0.1:5173>。API 监听 <http://127.0.0.1:8788>。要换 API 端口，先设置环境变量 `PORT`。按 Ctrl-C 停止两个进程。

没有上传镜像时，服务端使用 `tooling/fixtures/just_tx.elf`。上传文件必须是 Compact XDP ELF。服务端拒绝原始 BIN。界面操作见 [前端](tooling/web/README.md)。HTTP 字段见 [服务端](tooling/server/README.md)。

## 构建并测试

在仓库根目录运行：

```bash
lake build
lake test
```

`lake build` 构建 Lean 库、Rust 服务端和前端。`lake test` 先跑 `profile.toml` 里的双架构比较，再构建没有 `sorry` 的 `Verification` 库，然后跑 Rust 测试。

`profile.toml` 把镜像目录设为 `../build/<name>/`。这些文件由本仓库以外的编译器写入。只克隆本仓库时，`profile_programs_match_expect` 会因为找不到镜像而失败。仓库自带的用例不读这个目录。

```bash
lake env cargo test --manifest-path tooling/Cargo.toml --workspace -- --skip profile_programs_match_expect
lake env cargo run --manifest-path tooling/Cargo.toml -p server --bin classifier -- test --root tooling/test
```

`classifier test` 在每个 `case.json` 都符合期望时退出码为 0。有用例失败时退出码为 1。用法错误时退出码为 2。用例说明见 [tooling/test](tooling/test/README.md)。

`../build` 里的镜像齐全时，`profile.toml` 的期望如下。预算是 1024。

| 结果 | 程序 |
| --- | --- |
| `strict` | bitswap、bsort、firewall、incr、merge_try、square |
| `weak` | buf、fib、fletcher32、helper_loop、just_tx、memcpy |

`strict` 表示两端都展开完成，观察类别的顺序一致，并且分支表达式没有未完成项。`weak` 表示两端完成且类别顺序一致，同时至少有一条分支表达式没有配上。

## 目录

```text
src/                 Lean 源码
  Term Expression Observation Interface Wire Match   库 Core
  Node/              路径、预算展开、精确配置合并
  Cross/RV32/        RV32IMC 入口、解码与单步
  Cross/EBPF/        eBPF 入口、解码与单步
  Verification/      已证陈述。Unverified/ 不进入这个库
tooling/             Cargo 工作区、前端、夹具、vendor
doc/                 比较模型笔记
profile.toml         双架构程序与期望结果
```

Lake 库名是 `Core`、`Node`、`RV32`、`EBPF` 和 `Verification`。源码都在 `src/`。组件说明见 [工具工作区](tooling/README.md)。

## 笔记

从 [文档索引](doc/README.md) 进入。

- [接受](doc/接受.md) 写命题 1，也就是选定观察的含义一致。
- [表达式](doc/表达式.md)、[观察](doc/观察.md) 和 [寄存器](doc/寄存器.md) 给出比较所用的三项定义。
- [接口](doc/接口.md) 和 [路径](doc/路径.md) 记录 `create`、`step`、`update`、`history` 和单轮回边。
- [匹配](doc/匹配.md)、[局限](doc/局限.md) 和 [证明义务](doc/证明义务.md) 写下路径匹配、表达式匹配，以及命题 1 还缺的对应。
