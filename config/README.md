# 运行时配置与契约

本目录存放 RV32 路径流水线的**环境契约**。不再包含 Isla IR / ISA TOML。

| 文件 | 用途 |
|------|------|
| `esp32c3.environment.toml` | RV32 分类的显式运行时假设（helper ABI、栈/包/map 契约等）。默认 `--environment`；测试与模块内 `include_str!` 也指向此文件。 |

示例固件与 BPF 汇编夹具放在仓库根下的 `example/`（`esp32c3.bin`、`just_drop_bpf.toml`）。

`esp32c3.environment.toml` 是可运行的条件性示例契约，不是从硬件验证出的事实；更换固件时必须换成对应契约。
