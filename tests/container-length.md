# 合法 Compact ELF 总长失败基线

验证由任务书作者在 classifier `8e81c243e3918fd6b60ba8240f56a7ec77b9aa66`、Linux x86_64、Python 3.12、Z3 4.15.4 环境执行。使用 libbpf-mcu `v0.1.1` 的 `make/xpost_elf.py` 编解码器及该 Release 的 `just_drop` 容器元数据。

用上游 `parse_container` 取 `just_drop-vm-ebpf.elf` 的元数据。将 2124 条普通 `MOV64 r0, 1` 加一条 `EXIT` 编成 17,000 字节的镜像，用 `build_container` 封装。上游读回的元数据和镜像与输入相同。容器为 17,300 字节，SHA-256 为 `5b428a5226f85aaf2cd5242e10abcf9ff21094b0ec2279b90f02e6c7ab88eece`。普通 MOV 和 EXIT 的小端指令字节分别为 `b700000001000000` 和 `9500000000000000`。

用 `analyze.py analyze <容器> --engine ebpf --spec <规格> --out <新目录>` 执行。规格为 `{"cases":[{"id":"drop","input":{"packet_hex":""},"expect":[{"action":1}]}]}`。现有 head 退出 1 并报告 `error: Compact ELF exceeds 8192 bytes`。源码另见 [归档限制](https://github.com/nan-mu/classifier/blob/8e81c243e3918fd6b60ba8240f56a7ec77b9aa66/tooling/rbpf/analyze.py#L120) 与 [Rust 限制](https://github.com/nan-mu/classifier/blob/8e81c243e3918fd6b60ba8240f56a7ec77b9aa66/tooling/rbpf/src/main.rs#L8)。

这次执行覆盖旧 Compact ELF 单容器入口的失败。作为旧实现的历史记录保留，classifier PR #9 当前 eBPF 对象入口独立于 Compact ELF，无需在本轮复验此样本。
