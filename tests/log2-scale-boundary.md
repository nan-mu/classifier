# log2 首个超限规模的真实响应

历史 EXB2 协议诊断。这个用例测试 `n > 1024` 时的响应。它在计算循环前结束，当前 PR #9 的循环和包内写入验收使用已有合法向量。

任务书作者使用 classifier `8e81c243e3918fd6b60ba8240f56a7ec77b9aa66` 的 `make_specs.py`、libbpf-mcu `v0.1.0` 固定提交 `ef1771d9c949771c707b93fd9da5c3e2602efee0` 的 C host 入口和 `v0.1.1` 正式 rBPF 容器执行。host 入口由 `cc -O2 -shared -fPIC -DEB_HOST_ENTRY` 构建。两版 tag 的 `tests/xdp` 和 `tests/fixtures` 源码比较无 diff。

| 输入 | 长度 | host 观察 |
| --- | ---: | --- |
| `request(2, 1024, 1)` | 8258 | XDP_PASS，偏移 36 的 status 为 0 |
| `request(2, 1025, 1)` | 8264 | XDP_ABORTED，写入 0 字节，status 保持哨兵 `0xffffffff` |
| 第一个输入只把偏移 12 的小端 `n` 改为 1025 | 8258 | XDP_ABORTED，仅把偏移 36–39 的 status 写为 `04 00 00 00` |

[上游代码](https://github.com/nan-mu/libbpf-mcu/blob/ef1771d9c949771c707b93fd9da5c3e2602efee0/tests/xdp/exb2/exec_program.h#L49) 先核对容器内程序接收的包长，再检查 `n > EB_MAX_WORDS`。因此 8264 字节只测到 `EB_SHORT_BUFFER`。第三行测到 `EB_BAD_RANGE`。使用第三行生成的完整输入及期望直接运行 `analyze.py analyze`，正式发布中的 `log2-vm-ebpf.elf` 给出 `scale-over-limit: holds`，完整包字节及动作比较通过。
