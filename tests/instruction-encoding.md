# 非法指令字段被当成合法指令执行

任务书作者在 classifier `8e81c243e3918fd6b60ba8240f56a7ec77b9aa66` 使用 Python 3.12、Z3 4.15.4，通过 `tooling/rbpf/test_analysis.py` 的 `run()` 运行两条指令。该入口经 `decode()` 构建程序并求解正常退出覆盖和动作规格。

输入是空包，期望动作 1。编码依次为立即数 `MOV64 r0, 1`（`0xb7`）和 `EXIT`（`0x95`）。先用 `offset=0`，再只把 MOV 的 `offset` 改成 7。两次规格否定式均返回 `unsat`，最终判定均为 `holds`。同一环境运行 `python3 -m unittest discover -s tooling/rbpf -q` 时已有 7 项测试全部通过。

[RFC 9669 §3.1](https://www.rfc-editor.org/rfc/rfc9669.html#section-3.1) 规定未使用字段清零。结果定位到 [指令解码](https://github.com/nan-mu/classifier/blob/8e81c243e3918fd6b60ba8240f56a7ec77b9aa66/tooling/rbpf/machine.py#L140) 与 [ALU 分派](https://github.com/nan-mu/classifier/blob/8e81c243e3918fd6b60ba8240f56a7ec77b9aa66/tooling/rbpf/machine.py#L366)。复用旧版结果作失败基线，并在新 eBPF 对象入口验证合法编码的正常结果与非法编码的拒绝或未判定。
