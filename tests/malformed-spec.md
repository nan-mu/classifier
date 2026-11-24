# 单个坏规格中断发布批处理

历史诊断记录。这里损坏的是分析工具的外部 JSON 规格，使用的发布归档和 eBPF 对象均有效。当前 PR #9 的正式验收以真实对象和合法规格执行，正式验收遇到规格错误仍按任务书停止条件处理。

任务书作者在 classifier `8e81c243e3918fd6b60ba8240f56a7ec77b9aa66` 用 Python 3.12、Z3 4.15.4、7-Zip 25.01 和该提交编出的 Rust inspector，执行现有 `analyze.py release`。输入取 [v0.1.1](https://github.com/nan-mu/libbpf-mcu/releases/tag/v0.1.1) 的 `just_drop.7z` 和 `just_tx.7z`，SHA-256 从同一 Release 读取并核对，按名称依次处理。`just_tx` 使用原任务书的有效规格。

`just_drop.json` 中放入 `{"cases":[{"id":"bad","input":{"packet_hex":"00"},"expect":[{"action":1,"bytes":[]}]}]}`。CLI 退出 1，末行显示 `AttributeError: 'list' object has no attribute 'items'`，未生成 `summary.json` 和 `just_tx/result.json`。起因是 [规格解析](https://github.com/nan-mu/classifier/blob/8e81c243e3918fd6b60ba8240f56a7ec77b9aa66/tooling/rbpf/analysis.py#L194) 直接调用 `items()`，且 [release 与 offline 的错误边界](https://github.com/nan-mu/classifier/blob/8e81c243e3918fd6b60ba8240f56a7ec77b9aa66/tooling/rbpf/analyze.py#L204) 均无法报告此异常。
