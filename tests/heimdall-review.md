# PR9 当前执行框架与测试路径（静态审核）

审核对象：[classifier PR9](https://github.com/nan-mu/classifier/pull/9)，head `0c1d2a962624dee91dabd10a841f9164d61626b2`。任务书作者通过 GitHub MCP 读取 PR diff、提交历史、说明与审计记录，未运行程序。

- [angr_backend.py](https://github.com/nan-mu/classifier/blob/0c1d2a962624dee91dabd10a841f9164d61626b2/tooling/rbpf/angr_backend.py)：AngrBackend.run 使用 angr.Project 的 blob backend、XdpWorld.initial、project.factory.successors；Lookup 为 SimProcedure。正式路径已经使用 angr，但未采用完整上游装载、SimOS 和路径管理方法。
- [test_analysis.py](https://github.com/nan-mu/classifier/blob/0c1d2a962624dee91dabd10a841f9164d61626b2/tooling/rbpf/test_analysis.py)：run 构造 Program 时没有 backend；[analysis.py](https://github.com/nan-mu/classifier/blob/0c1d2a962624dee91dabd10a841f9164d61626b2/tooling/rbpf/analysis.py) execute 因此走 Machine。七项旧回归测试不能作为新后端语义测试。
- analysis.py run_case 在 coverage、comparison、spec_coverage 均 UNSAT 时设置 holds，没有独立裁决 gaps 的可达性。存在重叠的正常/异常路径时可能误判；这是静态风险，尚未复现具体反例。
- [上游固定提交](https://github.com/vdasu/heimdall/tree/90b4605e1c6ddae7ae5ead9738d5c1ff8e2843ad) 的目录读取确认存在 load_ebpf.py、simos_ebpf.py、arch_ebpf.py、instrs_ebpf.py、lift_ebpf.py、generate_formula.py、verify_equivalence.py。完整上游运行仍待本轮复现。
- tooling/README.md 当前仍把 rbpf 介绍为 Compact ELF 分析工具；tooling/rbpf/README.md 同时描述正式对象和历史容器入口。迁移后需要分清职责并检查其余引用。

这些是本轮静态基线，可直接引用；无需重复证明旧测试走 Machine。旧开发者报告的正式结果见 PR 审计，不能替代迁移后的重新执行。