# eBPF 发布对象分析

`analyze-object` 分析单个 ELF64 小端 XDP 对象。批处理 `release` 校验发布归档的 SHA-256、v3 索引及其 `bpf.path` 对应的成员，并调用同一个装载和执行入口。档案可以只有源文件、索引和发布对象。该链路使用 CLE eBPF ELF backend、archinfo、VEX、SimOS 和 angr SimulationManager。

## HEIMDALL 来源与适配

上游版本为 [HEIMDALL `90b4605`](https://github.com/vdasu/heimdall/tree/90b4605e1c6ddae7ae5ead9738d5c1ff8e2843ad)，许可证见 [angr_ebpf/LICENSE](angr_ebpf/LICENSE)。路径谓词与守卫输出采用论文 §3.2、§3.3 的构造。原生程序对复跑使用上游的 `verify_equivalence.py`，此处使用其路径符号执行与结果公式构造来检查各个程序的观察规格。[HEIMDALL 论文](https://arxiv.org/html/2605.25411v1#S3.SS2)

| 上游实现 | 适配 | 核对方式 |
| --- | --- | --- |
| `angr_ebpf_backend/angr_ebpf/{load,arch,lift}_ebpf.py` | 显式 CLE backend 用项目注册的 64 位小端 eBPF 架构类，解决构造函数中的别名解析。入口取 CLE 符号的重定位地址。 | 真实 ELF CLI 与全量发布对象。 |
| `angr_ebpf_backend/angr_ebpf/instrs_ebpf.py` | VEX 按 RFC 9669 对无符号零除数定义 DIV/MOD。装载时检查保留字段及合法但未支持的形式。 | 两种位宽的符号除数、零扩展、条件跳转和 END 回归。 |
| `angr_ebpf_backend/angr_ebpf/simos_ebpf.py` | 沿用 syscall 调用约定、lookup 对调用时刻的内存读取及 EXIT sentinel。SimOS 载入只注册 `map_lookup_elem` 的库并继承退出初始化。map 插件沿用已有有限 HASH/ARRAY 的逻辑键状态。 | firewall 的符号键及存在位和 just_tx 的指针写入、回绕、MAC 交换。 |
| `c2rust_translation/generate_formula.py` | 依照 `patch_ebpf_relocations` 通过 ELF 文件偏移定位 CLE 加载的 LDDW 并写入 map 索引。保留严格 ELF/BTF 验证，复核重定位后的 CLE 字节。复用路径约束合取和带守卫的结果析取。 | 坏重定位的槽定位、关系和覆盖 SMT-LIB 的独立复算。 |
| 上游 SimulationManager 的正常终止状态 | 沿用 SimulationManager 分类，通过指令、内存事件与 stash 保存中断、异常、未定义数据或预算缺口。只接受到达上游 EXIT sentinel 的 XDP 退出。 | 有限符号循环与刻意零回边预算。 |

状态范围为 XDP context、声明的有限包和逻辑 map、512 字节栈以及上游退出所需的内部帧。多值地址、未支持指令和 helper 会诊断。合法 END 支持 ALU 类的 LE/BE 转换。ALU64 END、带符号 DIV/MOD 和 MOVSX 形式目前拒绝装载。未列出的 HASH 键缺失，未列出的有效 ARRAY 键初值为零。分析受步数、回边、路径数和求解时间限制。

报告的 `result.json` 保存来源、后端、版本、入口、预算、路径条件、32 位动作、有效包范围和字节、context、map 初终态及有序 helper 与写入事件。helper 保存调用时刻的键，写入保存指令槽、资源、偏移、宽度和值。规格格式见 [单个容器的规格示例](../rbpf/README.md#单个容器)，两条入口共用同一格式和观察定义。

`holds` 要求域非空。正常退出覆盖缺口、路径重叠、可达执行缺口、规格覆盖缺口和规格否定式的查询均须为 UNSAT。覆盖或缺口可达性未判定时保留该状态。每个用例保存可独立用 Z3 复算的 SMT-LIB，其中 `return-formula.smt2` 是退出条件与对应动作构成的关系。规格比较另核对包、context、逻辑 map 和 helper 观察。

## 复跑 v0.1.1

需要 Python 3.12、7-Zip 和原任务包。锁文件保留了原型使用的依赖。环境使用锁定的 angr、claripy、CLE 和 Z3 版本。正式向量规格直接读取原包的 23 组输入和保存的独立期望，不重建历史 C host 用例。

```sh
run=$(mktemp -d)
python3.12 -m venv "$run/venv"
py="$run/venv/bin/python"
"$py" -m pip install -r tooling/angr/requirements-angr.txt
"$py" -m unittest discover -s tooling/angr -v
shasum -a 256 /tmp/classifier-release-elf-taskbook.zip
unzip -q /tmp/classifier-release-elf-taskbook.zip -d "$run/bundle"
mkdir "$run/assets"
gh release download v0.1.1 --repo nan-mu/libbpf-mcu --pattern '*.7z' --dir "$run/assets"

"$py" tooling/angr/make_specs.py \
  --evidence "$run/bundle/evidence" --out "$run/specs"
"$py" tooling/angr/analyze.py release --tag v0.1.1 \
  --assets "$run/assets" --digests tooling/angr/libbpf-mcu-v0.1.1-digests.json \
  --specs "$run/specs" --out "$run/release"
"$py" tooling/angr/acceptance_objects.py --release-results "$run/release" \
  --assets "$run/assets" --evidence "$run/bundle/evidence" \
  --specs "$run/specs" --out "$run/checks" --z3 z3
```

原任务包的 SHA-256 为 `64e25d28e27daffb5c3df264749e95c79da808895195be04413aea8c58208e8f`。正式验收用 `--z3` 指定独立的 Z3 可执行文件复算查询。单文件分析可直接使用复跑脚本导出的已核验对象。

```sh
"$py" tooling/angr/analyze.py analyze-object "$run/checks/case_mark_bpf.o" \
  --spec "$run/specs/case_mark.json" --out "$run/one-object"
```

批处理在每条记录中保留摘要或错误定位。合法对象按索引装载，rBPF mode 和容器成员不参与该路径。缺少规格的条目报告 `no_spec`，验收脚本要求 12 个程序均执行并通过对应向量。反例可把 `counterexample.json` 当作 `--spec` 重放。具体失败和未覆盖范围可从 `result.json` 追到指令槽及查询。
