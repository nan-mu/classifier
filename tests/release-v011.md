# v0.1.1 发布对象与验证记录

## 已核验的 eBPF 对象

从已核对 Release SHA-256 的 12 个正式归档，逐包读取 `index.toml` 的 `bpf.path`，核对成员长度、摘要及 ELF64 小端 `ET_REL` / `EM_BPF`。12 个条目均为 `objects/<程序>_bpf.o`。逐包比较对象的 `xdp` 节与同归档的 `.xpost.image`，12 对长度均相同，10 对字节完全一致。剩下两对各只有一条 map 引用的 `lddw` 不同。`firewall` 的 `.relxdp` 偏移 `0x60` 指向 `blacklist`，`just_tx` 的 `0x1f0` 指向 `rxcnt`，类型均为 `R_BPF_64_64`。两张 map 的键、值均为 4 字节，容量均为 256，分别为 HASH 和 ARRAY。对象给出了 map 身份和定义，装载器可以据此完成绑定。对应 [封装及改写代码](https://github.com/nan-mu/libbpf-mcu/blob/07a4ea9a81a7fedf7bef2d6ced8d7fcfcccfd113/tools/src/main.rs#L220)。

用 pyelftools 复核 12 个对象的节表和 XDP 重定位。全部对象都含非空 `xdp` 和 `license`，`.text` 均为空，且均无 `.bss`、`.data`、`.rodata`。只有 `firewall` 和 `just_tx` 含非空 `.maps`，且各有上文所列的一条 XDP 重定位。其他对象没有 XDP 重定位。该批次无需建立普通全局数据节的初始状态。EXB2 的 scratch 位于输入包缓冲区。例如 `copy` 原合法向量的 `n=4096`、`rounds=2`，可直接比较完整包和 scratch。 [copy 循环](https://github.com/nan-mu/libbpf-mcu/blob/07a4ea9a81a7fedf7bef2d6ced8d7fcfcccfd113/tests/xdp/exb2/copy.h#L1)

## 发布对象到 angr 的预验证

任务书作者在 Linux x86_64、Python 3.12.14，用 angr/claripy 9.2.176、pyelftools 0.32 和原任务包的 `evidence/angr_ebpf/` 运行。按该包的已知版本固定 bitstring 4.3.1、pycparser 2.23，避免重现仅安装 angr 时 bitstring 5.0.0 的 `ConstBitStream` 导入错误。

先用发布清单验证原始 7z，再用索引验证 eBPF 对象。以 ELF 解析器提取 `xdp`，用 `angr.Project` 的 blob 后端配合 `ArchExtendedBPF` 和 `SimOsEbpf` 执行，载入实验地址 `0x200000`。分别初始化 `R1` 的 context 指针、`R10` 的栈帧指针及包长和字节。地址与 Heimdall 内部调用栈和退出哨兵分离。三个对象的 XDP 节均无需重定位，过程未使用容器载荷。

| 对象 | 输入域 | 原型输出 |
| --- | --- | --- |
| `just_drop` | 空包 | 1 个正常出口，XDP_DROP，动作差异 UNSAT |
| `case_mark` | 使用原匹配帧模板，包长为 81 或 82，偏移 74 任意 | 3 个正常出口，覆盖缺口 UNSAT，动作和偏移 77 差异 UNSAT，错误版本规格 SAT |
| `case_swap` | 同一符号输入域 | 3 个正常出口，覆盖缺口 UNSAT，动作和偏移 77 差异 UNSAT，错误版本规格 SAT |

这次预验证覆盖三个无 map 重定位对象的装载和指定的观察量。原型的结果和预期可复用，正式 CLI 的共用入口、完整日志与 23 个向量需以本轮实现验证。`firewall` 和 `just_tx` 的 map 绑定已有静态证据，angr 下的 map 和 helper 行为仍待验证。

## 旧后端的批处理基线

任务书作者在 Linux x86_64 对 classifier `8e81c243e3918fd6b60ba8240f56a7ec77b9aa66` 进行端到端验证。使用 Rust 1.100.0 按锁文件构建 `classifier-rbpf`，Python 3.12.14、Z3 4.15.4 与 7-Zip 25.01。inspector 的报告版本为 0.1.0，本地可执行文件 SHA-256 为 `ef3392ebb6c67e93e8c5e1e41ffc7430d6be60c67c19893136752e8fc0f63729`。

从 [libbpf-mcu v0.1.1](https://github.com/nan-mu/libbpf-mcu/releases/tag/v0.1.1) 下载原始 12 个 7z。tag 指向 `07a4ea9a81a7fedf7bef2d6ced8d7fcfcccfd113`。从同一 Release 的资产元数据取得清单，并独立比对实际下载文件。规格用该 classifier head 的 `make_specs.py`、旧任务书附件的 23 组输入和完整期望，以及其固定的上游 C host 入口生成。旧附件为 `classifier-release-elf-taskbook.zip`，SHA-256 为 `64e25d28e27daffb5c3df264749e95c79da808895195be04413aea8c58208e8f`。该附件中的历史 7z 和离线容器仅用于对照。可查 [原任务书与规格输入](https://chatgpt.com/library?file_id=libfile_7e0ade78d60c819189063d8a7af5f0a1&account_id=personal)。

运行 `tooling/rbpf/analyze.py release --tag v0.1.1 --assets <原始发布目录> --digests <同版摘要清单> --specs <由 make_specs.py 生成的规格> --seven-zip 7zz --out <新目录>`。使用原 Release SHA-256、v3 索引、真实容器、Rust inspector 和模型执行。命令退出 0，`summary.json` 中 12 条为 `analyzed`，23/23 个具体向量通过。

| 程序 | rBPF 容器字节 | 具体向量 | 正式 7z 的 SHA-256 |
| --- | ---: | ---: | --- |
| `bsort` | 4336 | 2/2 | `e674f13bd6f2726922334e3058a5f106032d62bd94b040c2dfe0f3ca02119d5c` |
| `case_mark` | 1148 | 2/2 | `a94b68dd0461ad49e491756c56479c06a537b9e37904185dfaba8df1001c4881` |
| `case_swap` | 1148 | 2/2 | `f6244ceb52afb1bdfff818ce49c6e77c3f8fa881831c95da1d0ed2a8b7d29406` |
| `copy` | 3040 | 2/2 | `6b352e225d68af4ab04334ac7d666913ac5b396429027735af3ab4a6d9e0900e` |
| `firewall` | 516 | 2/2 | `72980d4d48058dd6209805ecdf3f3135baa39fff342e35b026ca8f007cdd2ea3` |
| `fletcher32` | 3340 | 2/2 | `aef8d3499bb45b5b29ae9d1c1b60745c1e7a8dfde835128cdf163da71c4e817e` |
| `just_drop` | 316 | 1/1 | `b6273506fa2e3e90bb4d9b4a610930f863212aa5aceae16c7621f45e9dbfb209` |
| `just_tx` | 1100 | 2/2 | `4288a9611cd12b3759c9d1256304a68d855ce3df7e13ad9ffb564fe8a3fe34a8` |
| `log2` | 4448 | 2/2 | `c33c0e5dfaf5437f9abde138f900235dfc78fde538e1c26e8d5ea348f14bd950` |
| `noop` | 2304 | 2/2 | `e288c29d5300357d87a5a5d8706a4eda750cf08a66b47de442fe4c17fadae30c` |
| `prime` | 2904 | 2/2 | `69102a43933888e96a7722e355475b14ac30bd70f718adf688efbef5ac055beb` |
| `strcmp` | 3880 | 2/2 | `710e1a699c1c3c984df16f939d23c9f182e808a4c95660a6fc194999c6986730` |

现有 56 个 `cases` 产生 53 个 `holds` 和 3 个预期反例。case_mark 的错误预期 2 被实际写入 1 推翻。case_swap 的错误预期 1 被实际写入 2 推翻。firewall 的错误计数预期 0 被实际值 1 推翻。三组反例均完成内部重放。三个结果均可复用到等价的代码、输入和模型。53 个 `holds` 中旧的 `log2/scale-over-limit` 只覆盖错误长度。另有 [EXB2 范围边界](log2-scale-boundary.md) 的历史调查。

逐程序取实际 `.xpost.image` 与离线容器对比，12/12 镜像字节相同，map 的逻辑名称、类型、容量及键值布局相同。`just_tx` 的 `rxcnt` VMA 从离线的 `0x40380388` 变为正式产物的 `0x40380390`。正式归档上的动作、包与计数规格均通过，证明该输入经现有 map 描述符路径可以分析。该验证不涉及设备执行。

上述执行实测覆盖旧 Python + Z3 后端的 rBPF 容器链路。其动作、包和 map 结果可作行为对照。原始归档 SHA-256 和对象检查可复用，本轮正式 angr CLI 的完整向量重放仍待验收。旧 `v0.1.0` 的 12 条缺件指当时缺 rBPF 容器的记录。

## 正式验收的规格输入

开工先从 [原任务书与规格输入](https://chatgpt.com/library?file_id=libfile_7e0ade78d60c819189063d8a7af5f0a1&account_id=personal) 获取原任务包，或使用 T3 上已有的 `/tmp/classifier-release-elf-taskbook.zip` 或其相同 SHA-256 的本地副本。摘要为 `64e25d28e27daffb5c3df264749e95c79da808895195be04413aea8c58208e8f`。其中 `evidence/vectors/` 是 23 组向量与独立期望，`evidence/angr_ebpf/`、`evidence/symbolic.py`、`evidence/requirements-symbolic.txt` 是 Heimdall 原型、演示和依赖。

直接从 `evidence/vectors/` 读取 23 组原输入和已保存的期望，规格适配可以复用 `tooling/rbpf/make_specs.py` 中现有的向量读取逻辑。旧生成器还会额外创建 EXB2 协议边界用例，并依赖 `ef1771d9c949771c707b93fd9da5c3e2602efee0` 的 C host。该批附加用例与 C host 重跑属于历史验证。本轮分析输入取 v0.1.1 正式发布对象。

原任务包无法取得、摘要不符或 23 组向量不完整时，按 [停止条件](../taskbook.md#开工与验收停止条件) 请用户介入。空包 `just_drop` 只能验证最小链路，完整验收需实际运行全部 23 组。
