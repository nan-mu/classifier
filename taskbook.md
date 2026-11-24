# classifier PR9 · 复现 HEIMDALL 并隔离正式分析工具

在 [nan-mu/classifier#9](https://github.com/nan-mu/classifier/pull/9) 的实际 head 上建立独立 worktree，沿用 `agent/release-elf-analysis`，目标为 main。审核基线为 `0c1d2a962624dee91dabd10a841f9164d61626b2`，上一轮 Gitea 任务书为 `7e4916149f71a136a5b7e0e65383337399cc3656`。分别记录开工 PR head 和本轮任务书提交。如 head 已变化，先核对是否影响本轮要求，不覆盖其他工作。

## 目标

将原始 eBPF ELF 的正式分析建立在 HEIMDALL 论文及公开实现的完整执行框架上，迁移到独立的 `tooling/angr/`。本轮只建立可信、可复跑的分析基础，保留原有 XDP 输入域、观察结果和验收，不扩展 Map 模型或定义新的可观察行为等价关系。

### 1. 复现上游并定位差异

用 `diagnosing-bugs` 阅读 [HEIMDALL 论文](https://arxiv.org/html/2605.25411v1) §3.2、§3.3 及相关附录，固定 [上游实现](https://github.com/vdasu/heimdall/tree/90b4605e1c6ddae7ae5ead9738d5c1ff8e2843ad) 的提交 `90b4605e1c6ddae7ae5ead9738d5c1ff8e2843ad`。先按上游原生入口复现至少一个已验证的程序对，记录装载、初态、路径探索、退出状态、公式和等价性结果。不要用修改后的 classifier 代替上游复现。

重点核对上游 `angr_ebpf_backend/angr_ebpf/` 的 loader、architecture、lifter、SimOS 和 helper 实现，以及 `c2rust_translation/generate_formula.py`、`verify_equivalence.py`。当前正式后端已实际调用 angr，但自行通过 blob、XdpWorld 和 successors 循环组织执行；七项旧回归测试仍走 Machine。静态依据见 [审核记录](tests/heimdall-review.md)。本轮需要改变的是方法复用与测试路径，不是仅把后端名称改为 angr。

### 2. 正式链路采用上游方法

用 `implement` 接通 CLE eBPF ELF backend、archinfo architecture、VEX lifter、SimOS/helper models、SimulationManager 和公式生成方法。直接复用上游适用实现；仅对 libbpf-mcu XDP ABI、ELF 重定位/BTF map 绑定、有限输入域及观察输出做必要适配。逐项记录上游代码、适配理由及验证，不另造平行执行器。上游不适用或无法复现时停止并报告，不自行退回 blob 或旧 Machine 路线。

单对象与 release 批处理共用正式装载及执行逻辑。正式输入仍为 v0.1.1 原始 7z、SHA-256 清单及 v3 index.toml 的 bpf.path；不依赖 rBPF mode 或容器。保留归档、索引、成员和对象校验，以及程序级来源、入口、绑定、后端版本和预算。初态按现有 XDP 契约设置 context、packet、stack 和有限 HASH/ARRAY，只支持本批所需的 map_lookup_elem。保留路径条件、32 位动作、有效包范围和完整字节、context、map 初终态、有序 helper 和写入事件（指令位置、资源、偏移、宽度和值）。helper 键取自调用时刻。Map 未声明键的现有约定不变。

### 3. 隔离目录并维护文档

正式入口、依赖锁定、上游来源及许可证、XDP 适配、测试和说明集中于 `tooling/angr/`。正式路径不依赖旧 Python/Z3 Machine，也不在失败时回退。历史 Compact ELF 分析保留为独立对照；不得因迁移破坏其现有用途。删除迁移产生的重复实现、过期入口及失效引用。

逐一核对仓库根 README、tooling/README.md、tooling/rbpf/README.md、doc/、实际调用脚本、已有规格和事实文档（如存在）。更新仍有用途的文档，使入口、目录、依赖、职责、适用版本和复跑命令与当前实现一致；删除已失效且无独立用途的文档。历史实验与审计记录保留原始版本及观察，不改写成新结果；对可能误导当前使用者的历史说明明确标注适用版本和替代入口。不要新增重复事实文件或另造术语系统。交付报告列出更新、删除及保留的相关文档与原因，检查正常入口不再引用迁移前路径。

### 4. 新后端语义与判定

用 `tdd` 从真实 ELF、正式装载、实际 angr 执行到公式/报告建立长期回归测试。旧 Machine 通过、mock 或仅检查后端名称不能作为新后端证据。

- 依据 [RFC 9669](https://www.rfc-editor.org/rfc/rfc9669.html) 检查 ALU32/64 的 DIV/MOD 零与非零除数（含符号除数），以及本批支持的 END、符号扩展和条件分支；不支持的合法形式须明确拒绝或未判定，不得误算。特别核对 ALU32 的高位清零。合法 MOV 得到正常结果，非法保留字段得到拒绝或未判定。
- 有限符号循环正常退出；预算耗尽保留未覆盖输入。未建模指令/helper、无法解析的内存访问、未定义数据不能产生错误的成立结论。
- 检查调用时刻的 helper 键、map 值指针写入、包内写入及退出有效包范围。沿用现有观察定义，不在本轮定义写入事件等价。
- 参照上游路径公式构造方法，保留输入域非空、正常退出覆盖、规格覆盖、规格否定式与反例复放。检查正常路径完整性和互斥性；声明域内仍存在可达未完成、异常、超时或预算缺口时，不得报告 holds。未判定的可达性本身不能被当作不可达。保存可复算 SMT-LIB。

### 5. 正式验收

原始输入及独立期望见 [发布记录](tests/release-v011.md)，旧轮实测见 [PR 审计](https://github.com/nan-mu/classifier/blob/0c1d2a962624dee91dabd10a841f9164d61626b2/.audit/taskbook/mcp/classifier/7e4916149f71a136a5b7e0e65383337399cc3656.md)。核对原任务包 SHA-256 `64e25d28e27daffb5c3df264749e95c79da808895195be04413aea8c58208e8f`、发布归档和 23 个独立期望；复用仍一致的静态资产及期望，不复用旧执行结果作为新后端通过证据。

- 真实 v0.1.1 的 bsort、case_mark、case_swap、copy、firewall、fletcher32、just_drop、just_tx、log2、noop、prime、strcmp 全部进入新正式路径；23/23 个原具体向量通过，比较动作、完整有效包和适用的 map/helper 行为。验证缺 rBPF 成员仍可分析，损坏、摘要错误及 map 绑定失败有定位。
- case_mark/case_swap 的 81/82 字节域、偏移 74 任意、匹配 TX 并在偏移 77 写 1/2，否则 PASS；交换期望产生两个可复放反例。firewall 的符号存在位与旧值：命中 DROP 且加一，否则 PASS；错误计数规格产生第三个可复放反例。保留原 just_tx 键、MAC、短包及 u32 回绕检查。
- 七个 EXB2 程序使用原合法/短请求向量，核对完整有效包、状态、轮数、结果、摘要及 scratch；copy 预算为零时报告未覆盖。
- 完成新后端语义回归、独立 Z3 复算（核对本轮实际生成的查询，不固定旧查询数量）、历史入口兼容检查和文档引用检查。

just_drop 单项仅为冒烟。no_spec、历史结果及跳过项不计入正式验收。必需输入缺失、摘要不符、上游复现失败、XDP ABI 冲突、正式验收意外失败/未判定时停止推进，报告版本、入口、预期、实际和所需决定。刻意设置的反例与预算缺口按其预期验收。

## 不在本轮实施

完整符号 Map 模型、Map 等价、写入事件等价、跨架构统一状态、无界循环证明、其他架构后端及 C-to-Rust 迁移。保留现有输出供后续独立 PR 使用，不创建或实施后续研究任务。

## 交付

用 `code-review` 核对上游方法与正常入口、适配边界、实际测试路径、失败判定、目录及文档；主代理执行剩余验收。用 `pr` 经指定 GitHub MCP 更新同一 PR9，记录上游复现、新跑结果、复用证据、限制、文档处置和最终 head。保持开放待维护者审核；通过审核后再合并至 main，不在本轮自行合并或创建后续实现 PR。
