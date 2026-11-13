# Audit: alive2-ebpf

任务书：本轮 `/poteto-delivery` 参数中的《Alive2 机器码前端适配与符号执行可行性验证任务书》，无后续修订。
PStack：`/Volumes/SSD/.claude/plugins/cache/cursor-plugins/pstack/0.15.36` v0.15.36，playbook `session-pickup` → `autonomous-run`。
Base：`main`　Branch：`agent/alive2-ebpf`　PR：见本文件末尾交付记录。

工作区说明。本任务在独立 worktree 的 `agent/alive2-ebpf` 分支上完成，路径见下方交付记录。主 checkout 里 `profile.toml` 和 `tooling/` 的 5 个改动属于另一个任务，本轮不碰，提交按 `alive2/` 与 `.audit/alive2-ebpf.md` 路径限定。

清单存放说明。本文件是可提交的需求清单，位于 `.audit/alive2-ebpf.md`。仓库 `.gitignore` 已移除对 `/.audit/` 的整体忽略，改为只忽略 `/.audit/*.tsv` 与 `/.audit/__pycache__/`，所以决策轨迹 `.audit/alive2-ebpf.tsv` 仍留在本地。`.audit/` 下其他任务的文件不在本轮提交范围内。

复核方式。需求一致性由 agent 逐行阅读任务书与本清单、对照真实产物自主判断，不由脚本判定。`audit-check.sh` 之类的表格解析只能数 `yes` 的个数，不能判断某行是否真的被对应测试覆盖，因此不作为验收依据。

上游：`https://github.com/AliveToolkit/alive2` commit `adacbd5180ccf95075e9867c4f0c259f59c9fef2`。
ISA 规范：Linux v6.12 `Documentation/bpf/standardization/instruction-set.rst`，取自 `https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/plain/Documentation/bpf/standardization/instruction-set.rst?h=v6.12`。

## 退出判据

1. `alive2/bootstrap.sh` 从零配置并构建可执行文件，全部测试退出码 0。
2. 解码器接受的每个 opcode，在 ISA 定义的每种宽度下，都有独立参考的符号等价 UNSAT 行和边界点扫描。
3. 随机差分测试跑满约定轮数且无差异，反例保存路径可用。
4. 反向测试抓住任务书点名的 4 类错误转换，以及新增语义对应的错误。
5. D1/D2/D3 用真实机器码跑通，展开上限效果和未覆盖行程有记录。
6. 本文件每行 Implemented/Verified 为 yes 且有证据，或明确记为未达成并写明原因。
7. `feasibility-report.md` 回答任务书第九节第 5 项的 6 个问题，含修改记录与样例。
8. Draft PR 就地更新，阶段评论按 head SHA 去重；全部验收通过才转 Ready。

## 需求清单

| # | 需求（任务书） | Implemented | Verified | Evidence | Open issue |
|---|---|---|---|---|---|
| A1 | 克隆 Alive2 官方仓库并记录完整 commit SHA | yes | yes | `alive2/UPSTREAM.txt:4-6` | — |
| A2 | 按官方 README 装依赖并构建成功 | yes | yes | `alive2/bootstrap.sh`；本轮移走两个 build 目录后从零构建成功，重跑不重复打补丁 | — |
| A3 | 回答如何直接构造内部 `Function` | yes | yes | `feasibility-report.md` 第二节；`ir/function.h:118,154,174`；`src/ebpf_run.cpp:45-47` | — |
| A4 | 回答如何向 `BasicBlock` 加指令并连控制流 | yes | yes | `ir/function.h:50,146`；`src/ebpf_lift.cpp` 的 `emit`/`fill_phis` | — |
| A5 | 回答独立符号执行入口 | yes | yes | `util/symexec.h:11`、`util/symexec.cpp:78`；`src/ebpf_run.cpp:65-66` | — |
| A6 | 回答如何取返回值、路径条件、定义性、符号内存 | yes | yes | `ir/state.h:201,361,363`；`src/ebpf_run.cpp:67-82` | — |
| A7 | 回答执行入口是否隐含依赖 LLVM 转换器元数据 | yes | yes | `src/ebpf_run.cpp:14-33`；`ir/state.cpp:310`；报告第二节列出必须手工初始化的 globals | — |
| B1 | `x + y*3` 符号输入，全 32 位 SMT 检查，含溢出 | yes | yes | `direct-ir.log` 12 条求解检查；`x+y*4` 对照 SAT | — |
| B2 | `x > 10` 分支，SMT 证明与条件表达式等价 | yes | yes | `direct-ir.log` 分支等价 UNSAT | — |
| B3 | 最小内存写读，符号内存更新、读回值、有效性与 UB 条件可取 | yes | yes | `direct-ir.log` 三条 memory 检查 UNSAT | — |
| B4 | 独立可执行程序输出 7 段结果，保留 SMT 表达式对象 | yes | yes | `src/direct_ir.cpp`；`src/ebpf_check.cpp` 的 `print_sample`；`src/ebpf_run.cpp:74-85` 保留 expr | — |
| C1 | 真实编码解码：opcode/class、dst/src、立即数符号规则、地址与跳转目标 | yes | yes | `src/ebpf_decode.cpp:34-175`；规范例子测试 PASS | — |
| C2 | 不支持的指令明确报错，不静默跳过或当空操作 | yes | yes | `ebpf-test.log` "unsupported encodings" 段 14 例，各带错误原因 | — |
| C3 | MOV/ADD/SUB 基本运算与 32/64 位语义 | yes | yes | 矩阵 `alu32/alu64 mov/add/sub` 各 3 例，等价 UNSAT + 边界扫描 | — |
| C4 | MUL 有限位宽乘法与溢出 | yes | yes | 矩阵两种宽度；`mul (max+3)*2 wraps to 4` PASS | — |
| C5 | DIV/MOD 除零等特殊行为 | yes | yes | 矩阵 div/mod/sdiv/smod 两种宽度两种来源；`sdiv64 INT_MIN / -1 wraps`、`smod64 INT_MIN % -1 is 0` PASS | — |
| C6 | LSH/RSH/ARSH 移位掩码与有符号行为 | yes | yes | 矩阵两种宽度；`lsh 127 masks to 63`、`arsh sign fill`、`rsh zero fill` PASS | — |
| C7 | JEQ/JNE/JA 条件跳转与 CFG | yes | yes | 矩阵 `jmp/jmp32 jeq/jne` 各 3 例；`jmp ja`、`jmp32 ja` PASS | — |
| C8 | EXIT 程序终止与返回值 | yes | yes | 矩阵 `jmp exit` 独立行 PASS | — |
| C9 | AND/OR/XOR 等简单指令 | yes | yes | 矩阵两种宽度两种来源各 3 例 | — |
| C10 | 支持被测程序涉及的寄存器，明确 r0 为返回值 | yes | yes | `src/ebpf_lift.cpp:172-183,264` | 未初始化寄存器建模为 0，报告第六节声明 |
| C11 | 寄存器多次写入的 SSA 版本化与 phi 合并 | yes | yes | `src/ebpf_lift.cpp:232-249,407-421`；branch 样例 IR 的 `%b3_r0` phi | — |
| C12 | ALU32 如何更新 64 位寄存器、高 32 位如何处理 | yes | yes | `src/ebpf_lift.cpp:295-300`；`alu32 clears high bits` PASS；93 条 ALU 矩阵行含 47 条 ALU32 | — |
| C13 | ALU64 的 32 位立即数如何扩展 | yes | yes | `src/ebpf_lift.cpp:84-88,287`；spec:383-391,408-410；`imm without sign extend is caught` SAT | — |
| C14 | 算术溢出按固定宽度回绕 | yes | yes | `mul (max+3)*2 wraps to 4`、`sdiv64 INT_MIN / -1 wraps to INT_MIN` PASS | — |
| C15 | 无符号 DIV 除零结果为 0 | yes | yes | `div zero` PASS；`div zero as ub is caught` SAT | — |
| C16 | MOD 除零保留目标寄存器值 | yes | yes | `mod zero keeps dst`、`mod32 zero clears high`、`smod64 zero divisor keeps dst` PASS | — |
| C17 | 移位量按 32/64 位掩码 | yes | yes | 矩阵两种宽度；`lsh 127 masks to 63` PASS；`shift without mask is caught` SAT | — |
| C18 | 算术右移、逻辑右移、有符号比较正确区分 | yes | yes | `arsh sign fill`、`rsh zero fill`、`jsgt`/`jgt` PASS；矩阵 10 个比较 × 2 宽度 | — |
| C19 | 优先用现有 IR 指令组合表达 ISA 语义 | yes | yes | `src/ebpf_lift.cpp` 的 `emit_divmod` 用 icmp+br+phi；`emit_movsx` 用 trunc+sext | — |
| C20 | 语义扩展按顺序尝试：先用现有 IR 组合，不足才做最小扩展并附独立测试 | yes | yes | 第一步即充分：除零/溢出用 icmp+br+phi，MOVSX 用 trunc+sext，移位用 and+shift；未新增 `toSMT()`，报告第七节声明 | 若后续内存建模需要扩展，在此登记 |
| D1 | 直线程序：真实机器码 → IR → 符号执行 → 结果 | yes | yes | `ebpf-test.log` mul/div/mod/shift 程序；6 个 Clang 端到端程序 | — |
| D2 | 条件跳转：恢复 CFG、SSA 关系、等价路径条件与返回表达式 | yes | yes | `ebpf-test.log` "sample conditional program" 六段产物 | — |
| D3 | 有限循环：调用 Alive2 已有展开机制，不手工展开机器码 | yes | yes | `src/ebpf_run.cpp:50-56` 调 `fn.unroll`；`ebpf-test.log` unroll 1/4 | — |
| D4 | 回边识别、展开配置生效、不同上限结果变化、越界路径处理 | yes | yes | `src/ebpf_lift.cpp:116-117`；两种 CFG 形状各测 unroll 1/4：头块判断退出得 `k+1` 行程，回边为条件跳转得 `k` 行程；`larger unroll covers more trips`、`some trips stay outside the bound` 各 2 条 PASS | 上一轮的 `k+1` 通用推测已被第二种形状否定 |
| D5 | 不把未覆盖路径称为已验证 | yes | yes | `src/ebpf_test.cpp` 的 `returns_at` 按 return domain 判定；报告第五节 | — |
| E1 | 每条支持指令有独立参考模型，依据固定版本官方规范 | yes | yes | `src/ebpf_ref.cpp` 只包含 `ebpf.h` 与 `smt/expr.h`，无 lifter 包含或调用；具体解释器 + 独立 Z3 模型；156 例矩阵逐 opcode 对照 | 解码器 `ebpf_decode.cpp` 为两侧共享，无独立第二实现；报告第六节记为共模风险 |
| E2 | `valid_input ∧ (Alive2 ≠ Reference)` 交由 SMT 判定 | yes | yes | `src/ebpf_check.cpp` 的 `expect_equiv` | — |
| E3 | UNSAT 才算通过；SAT 存反例；UNKNOWN/超时不得报成功 | yes | yes | `src/ebpf_check.cpp` 的 `check` 区分 UNSAT/SAT/TIMEOUT，SAT 落盘 `counterexamples/`；本轮 8 个反例文件对应 8 类反向测试 | — |
| E4 | 反向测试：ADD 当 SUB | yes | yes | `add as sub is caught SAT` | — |
| E5 | 反向测试：ALU32 当 ALU64 | yes | yes | `alu32 as alu64 is caught SAT` | — |
| E6 | 反向测试：eBPF 除零当 UB | yes | yes | `div zero as ub is caught SAT` | — |
| E7 | 反向测试：条件跳转目标设错 | yes | yes | `bad jump is caught SAT` | — |
| E8 | 具体边界输入补充交叉验证 | yes | yes | `expect_at` 系列 + `expect_sweep` 边界扫描，单输入 12 点、双输入 144 点 | — |
| E9 | 随机输入补充交叉验证 | yes | yes | `check_random_differential(120, 0x5eed1234)`；240 条 PASS，每程序 24 随机点 + 12 边界点 | 随机程序只含前向跳转，循环由 D3 单独覆盖 |
| E10 | 已有 eBPF 测试向量补充交叉验证 | yes | yes | `alu32 bytes match clang -target bpf` PASS；6 个 Clang 编译程序的 `.text` 字节 | — |
| E11 | 可选：Clang BPF target 的 C → 机器码端到端 | yes | yes | `tests/run-clang-e2e.sh` 现场编译 `tests/bpf/*.c`，`llvm-objcopy` 提取 `.text`，`clang-e2e.log` 6 PASS 0 FAIL | — |
| R1 | 交付可运行代码与 Alive2 构建/依赖配置 | yes | yes | `bootstrap.sh` 从零构建实测通过；Z3 路径经 pkg-config/brew 探测，不再硬编码 | — |
| R2 | 自动化测试覆盖算术、位宽、除零、移位、条件跳转、路径合并、循环边界 | yes | yes | `tests/run-all.sh`：687 PASS 0 FAIL + 12 求解检查 + 6 端到端 | — |
| R3 | 明确记录哪些测试成功、失败、尚未实现 | yes | yes | `feasibility-report.md` 第一、六节；14 例拒绝测试列出未实现 opcode | — |
| R4 | 符号结果样例含 6 段产物 | yes | yes | `ebpf-test.log` "sample conditional program"；报告第八节 | — |
| R5 | 修改记录区分复用/新前端/扩展语义/改上游 4 类 | yes | yes | `feasibility-report.md` 第七节四类分列 | — |
| R6 | `feasibility-report.md` 回答 6 个研究问题 | yes | yes | 报告第三、四节（无损映射/额外建模）、第五节（复用程度）、第九节（结构性问题）、第十节（下一阶段工作量与风险） | — |
| R7 | 区分已实验验证的结论与未验证推测 | yes | yes | `feasibility-report.md` 第十一节逐条分列；第五节标注 `k+1` 未证明；第六节声明未对照真实执行器 | — |
| W1 | 隔离实验代码，记录上游 commit，不改 classifier/XPOST 主线 | yes | yes | 分支 `agent/alive2-ebpf`；`UPSTREAM.txt`；提交按 `alive2/` 限定，未碰 `profile.toml` 与 `tooling/` | 工作区复用见文件开头说明 |
| W2 | 需求清单持续复核 | yes | yes | 本文件；实现前、阶段收尾、提交前各复核一次 | 交付前再复核一次 |
| W3 | 一个 Draft PR 就地更新，阶段评论按 SHA 去重 | yes | yes | PR #5 `https://github.com/nan-mu/classifier/pull/5`，Draft，base `main`，head `agent/alive2-ebpf`；经 GitHub MCP 创建并 link | 阶段评论按 head SHA 去重 |
| W4 | 不合并、不 force push、不清理 worktree | yes | yes | 本轮无此类操作 | 合并由用户在 GitHub 执行 |

## 人工复核记录

复核由 agent 阅读任务书与本清单、对照真实产物完成，不依赖脚本判定。本轮实际读过的核对动作：

- 逐条比对 `ebpf_decode.cpp` 接受的 opcode 集合与 `isa_matrix()` 生成的集合。ALU 侧 9 个通用 switch 分支加上 NEG、DIV/SDIV、MOD/SMOD、MOV/MOVSX 四个特判，共 18 个操作族；JMP 侧 10 个比较加上 JA、EXIT。矩阵 93 条 ALU + 60 条条件跳转 + 3 条 JA/EXIT = 156，与日志 `matrix cases 156` 一致，无遗漏族。
- 读 `ebpf_ref.cpp` 与 `ebpf_ref.h` 的包含与调用，确认只有 `ebpf.h` 和 `smt/expr.h`，不含 lifter、不调用 `lift_ebpf`。同时发现解码器为两侧共享，已记入 E1 的 Open issue 与报告第六节。
- 读 `ebpf-test.log` 的两种循环形状覆盖行，确认头块判断退出得 `k+1`、回边为条件跳转得 `k`，与报告的否定结论一致。
- 读 `direct-ir.log` 的 `x + y * 4` 对照行为 SAT，确认等价查询不是恒真。
- 对照 kernel.org 取回的 v6.12 规范第 330-354、383-399、424-425 行，核对除零、有符号溢出、立即数扩展、移位掩码四类语义。

## 交付记录

PR：https://github.com/nan-mu/classifier/pull/5 （Draft，base `main`，head `agent/alive2-ebpf`）。经 GitHub MCP 创建，已 link 到本线程。

工作区：独立 worktree `/Volumes/SSD/bs/classifier-alive2-ebpf`，分支 `agent/alive2-ebpf`，经 `EnterWorktree` 绑定。主 checkout 已切回 `main`，其 `profile.toml` 与 `tooling/` 的 5 个未提交改动原样保留，未被本轮触碰。

可移植性实测：该 worktree 不含任何构建产物，仅凭已提交文件跑 `bash alive2/bootstrap.sh` 从零构建成功（8.7 秒墙钟，退出码 0），随后 `bash alive2/tests/run-all.sh` 复现 687 PASS 0 FAIL、12 条求解检查、6 个 Clang 端到端。迁移没有依赖工作区外的状态。

复核入口：`bash alive2/tests/run-all.sh`。构建入口：`bash alive2/bootstrap.sh`。

结论：Conditionally feasible。详见 `feasibility-report.md`。

合并由用户在 GitHub 执行，本轮不合并、不 force push、不清理 worktree。