# Alive2 能否执行 eBPF 机器码

**结论：Conditionally feasible。** 符号执行器、CFG、phi 合并和有界循环展开都能绕过 LLVM 前端使用。真实 eBPF 机器码已经能转成 Alive2 内部 IR 并得到符号表达式，且与独立 ISA 参考模型交叉验证一致。代价是每条与 LLVM 语义不同的 eBPF 指令都要在前端显式改写，不能靠同名运算。eBPF 内存指令、helper、Map 和 RV32IMC 本轮没有做。

上游 commit `adacbd5180ccf95075e9867c4f0c259f59c9fef2`。ISA 对照 Linux v6.12 `Documentation/bpf/standardization/instruction-set.rst`，取自 kernel.org 的 v6.12 tag。目录 `classifier/alive2/` 是 classifier 仓库里的普通目录，不是 submodule。

复核入口是 `bash tests/run-all.sh`。它重新生成三份日志并打印计数。日志的字节内容不是判据：Alive2 按指针哈希排列 SMT 合取项，同一份代码两次运行的文本顺序会不同。判据是退出码和 PASS/FAIL 计数。

## 一、本轮结果

| 项目 | 结果 |
|---|---|
| `direct_ir` 求解检查 | 12 条，0 失败 |
| `ebpf_test` | 695 PASS，0 FAIL |
| 逐 opcode ISA 矩阵 | 156 例（93 条 ALU，60 条条件跳转，3 条 JA/EXIT） |
| 随机差分 | 120 个程序，种子 `0x5eed1234`，每个 24 个随机点加 12 个边界点 |
| Clang C → eBPF 端到端 | 6 个程序全部通过 |
| 反向测试 | 8 类错误转换全部被抓到（SAT） |
| 不支持编码的拒绝 | 14 例，全部给出明确错误原因 |

矩阵按 v6.12 的 opcode 表生成，不是手写程序清单。ALU 覆盖 18 个操作族在 ALU32/ALU64 两种宽度、立即数/寄存器两种来源下的组合，立即数取 `-1` 和 `0x40000001` 两个值。条件跳转覆盖 10 个比较操作在 JMP/JMP32 两种宽度下的组合。每例做两件事：全输入域符号等价（UNSAT），以及一次覆盖全部边界点的求解查询。

边界点集合是 `0, 1, 2, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x1ffffffff, 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff, 0xdeadbeefcafebabe`。单输入程序扫 12 点，双输入程序扫 144 点。整个扫描是一次求解查询，形式是所有"Alive2 与独立解释器不一致"的点的析取。

## 二、阶段 A：执行接口调查

以下行号指 `third_party/alive2/`。

**如何直接构造内部 `Function`。** `ir/function.h:118` 的构造函数只需要返回类型和名字，指针位宽和端序有默认值。`src/ebpf_run.cpp:45-47` 就是这样用的。输入用 `Function::addInput`（`ir/function.h:174`），常量用 `addConstant`（`ir/function.h:154`）。两者都接管 `unique_ptr` 所有权。

**如何加指令并连控制流。** `BasicBlock::addInstr`（`ir/function.h:50`）接管指令所有权。块用 `Function::getBB(name)`（`ir/function.h:146`）按名字创建或取得。控制流是 `Branch` 指令，无条件版指向一个块，条件版指向两个块。汇合点用 `Phi`，`Phi::addValue(value, from_block_name)` 按前驱块名登记。`src/ebpf_lift.cpp` 的 `emit` 和 `fill_phis` 是完整用例。

**独立符号执行入口。** `util/symexec.h:11` 的 `util::sym_exec(State&)`。它不引用任何 LLVM 头。构造 `IR::State(fn, true)` 后直接调用即可，见 `src/ebpf_run.cpp:65-66`。

**如何取结果。** `State::returnVal()`（`ir/state.h:363`）返回一个 `ValTy`，其中 `val.value` 是返回值表达式，`val.non_poison` 是非 poison 条件，`domain()` 是定义性/UB 条件，`return_domain`（`ir/state.h:201`）是返回条件。符号内存用 `State::returnMemory()`（`ir/state.h:361`）。`src/ebpf_run.cpp:67-82` 把这五项全部取出并保留为 `smt::expr` 对象，文本输出只用于人工检查。

**是否隐含依赖 LLVM 转换器的元数据。** 不依赖 LLVM 库，但依赖一组全局变量，正常路径下由转换器设置。`src/ebpf_run.cpp:14-33` 的 `configure_pure_alu()` 显式把 `num_locals_src`、`num_nonlocals`、`has_fncall`、`has_alloca`、`observes_addresses` 等设为纯算术程序的值，并调用 `IR::State::resetGlobals()`（`ir/state.cpp:310`，内部转调 `Memory::resetGlobals()`）。不做这一步，默认块数量会把纯算术程序的定义性条件撑得很大。这是调用约定，不是 eBPF 内存语义。

构建用 `bootstrap.sh`，它配置并编译上游（`-DBUILD_TV=OFF`，只链接 `ir`、`smt`、`tools`、`util`，不链接 LLVM），再编译三个可执行文件。本轮实测从零构建成功，重复运行不重复打补丁。

## 三、哪些指令能无损映射

同名 LLVM 运算可以直接用的：`ADD`、`SUB`、`MUL`、`AND`、`OR`、`XOR`、`MOV`（寄存器源）、`NEG`（写成 `0 - dst`）。这些在固定宽度下都是回绕算术，Alive2 的 `add`/`sub`/`mul` 不带 NSW/NUW 标志时语义一致。10 个条件跳转直接对应 `icmp` 的 EQ/NE/UGT/UGE/ULT/ULE/SGT/SGE/SLT/SLE，再接 `br`。

`MOVSX` 用 `trunc` 到 8/16/32 位再 `sext` 表达，ALU32 形式末尾再 `zext` 回 64 位。不需要新指令。

## 四、哪些必须额外建模

以下每一项都有独立测试，且都有对应的反向测试证明测试不是恒真。

**ALU32 的宽度处理。** 先 `trunc` 到 32 位，运算后 `zext` 回 64 位。`r1 = 0x1ffffffff` 再做 ALU32 加 1 得 0。错做成 ALU64 时等价查询是 SAT。

**ALU64 立即数的符号扩展。** 规范第 383-391 行和 408-410 行：ALU64 的 `imm` 先从 32 位符号扩展到 64 位。无符号 `DIV`/`MOD` 也一样先符号扩展再按无符号使用，所以 `2^32 / -1` 得 0，因为除数是 64 位全 1。ALU32 的立即数按 32 位解释。去掉符号扩展的反向测试是 SAT。

**无符号除零。** 规范第 349-354 行：`DIV` 除零得 0，`MOD` 除零在 ALU64 保留目标寄存器、在 ALU32 把高 32 位清零。Alive2 的 `udiv`/`urem` 通过 `div_ub`（`ir/instr.cpp:213-221`）把除零记成 UB。前端先 `icmp eq src, 0` 再分支，只在除数非 0 的块里放 `udiv`/`urem`，汇合点用 phi。直接用 `udiv` 的反向测试是 SAT；分支之后除零输入上的定义性查询是 UNSAT。

**有符号除法的溢出。** 这是本轮新增的发现。`div_ub`（`ir/instr.cpp:218-220`）除了有除零 UB，还对 signed 情形加了一条：`a != IntSMin || b != -1`。也就是说 Alive2 把 `INT_MIN / -1` 记成 UB。eBPF 规范第 349-350 行说算术溢出按固定宽度回绕，所以 `SDIV(INT64_MIN, -1)` 应得 `INT64_MIN`。前端为此多加一条分支：除零、溢出、正常三种情况各一个块。实测 `sdiv64 INT_MIN / -1 wraps to INT_MIN` 通过，去掉该分支的反向测试是 SAT。

还有一处细节，本轮由独立复核查出并修复。Alive2 的 `expr::sdiv`（`smt/expr.cpp:757-758`）在两个操作数都是常量时把 `SMin / -1` 折叠成 0，既不是回绕值也不是 UB。前端的分支守卫让 `sdiv` 永远看不到这组操作数，所以 lifter 不受影响。但参考模型的符号实现原先直接调 `d.sdiv(s)`，在常量操作数下会继承这个错误折叠，与自己的具体解释器不一致。

这个缺陷原先测不出来。矩阵和随机程序的寄存器都是符号变量，`sdiv` 交给 Z3 的 `bvsdiv`，结果正确；而边界扫描比较的是 Alive2 与具体解释器，根本不调用符号参考。补上一个两操作数皆为常量的程序后，`expect_equiv` 立刻返回 SAT。修复方式是在符号参考里按规范先选出被除数，再让折叠结果落在不会被选中的分支上。现在 `sdiv64 constant INT_MIN / -1` 与 `smod64 constant INT_MIN % -1` 都有独立用例。

由此得到一条关于测试分工的准确说法：全输入域等价查询负责检查符号参考，边界扫描负责检查 Alive2 与 lifter 这一侧。两者覆盖不同的错误来源，任何一个都不能替代另一个。

**有符号取模。** 规范第 393-399 行要求截断除法（`-13 % 3 == -1`）。Alive2 的 `srem` 映射到 Z3 的 `bvsrem`（`smt/expr.cpp:786`），正是截断语义，不是 SMT-LIB `bvsmod` 的向下取整语义。`SMOD(INT64_MIN, -1)` 数学上是 0，实测通过。除零保留目标寄存器，与无符号 `MOD` 一致。

**移位掩码。** 规范第 424-425 行：64 位掩码 `0x3F`，32 位掩码 `0x1F`。Alive2 的 `shl`/`lshr`/`ashr` 把超范围移位量记成 poison（`ir/instr.cpp:298`）。前端先 `and` 再移位。`1 << 127` 得 `1 << 63`。去掉掩码的反向测试是 SAT。

**算术右移与逻辑右移、有符号与无符号比较。** `arsh` 用 `ashr`，`rsh` 用 `lshr`，在 `0x8000000000000000` 上结果不同。`JSGT` 把 `-1 > 0` 判为假，`JGT` 判为真。

**JMP32 的宽度。** 比较前把两个操作数都 `trunc` 到 32 位。`JMP32 JNE` 用 `r1 = 0x100000000` 和立即数 0 比较，低 32 位相等所以不跳；按 64 位比较则会跳，反向测试是 SAT。

## 五、CFG、路径合并和循环复用了多少

全部复用，前端没有自己实现这些机制。

基本块、边、phi 是 Alive2 原有的。前端只做三件事：按 leader 切块、把机器寄存器版本化成 SSA 值、在汇合点放 phi。`Function::topSort()` 处理无循环程序，`Function::unroll(k)`（`ir/function.h:227`）处理有回边的程序。前端没有手工展开机器码。

回边识别在 `src/ebpf_lift.cpp:116-117`：跳转目标不大于当前指令下标即标记为循环。

本轮测了两种 CFG 形状，结论是**覆盖行程数取决于循环形状，不是通用的 `k+1`**。

形状一，退出判断在头块、回边是 `JA`。程序是 `r0` 从 0 开始每次加 1，`r1` 每次减 1，直到 `r1` 为 0。实测：

- `unroll(1)` 覆盖行程 0 和 1，返回表达式 `(ite (= r1 0) 0 1)`。
- `unroll(4)` 覆盖行程 0 到 4。
- 行程 5 到 8 没有返回，`return domain` 为假。
- 覆盖行程数是 `k+1`，含行程 0。

形状二，先执行循环体、回边是条件跳转 `JNE`。程序是 `r0` 从 0 开始每次加 2，`r1` 每次减 1，`r1 != 0` 则跳回循环体。实测：

- `unroll(1)` 只覆盖行程 1。
- `unroll(4)` 覆盖行程 1 到 4。
- 覆盖行程数是 `k`，不是 `k+1`。
- 行程 0 在这个程序里本来就不终止：`r1` 从 0 减到 -1 后永远不等于 0。它没有被记成已覆盖，这是正确行为。

两种形状都满足：展开后的回边指向 `#sink` 而不是下一次迭代；返回条件同时要求输入不是 undef、不是 poison，并且行程落在展开范围内；更大的上限覆盖更多行程；仍有行程留在界限之外。

未覆盖的行程没有被记成已验证。判定方式是查询 `input_ok ∧ r1 == n ∧ ¬return_domain` 是否 UNSAT，只有 UNSAT 才算该行程被覆盖。

**上一轮推测已被本轮实验否定。** 上一轮只在形状一上测过，把 `k+1` 当成可能的通用关系记录下来。形状二的实测结果是 `k`，所以该推测不成立。推断的解释是退出判断相对回边的位置决定了头块被复制的次数，但这条解释本身没有进一步验证。使用者不应假设任何固定的行程数公式，而应逐程序查询 `return_domain`。

## 六、测试覆盖与未实现部分

**已通过。** 上面第一节的表格是本轮实测计数。逐 opcode 矩阵、随机差分、Clang 端到端、8 类反向测试、14 例拒绝测试全部通过。

**反向测试抓到的 8 类错误。** ADD 当 SUB、ALU32 当 ALU64、除零当 UB、跳转目标设错、有符号除法溢出当 UB、移位不加掩码、MOVSX 当零扩展、立即数不做符号扩展。每类的 SAT 模型落盘在 `counterexamples/`（该目录已 gitignore）。

**明确未实现，解码器报错而非当空操作。** 内存指令 `LDX`/`ST`/`STX`、`LDDW` 宽立即数、`CALL`（helper 和程序内调用）、`JSET`、字节交换 `END`、原子操作。14 例拒绝测试逐一验证了错误原因，见 `ebpf-test.log` 的 "unsupported encodings" 段。

**已知建模假设。** 测试标明的寄存器是符号输入，其余寄存器从 0 开始。这不是 Linux 验证器对未初始化寄存器的结论。纯算术程序把本地块和非本地块数量设成 0，这是调用约定。

**共模风险：解码器是共享的。** 参考模型不调用 lifter 的任何函数，`ebpf_ref.cpp` 只包含 `ebpf.h` 和 `smt/expr.h`，具体解释器和符号模型都是独立写的。但两者都消费 `ebpf_decode.cpp` 解出的 `EbInsn`。如果解码本身读错了某个字段，两边会一致地错，符号等价查询查不出来。任务书禁止的是复用 lifter 的核心实现，这一条没有违反；但解码层没有独立第二实现，这是本轮验证的真实边界。现有缓解是规范例子解码断言、14 例非法编码拒绝测试，以及 6 个 Clang 真实编译产物的端到端对照。要彻底消除这条风险，需要再写一个独立解码器做字节级对照，本轮没有做。

**未做的交叉验证。** 没有对照真实内核执行器或 JIT 跑过。正确性标准是 v6.12 规范文本，不是某个实现的行为。有符号除法溢出这一项尤其值得注意：规范说回绕，而 C 语言的 `INT64_MIN / -1` 本身是未定义行为，真实执行器在 x86 上可能触发 `idiv` 异常。本轮以规范为准，没有实测执行器，这是一条声明的限制而不是已验证的结论。

## 七、修改记录

**完全复用的 Alive2 组件。** `ir/` 的 `Function`、`BasicBlock`、`Instr` 及其子类（`BinOp`、`ICmp`、`ConversionOp`、`Phi`、`Branch`、`Return`、`Input`、`IntConst`）、`State`、`Memory`；`smt/` 的 `expr`、`Solver`、`check_expr`；`util/symexec` 的 `sym_exec`；`Function::unroll` 和 `Function::topSort`。符号执行算法、路径条件合并、循环展开算法一行未改。

**新实现的机器码前端。** `src/ebpf_decode.cpp` 解码，`src/ebpf_lift.cpp` 转 IR，`src/ebpf_run.cpp` 执行与结果提取，`src/ebpf_check.cpp` 共享断言，`src/ebpf_file.cpp` 字节码文件 CLI，`src/ebpf_test.cpp` 测试套件。

**独立参考模型。** `src/ebpf_ref.cpp` 含两个互不相同的实现：一个具体执行解释器（纯 C++ 整数运算，显式特判溢出），一个独立写的 Z3 位向量符号模型。两者都不调用 lifter 的任何函数。分工是：边界扫描把 Alive2 的符号结果与具体解释器在每个点上对照，全输入域等价查询把 Alive2 与符号参考对照。具体解释器不依赖 Alive2 的任何求值路径，所以它是常量折叠这类共享错误的裁判；符号参考则用了 Alive2 的 `smt::expr` 作为基底，本轮已经查出并修掉一处由它继承的折叠错误。

**必须扩展的 IR 指令语义。** 无。所有 eBPF 特殊语义都用现有 IR 指令组合表达，没有新增 `toSMT()`。

**对 Alive2 原有代码的修改。** 只有 `patches/clang-iterator.patch`，在 `ir/attrs.cpp`、`ir/function.cpp`、`ir/instr.cpp`、`ir/state.cpp`、`smt/exprs.cpp` 五个文件各加一行 `#include <iterator>`。这是 libc++ 的显式包含要求，不改变任何指令语义。补丁已应用于 vendored 树，`bootstrap.sh` 会检测并跳过重复应用。

## 八、符号结果样例

`ebpf-test.log` 的 "sample conditional program" 段是一个真实 eBPF 程序的完整六段产物。程序是 `if (x > 10) return x + 1; return x - 1;`。

解码结果、控制流结构、生成的 Alive2 IR、符号返回表达式、路径与定义性条件、参考等价结果都在该段里。核心结果是：

```
Symbolic return expression
(ite (bvule #x000000000000000b r1)
     (bvadd r1 #x0000000000000001)
     (bvadd r1 #xffffffffffffffff))
Path / definedness conditions
(and (= isundef_r1 #b0) np_r1)
```

控制流是 `b0 -> b2 or b1`、`b1 -> b3`、`b2 -> b3`、`b3 exit`，汇合点 `%b3_r0 = phi i64 [ %1, %b1 ], [ %2, %b2 ]`。与独立参考的不等价查询是 UNSAT。

另有 `build/ebpf_file <bytecode> --regs r1,r2` 可对任意原始字节码文件打印同样六段并做等价检查。`tests/run-clang-e2e.sh` 用它跑 Clang 编译出的真实 `.text`。

## 九、结构上会挡住完整 ISA 的地方

**除法和超范围移位的语义差是局部成本。** Alive2 把除零、有符号溢出、超范围移位记成 UB 或 poison，eBPF 把它们定义成回绕、掩码或除零结果。每条这样的指令都要在前端改写成分支或掩码。这个成本是局部的、可重复的，现有测试已经覆盖无符号除法、有符号除法、有符号取模和三种移位。没有理由认为它会阻止完整 ISA 支持。

**内存模型是真正的未知。** eBPF 的栈、包和 Map 还没有接到 Alive2 的内存模型上。现在只知道一条 `alloca` 能往返（`direct-ir.log` 的三条 memory 检查）。Alive2 的内存带块号、来源和 poison 字节。如果 eBPF 内存或 helper 不能用现有的 `load`/`store` 加显式边界条件表达，就要改 Alive2 的内存模型或执行状态。那一步超出前端适配范畴，本轮没有实验证据，属于推测。

**有界展开的返回域不是全程序证明。** 超出 `#sink` 的路径必须继续标成未覆盖。这一点已经在测试里强制，但任何上层使用者都必须尊重 `return_domain`，不能把有界结果说成完整验证。

## 十、下一阶段工作量与风险

以下是估计，不是实测。

**eBPF 内存指令（LDX/ST/STX）。** 工作量中等。需要把 eBPF 的栈帧和上下文指针映射到 Alive2 的内存块，并显式表达边界条件。风险在于 Alive2 的内存块模型是否能表达 eBPF 验证器的"已检查过的包范围"这类状态。若不能，触发任务书第八节情况二。

**helper 调用。** 工作量中等偏大，风险高。helper 是外部函数，语义不在 ISA 规范里。要么为每个 helper 写摘要，要么建模为未解释函数加约束。前者是逐个 helper 的持续成本，后者会丢失精度。

**Map。** 工作量中等，风险中等。Map 查找返回可能为空的指针，需要建模成分支加指针有效性条件。Alive2 的指针模型能否表达"查找失败"路径需要实验。

**LDDW 和 JSET。** 工作量小。LDDW 是 16 字节宽指令，解码器要处理指令跨槽；JSET 是位测试跳转，直接对应 `and` 加 `icmp ne 0`。

**RV32IMC。** 工作量中等偏大，风险中等。RV32 的算术语义与 eBPF 接近，前端结构可以复用。主要新增成本是压缩指令的 16 位解码、CSR 访问，以及 RV32 的 `MULH`/`DIV` 语义差（RISC-V 的除零结果与 eBPF 不同，需要另一套改写）。跨架构比较和可观察事件提取本轮明确不做。

## 十一、已验证与未验证的分界

**已由实验验证。** 符号执行器可脱离 LLVM 前端运行；真实 eBPF 机器码可转成 Alive2 IR 并得到符号表达式；156 例逐 opcode 矩阵与独立参考等价；120 个随机程序差分无差异；6 个 Clang 编译程序端到端通过；条件分支与两种形状的有界循环复用 Alive2 原有机制；8 类错误转换被测试抓到；14 例不支持编码明确报错；有界展开的覆盖行程数随 CFG 形状变化，不是固定公式。

**已被实验否定的推测。** 上一轮记录的"`unroll(k)` 覆盖 `k+1` 个行程"不通用。头块判断退出的形状测得 `k+1`，循环体先执行、回边为条件跳转的形状测得 `k`。

**尚未验证的推测。** 覆盖行程数差异源于退出判断相对回边的位置；eBPF 内存/helper/Map 能用现有内存模型表达；RV32IMC 能复用同一前端结构；真实内核执行器与 v6.12 规范在有符号除法溢出上行为一致。