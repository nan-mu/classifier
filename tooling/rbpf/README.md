# eBPF 发布对象分析

`analyze-object` 分析单个 eBPF `.o`。`release` 逐包核对发布 SHA-256、v3 索引和 `bpf.path` 所指成员，使用同一对象装载器和 angr/Heimdall 执行后端。对象需为 ELF64 小端 ET_REL / EM_BPF，具有唯一 XDP 入口。装载器解析 XDP 节的 `R_BPF_64_64` 重定位、ELF 符号和 `.BTF` 中的 map 定义。

对象报告记录对象摘要、代码节和入口符号、重定位绑定，以及 angr、claripy 和 Heimdall 版本。路径来自 angr 的退出状态，报告保留可见 context、完整有效包、map 初态和终态、有序 helper 与写入事件。声明域、退出覆盖和规格查询可使用保存的 SMT-LIB 复算。执行环境支持本批 XDP 程序所需的 HASH、ARRAY 和 `map_lookup_elem`。未建模的代码、符号地址、异常和预算缺口出现在诊断中。初始 context 与栈按 XDP 入口设置，包内 scratch 与包数据一起比较。

## 复跑 v0.1.1

需要 Python 3.12、7-Zip 和原任务包。锁文件保留了原型使用的依赖。Heimdall 的架构和 VEX lifter 来自任务包中固定提交的原型，许可证随源码保留。正式向量规格直接读取原包的 23 组输入和保存的独立期望，不重建历史 C host 用例。

```sh
run=$(mktemp -d)
python3.12 -m venv "$run/venv"
py="$run/venv/bin/python"
"$py" -m pip install -r tooling/rbpf/requirements-angr.txt
shasum -a 256 /tmp/classifier-release-elf-taskbook.zip
unzip -q /tmp/classifier-release-elf-taskbook.zip -d "$run/bundle"
mkdir "$run/assets"
gh release download v0.1.1 --repo nan-mu/libbpf-mcu --pattern '*.7z' --dir "$run/assets"

"$py" tooling/rbpf/make_specs.py --release-objects \
  --evidence "$run/bundle/evidence" --out "$run/specs"
"$py" tooling/rbpf/analyze.py release --tag v0.1.1 \
  --assets "$run/assets" --digests tooling/rbpf/libbpf-mcu-v0.1.1-digests.json \
  --specs "$run/specs" --out "$run/release"
"$py" tooling/rbpf/acceptance_objects.py --release-results "$run/release" \
  --assets "$run/assets" --evidence "$run/bundle/evidence" \
  --specs "$run/specs" --out "$run/checks" --z3 z3
```

原任务包的 SHA-256 为 `64e25d28e27daffb5c3df264749e95c79da808895195be04413aea8c58208e8f`。`--z3` 用独立的 Z3 可执行文件复算查询，可省略。单文件分析可直接使用复跑脚本导出的已核验对象。

```sh
"$py" tooling/rbpf/analyze.py analyze-object "$run/checks/case_mark_bpf.o" \
  --spec "$run/specs/case_mark.json" --out "$run/one-object"
```

批处理在每条记录中保留摘要或错误定位。合法对象按索引装载，rBPF mode 和容器成员不参与该路径。缺少规格的条目报告 `no_spec`，验收脚本要求 12 个程序均执行并通过对应向量。反例可把 `counterexample.json` 当作 `--spec` 重放。具体失败和未覆盖范围可从 `result.json` 追到指令槽及查询。

## 历史 rBPF 容器对照

分析入口读取 Compact ELF 的 `.xpost.image`，以容器 map 描述符的顺序解析 `lddw` 中的 map 索引。Rust 校验器复用 vendored `xpost-elf`，核对发布端 8 KiB 上限、规范 ELF 布局和镜像 SHA-256。Compact ELF V0 没有执行引擎字段。单文件由 `--engine ebpf` 声明，发布归档由索引中的 `mode.name = "ebpf"` 声明，离线批处理读取 `<程序>/ebpf.elf`。

在仓库根目录构建并准备 Python 环境。批处理还需要 7-Zip。生成 EXB2 验收规格需要 C 编译器和 libbpf-mcu 源码。

```sh
cargo build --locked --manifest-path tooling/Cargo.toml -p classifier-rbpf
run=$(mktemp -d)
python3.11 -m venv "$run/venv"
py="$run/venv/bin/python"
"$py" -m pip install z3-solver==4.15.4.0
```

### 单个容器

```sh
"$py" tooling/rbpf/analyze.py analyze /path/to/ebpf.elf --engine ebpf \
  --spec /path/to/spec.json --out "$run/single"
```

规格文件包含 `cases` 和 `vectors`。每个用例声明输入和可选的行为期望。以下用例检查长度取 0 或 1 时，程序是否总返回 32 位 XDP_DROP 并保持所有观察状态。域内的第一个字节可以取任意 8 位值。

```json
{
  "cases": [
    {
      "id": "drop",
      "input": {"packet_hex": "ff", "lengths": [0, 1], "symbolic_bytes": [0]},
      "expect": [{"action": 1}]
    }
  ]
}
```

- `input.packet_hex` 提供包模板。`lengths` 默认为模板长度。`symbolic_bytes` 列出取值自由的模板偏移。`context_hex` 设定紧随 `data` 和 `data_end` 的 16 个初始 context 字节，默认填零。
- `input.map` 是 `{"map":"blacklist","key":"c0000211","present":null,"value":null}` 形式的条目列表。`key` 是内存序十六进制字节。`present` 和 `value` 分别采用布尔值和对应宽度的无符号整数，两者都可用 `null` 声明符号量。未列出的 HASH 键缺失，未列出的合法 ARRAY 索引存在且值为零。
- 每条 `expect` 用必填 `action` 声明动作，`bytes` 和 `context` 用十进制偏移字符串到整数的映射覆盖指定字节。其余有效包字节和 context 字节应保持初态。可用 `map` 列表为命名键声明期望存在性及最终 `value`，或指定按值宽度回绕的 `add`。默认 map 保持初态。缺失键只比较存在性。
- `helpers` 声明有序调用，默认列表为空。每条记录含 `helper`、`map`、`key` 和 `present`。`key` 也可为 `{"packet_offset":26}`，表示从输入包读取一个描述符宽度的键。
- `when` 可按 `length`、`bytes`、map 的 `present`（条目含 `map`、`key`、`is`）限定期望。`not` 对嵌套条件取反，`all` 对条件列表取合取。每条适用期望都必须满足。遗漏的输入由规格覆盖查询报告。省略 `expect` 的用例只检查退出覆盖。`vectors` 要求固定输入及期望，单独统计通过数。

程序目录保存 `spec.json`、容器与镜像摘要、指令操作码清单、map 布局、校验器版本及可执行文件摘要、Python/Z3 版本和预算。每个用例保存 `domain.smt2`、`uncovered.smt2` 及适用的 `spec-uncovered.smt2` 和 `negated-spec.smt2`。可直接用 `z3 <文件>` 复算。域非空、所有输入均有正常退出、期望覆盖全域且否定式 UNSAT 时，用例才报告 `holds`。

`result.json` 含退出条件、动作、有效包范围、字节、context 和稀疏 map 终态，以及按执行顺序记录的写入和 helper 事件。指令位置 `pc` 从镜像首个 8 字节槽开始编号。`packet.origin` 标出所列字节的首个偏移。符号范围通过 `packet_range` 给出。反例目录内的 `counterexample.json` 可直接作为 `--spec` 重放。

执行模型覆盖发布语料使用的指令和 `map_lookup_elem`。HASH lookup 在已声明的逻辑键及其补集上分支。多值内存地址、多值 ARRAY 索引、未建模指令或 helper、异常、预算和求解超时会留下未覆盖条件。路径终止和规格结论受所声明的输入、map 初态及指令语义约束。

### 历史发布和离线验收

发布模式读取本地归档和对应 SHA-256 清单。清单中的每个资产都有一条记录。归档只读指定成员，核对资产摘要、`index.toml` 的程序身份及其记录的成员长度和摘要。`bpf.path` 参与索引核验，分析只加载 `containers/<程序>-vm-ebpf.elf`。有容器的程序使用 `--specs <目录>` 下的 `<程序>.json`。没有声明输入的容器记为 `no_spec`。各批次目录须为新目录。

```sh
"$py" tooling/rbpf/analyze.py container-release --tag v0.1.0 \
  --assets /path/to/release/v0.1.0 --digests /path/to/evidence/digests.json \
  --out "$run/release"
"$py" tooling/rbpf/analyze.py offline --containers /path/to/evidence/containers \
  --specs /path/to/specs --out "$run/offline"
```

验收使用原任务书 ZIP 中的发布资产、离线容器及具体向量。这些输入保留在附件。脚本复跑两种批处理和三个反例，并检查含缺失归档、损坏容器、普通编译对象及有效索引容器的部分发布。EXB2 的附加期望来自固定版本的 host 入口，copy 和 bsort 的 scratch 分别以直接复制和排序复核。脚本还对七个 EXB2 容器使用零回边预算，检查未覆盖条件能否保留。

```sh
unzip /tmp/classifier-release-elf-taskbook.zip -d "$run/bundle"
git clone --depth 1 --branch v0.1.0 git@github.com:nan-mu/libbpf-mcu.git "$run/libbpf-mcu"
"$py" tooling/rbpf/acceptance.py --bundle "$run/bundle" \
  --upstream "$run/libbpf-mcu" --out "$run/acceptance" --z3 z3
"$py" -m unittest discover -s tooling/rbpf -v
```

发布清点和离线分析分别写 `release/summary.json` 及 `offline/summary.json`。`acceptance.json` 记录 EXB2 host 编译器、编译参数和上游提交，指定 `--z3` 时也记录外部求解器版本与复算结果。下列查询对应 case_mark 的长度/版本字节域、firewall 的错误计数规格以及 copy 的零回边预算。

```sh
z3 "$run/acceptance/offline/case_mark/cases/version/uncovered.smt2"
z3 "$run/acceptance/offline/case_mark/cases/version/negated-spec.smt2"
z3 "$run/acceptance/offline/firewall/cases/wrong-count/negated-spec.smt2"
z3 "$run/acceptance/budget-copy/cases/magic-byte/uncovered.smt2"
```
