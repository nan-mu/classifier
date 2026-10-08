# 文档索引

[返回项目入口](../README.md)

## 阅读路线

1. 阅读 [共同数学定义](common-math.md)，了解 Reg、Term、Expr、Predicate、状态快照与有预算展开。新增节点和算法定义在原文中标为草案。
2. 按指令集阅读 [RV32IMC 值函数](rv32imc-expr-value-functions.md)或 [eBPF 值函数](ebpf-expr-value-functions.md)，查看更新规则、拒绝项和待定边界。
3. 调试 RV32 XDP 镜像时，阅读 [RV32 初态](rv32-initial-expr.zh.md)，了解入口寄存器与 `xdp_md` 槽。当前栈绑定及 ESP32-C3 展开观察见 RV32IMC 值函数第 7.3、7.4 节。
4. 探索循环与路径表达式时，阅读 [代数程序分析](algebraic-program-analysis.zh.md)。该文讨论研究方法，不确定项目最终架构或输出类型。

## 运行与开发

- [项目 README](../README.md)：工作区布局、构建检查与一键启动。
- [调试服务](../debug_server/README.md)：API、程序选择与会话预算。
- [调试界面](../debug_web/README.md)：独立启动、构建与图操作。
- [代理工作约定](../AGENTS.md)：架构边界与 Lean 工作交接要求。

## 文档维护约定

共享数学对象在 `common-math.md` 中维护，指令集文档引用共同定义并说明各自规则。入口条件放在初态文档；运行命令和接口说明放在对应组件 README。

实现观察与数学规范应明确区分，保留草案、待定和拒绝边界。实现发生变化时，同时检查对应说明与示例；单次运行的节点数和预算不应当作通用保证。

新增主题文档时更新本索引。优先保持现有文件名，并使用相对链接，便于仓库内浏览。
