# Alive file v1

A `.alive` file is text. It is not an ELF object, not SMT-LIB, and not LLVM bitcode. The body is what `Function::print` writes. The loader rebuilds Alive2 `Function`, `BasicBlock`, and `Instr` objects from that text. It does not parse a source-to-target transform, and it does not wrap the program as `f => f`.

This note records the printers that were read. A form that is not listed here is not part of v1 yet. The loader must reject it. No loader exists yet.

## Header

`Function::print` does not write a version. v1 adds comment lines before the first `define` or `declare`. A comment starts with `;` and runs to the end of the line.

The first comment is `; alive-file v1`. The file also names the Alive2 pin and the Rocq pin.

```
; alive-file v1
; alive2-pin adacbd5180ccf95075e9867c4f0c259f59c9fef2
; rocq-pin 78d65a77592aae84b31f86385f8be4ab83b45ccb
```

A missing `alive-file v1` line, or a different version token, is a hard error. The pins are checked against the loader's built-in pins. A mismatch is a hard error. Comments elsewhere are ignored. The body contains no pass lines, no JSON, and no proof result.

The conditional text in `alive2/ebpf-test.log` under `Generated Alive2 IR` is a real `Function::print` body. It has no v1 header. A generated file adds the header above that body.

## Module

`Function::print` (`alive2/third_party/alive2/ir/function.cpp:877`) writes optional declarations, optional globals, then one function.

A declaration is `declare`, the return type, a name, `(`, comma-separated typed inputs, optional `...`, `)`, and the function attributes. Inputs print as attribute text immediately followed by the type (`function.cpp:885`).

The function header is `define`, the return type, ` @`, the name, `(`, comma-separated inputs, `)`, the attributes, and ` {`. Each input prints through `operator<<` on `Value` (`value.cpp:33`), which is the type, a space, and the name. Attributes come from `FnAttrs` (`attrs.cpp:105`) and end with `MemoryAccess` (`attrs.cpp:283`). `memory(none)` is the zero mask. `memory(read)` and `memory(write)` are the read-anything and write-anything cases. A narrower mask prints `argmem`, `globals`, `inaccessiblemem`, `errno`, or `other`, each with `: read`, `: write`, or `: readwrite`.

A helper that stores must not be declared `memory(none)`.

## Blocks

`operator<<` for `BasicBlock` (`function.cpp:120`) prints the name without its leading `%`, then `:`, then each instruction indented two spaces. Blocks are separated by a blank line. The function ends with `}`.

A block name in a branch or a phi keeps the `%`. The label at the block does not.

## Types and names

`IntType::print` (`type.cpp:409`) writes `i` and the bit width. `PtrType::print` (`type.cpp:776`) writes `ptr`, plus ` addrspace(N)` when the address space is not 0. `print_type` (`instr.cpp:36`) prints the type and a trailing space when the type string is not empty.

A value prints as its type, a space, and its name, unless the type string is empty. Instruction names in the existing lifter output are `%0`, `%b3_r0`, register inputs such as `r1`, and integer constants such as `10`.

## Instructions read

`BinOp::print` (`instr.cpp:153`) writes the result name, ` = `, the opcode, optional `nsw `, `nuw `, `exact `, and `disjoint `, then the left value with its type and the right name without a type. Opcodes read from that switch include `add`, `sub`, `mul`, `sdiv`, `udiv`, `srem`, `urem`, `shl`, `ashr`, `lshr`, `and`, `or`, and `xor`. An eBPF shift is the opcode after a mask. An eBPF divide is not a bare `udiv` or `sdiv` on the zero or overflow path. Those paths are branches and phis, because Alive2 treats them as undefined behavior.

`ICmp::print` (`instr.cpp:2953`) writes `name = icmp `, optional `samesign `, the condition, the left value with its type, `, `, and the right name. Conditions read there are `eq`, `ne`, `sle`, `slt`, `sge`, `sgt`, `ule`, `ult`, `uge`, and `ugt`. Optional suffixes are `, use_provenance` and `, offsetonly`.

`Phi::print` (`instr.cpp:3300`) writes `name = phi `, the type with a trailing space, then `[ `, the value name, `, `, the predecessor block name, ` ]`. Later pairs follow `, `.

`Branch::print` (`instr.cpp:3403`) writes `br `, the condition value with its type when present, `, `, `label `, and the true block name. A conditional branch adds `, label ` and the false block name.

`Return::print` (`instr.cpp:3521`) writes `ret `, the type with a trailing space, and the value name.

`Load::print` (`instr.cpp:4411`) writes `name = load `, the loaded type, `, `, the pointer value with its type, `, align `, and the alignment.

`Store::print` (`instr.cpp:4458`) writes `store `, the stored value with its type, `, `, the pointer value with its type, `, align `, and the alignment.

`FnCall::print` (`instr.cpp:2599`) writes an optional `name = `, then `call `, the return type with a trailing space, the callee name, `(`, arguments, `)`, and the call attributes. Each argument is its attribute text plus the value. A void call omits the result name.

## Not accepted yet

Printers for `trunc`, `zext`, `sext`, `getelementptr`, `alloca`, `switch`, `freeze`, and `select` were not read. v1 does not accept those spellings until the printer is cited and the loader builds that instruction. The corpus needs byte and word loads, so a later pass has to add the conversion printers or choose a load type that `Load::print` already emits.

`END` / `be32` / `be64` is not an Alive2 opcode. The compiler rewrites it into instructions whose printers are listed above. It does not invent a `bswap` token.

A forward reference to a block or a value is allowed in the text. The loader resolves names in a second pass. A missing name, a repeated definition, a phi predecessor that is not a predecessor, or a block that does not end in `br` or `ret` is a hard error.
