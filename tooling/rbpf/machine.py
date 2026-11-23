"""Bounded XDP eBPF execution for the libbpf-mcu rBPF ABI."""

from dataclasses import dataclass, field, replace
import operator
import struct

import z3


CONTEXT = 0x100
PACKET = 0x10000
FRAME = 0x20000
MAP_VALUES = 0x40000
CONTEXT_BYTES = 24

ALU = {
    0x00: operator.add, 0x10: operator.sub, 0x20: operator.mul,
    0x40: operator.or_, 0x50: operator.and_, 0x80: lambda a, _: -a,
    0xA0: operator.xor, 0xB0: lambda _, b: b,
}
JUMPS = {
    0x10: operator.eq, 0x20: z3.UGT, 0x30: z3.UGE,
    0x40: lambda a, b: (a & b) != 0, 0x50: operator.ne,
    0x60: operator.gt, 0x70: operator.ge, 0xA0: z3.ULT, 0xB0: z3.ULE,
    0xC0: operator.lt, 0xD0: operator.le,
}


def bv(value, bits):
    return z3.BitVecVal(value, bits)


def resize(value, bits):
    if value.size() == bits:
        return value
    if value.size() < bits:
        return z3.ZeroExt(bits - value.size(), value)
    return z3.Extract(bits - 1, 0, value)


def octets(value, width):
    value = z3.simplify(value)
    if z3.is_bv_value(value):
        return [bv((value.as_long() >> (8 * i)) & 255, 8) for i in range(width)]
    return [z3.simplify(z3.Extract(8 * i + 7, 8 * i, value)) for i in range(width)]


def unpack(data):
    if len(data) == 1:
        return data[0]
    return z3.simplify(z3.Concat(*reversed(data)))


def literal(value):
    return value.as_long() if z3.is_bv_value(value) else None


class Gap(Exception):
    def __init__(self, kind, detail):
        super().__init__(detail)
        self.kind = kind


class Infeasible(Exception):
    """The remainder of a state has already been recorded or ruled out."""


def solver_gap(reason):
    return "solver_timeout" if reason in ("timeout", "canceled") else "solver_unknown"


@dataclass(frozen=True)
class Map:
    name: str
    type: int
    capacity: int
    vma: int
    key_bytes: int
    value_bytes: int

    @property
    def array(self):
        return self.type == 2

    def default(self, key):
        present = self.array and int.from_bytes(bytes.fromhex(key), "little") < self.capacity
        return Entry(z3.BoolVal(present), bv(0, self.value_bytes * 8))


@dataclass(frozen=True)
class Entry:
    present: z3.BoolRef
    value: z3.BitVecRef
    address: int = 0


@dataclass
class State:
    packet: list
    length: z3.BitVecRef
    context: list
    regs: list
    maps: dict
    guard: z3.BoolRef
    pc: int = 0
    steps: int = 0
    back_edges: int = 0
    stack: dict = field(default_factory=dict)
    events: list = field(default_factory=list)

    def fork(self, guard):
        return replace(
            self, guard=guard, packet=self.packet.copy(), context=self.context.copy(),
            regs=self.regs.copy(), maps=self.maps.copy(), stack=self.stack.copy(),
            events=self.events.copy(),
        )

    def register(self, reg):
        value = self.regs[reg]
        if value is None:
            raise Gap("exception", f"read of undefined r{reg}")
        return value

    def write_register(self, reg, value):
        if reg == 10:
            raise Gap("exception", "write to frame pointer")
        self.regs[reg] = z3.simplify(resize(value, 64))


@dataclass(frozen=True)
class Instruction:
    code: int
    dst: int
    src: int
    offset: int
    imm: int
    high: int | None = None


def decode(image, map_count):
    if not image or len(image) % 8:
        raise ValueError("rBPF image must contain complete 8-byte instructions")
    words = tuple(struct.iter_unpack("<BBhi", image))
    instructions = {}
    pc = 0
    while pc < len(words):
        code, regs, offset, imm = words[pc]
        dst, src = regs & 15, regs >> 4
        if dst > 10 or src > 10 or code == 0:
            raise ValueError(f"invalid rBPF instruction at slot {pc}")
        if (code == 0x95 and (regs or offset or imm)
                or code == 0x85 and (dst or offset)
                or code == 0x05 and (regs or imm)
                or code == 0x06 and (regs or offset)):
            raise ValueError(f"invalid rBPF control instruction at slot {pc}")
        high = None
        if code == 0x18:
            if pc + 1 >= len(words) or words[pc + 1][:3] != (0, 0, 0):
                raise ValueError(f"malformed lddw at slot {pc}")
            high = words[pc + 1][3]
            if offset or src not in (0, 1) or (src == 1 and (high or not 0 <= imm < map_count)):
                raise ValueError(f"invalid rBPF map reference or lddw at slot {pc}")
        instructions[pc] = Instruction(code, dst, src, offset, imm, high)
        pc += 2 if high is not None else 1
    return instructions


class Machine:
    def __init__(self, instructions, maps, max_steps, max_back_edges, max_paths, timeout):
        self.instructions = instructions
        self.maps = maps
        self.maps_by_vma = {map_.vma: map_ for map_ in maps}
        self.max_steps = max_steps
        self.max_back_edges = max_back_edges
        self.max_paths = max_paths
        self.solver = z3.Solver()
        self.solver.set(timeout=timeout)
        self.gaps = []

    def record(self, state, kind, detail, guard=None):
        self.gaps.append({
            "kind": kind, "detail": detail, "pc": state.pc, "steps": state.steps,
            "back_edges": state.back_edges,
            "guard": state.guard if guard is None else guard,
        })

    def feasible(self, state, guard):
        guard = z3.simplify(guard)
        if z3.is_false(guard):
            return False
        if z3.is_true(guard):
            return True
        result = self.solver.check(guard)
        if result == z3.unknown:
            reason = self.solver.reason_unknown()
            self.record(state, solver_gap(reason), reason, guard)
        return result == z3.sat

    def require(self, state, condition, detail):
        condition = z3.simplify(condition)
        if z3.is_true(condition):
            return
        invalid = z3.simplify(z3.And(state.guard, z3.Not(condition)))
        if self.feasible(state, invalid):
            self.record(state, "exception", detail, invalid)
        valid = z3.simplify(z3.And(state.guard, condition))
        if not self.feasible(state, valid):
            raise Infeasible
        state.guard = valid

    def resolve(self, state, value, detail):
        value = z3.simplify(value)
        concrete = literal(value)
        if concrete is not None:
            return concrete
        result = self.solver.check(state.guard)
        if result == z3.unknown:
            reason = self.solver.reason_unknown()
            raise Gap(solver_gap(reason), reason)
        if result == z3.unsat:
            raise Infeasible
        candidate = self.solver.model().eval(value, model_completion=True).as_long()
        result = self.solver.check(state.guard, value != candidate)
        if result == z3.unknown:
            reason = self.solver.reason_unknown()
            raise Gap(solver_gap(reason), reason)
        if result == z3.sat:
            raise Gap("symbolic_address", f"{detail}: {value.sexpr()}")
        return candidate

    def locate(self, state, address, width):
        end = address + width
        if PACKET <= address and end <= PACKET + len(state.packet):
            offset = address - PACKET
            self.require(state, z3.UGE(state.length, offset + width), "packet access beyond data_end")
            return "packet", offset, None
        if CONTEXT <= address and end <= CONTEXT + len(state.context):
            return "context", address - CONTEXT, None
        if FRAME - 512 <= address and end <= FRAME:
            return "stack", address, None
        for identity, entry in state.maps.items():
            if entry.address and entry.address <= address and end <= entry.address + entry.value.size() // 8:
                self.require(state, entry.present, "map value access after deletion")
                return "map", address - entry.address, identity
        raise Gap("exception", f"memory range {address:#x}..{end:#x} lies outside accessible regions")

    def load(self, state, address, width):
        location = self.resolve(state, address, "memory address varies over path")
        resource, offset, identity = self.locate(state, location, width)
        if resource == "stack":
            try:
                data = [state.stack[i] for i in range(offset, offset + width)]
            except KeyError as err:
                raise Gap("exception", "read of uninitialized stack byte") from err
        elif resource == "map":
            value = state.maps[identity].value
            return z3.simplify(z3.Extract((offset + width) * 8 - 1, offset * 8, value))
        else:
            data = getattr(state, resource)[offset:offset + width]
        return unpack(data)

    def store(self, state, address, width, value):
        location = self.resolve(state, address, "memory address varies over path")
        resource, offset, identity = self.locate(state, location, width)
        data = octets(resize(value, width * 8), width)
        if resource == "stack":
            state.stack.update(zip(range(offset, offset + width), data))
            return
        event = {"pc": state.pc, "kind": "write", "resource": resource,
                 "offset": offset, "width": width, "value": unpack(data)}
        if resource == "map":
            entry = state.maps[identity]
            contents = octets(entry.value, entry.value.size() // 8)
            contents[offset:offset + width] = data
            state.maps[identity] = replace(entry, value=unpack(contents))
            event.update(map=identity[0], key=identity[1])
        else:
            getattr(state, resource)[offset:offset + width] = data
        state.events.append(event)

    def helper(self, state, helper_id):
        if helper_id != 1:
            raise Gap("unknown_helper", f"helper {helper_id} has no modeled semantics")
        handle = self.resolve(state, state.register(1), "map handle varies over path")
        map_ = self.maps_by_vma.get(handle)
        if map_ is None:
            raise Gap("exception", "lookup has no container map descriptor")

        key_value = z3.simplify(self.load(state, state.register(2), map_.key_bytes))
        key_int = literal(key_value)
        if key_int is None and map_.array:
            key_int = self.resolve(state, key_value, "ARRAY lookup key varies over path")
        if key_int is not None:
            key = key_int.to_bytes(map_.key_bytes, "little").hex()
            self.lookup(state, map_, key_value, key)
            return [state]

        # A HASH domain is sparse. Partition on its named logical keys, with
        # a single miss arm for all other keys and the exact key in the event.
        alternatives = []
        remaining = state.guard
        for name, key in state.maps:
            if name != map_.name:
                continue
            matches = key_value == int.from_bytes(bytes.fromhex(key), "little")
            guard = z3.simplify(z3.And(remaining, matches))
            if self.feasible(state, guard):
                alternative = state.fork(guard)
                self.lookup(alternative, map_, key_value, key)
                alternatives.append(alternative)
            remaining = z3.simplify(z3.And(remaining, z3.Not(matches)))
        if self.feasible(state, remaining):
            alternative = state.fork(remaining)
            self.lookup(alternative, map_, key_value, None)
            alternatives.append(alternative)
        return alternatives

    def lookup(self, state, map_, key_value, key):
        entry = Entry(z3.BoolVal(False), bv(0, map_.value_bytes * 8))
        if key is not None:
            identity = (map_.name, key)
            entry = state.maps.get(identity, map_.default(key))
            if not entry.address and not z3.is_false(entry.present):
                # Repeated lookup of one logical key aliases existing pointers.
                address = MAP_VALUES + 256 * sum(bool(e.address) for e in state.maps.values())
                entry = replace(entry, address=address)
            state.maps[identity] = entry
        result = z3.simplify(z3.If(entry.present, bv(entry.address, 64), bv(0, 64)))
        state.write_register(0, result)
        for i in range(1, 6):
            state.regs[i] = None
        state.events.append({
            "pc": state.pc, "kind": "helper", "helper": 1, "name": "map_lookup_elem",
            "resource": "map", "map": map_.name, "key": key if key is not None else key_value,
            "key_width": map_.key_bytes, "key_value": key_value,
            "present": entry.present, "result": result,
        })

    def branch(self, state, condition, yes, no):
        condition = z3.simplify(condition)
        if z3.is_true(condition):
            return [(state, yes)]
        if z3.is_false(condition):
            return [(state, no)]
        targets = []
        for predicate, target in ((condition, yes), (z3.Not(condition), no)):
            guard = z3.simplify(z3.And(state.guard, predicate))
            if self.feasible(state, guard):
                targets.append((state.fork(guard), target))
        return targets

    def alu(self, state, insn, bits):
        op = insn.code & 0xf0
        if op == 0xd0:
            width = insn.imm
            if width not in (16, 32, 64):
                raise Gap("unsupported_instruction", f"invalid endian width {width}")
            value = resize(state.register(insn.dst), width)
            if insn.code & 8 or bits == 64:
                value = z3.Concat(*octets(value, width // 8))
            return value

        use_src = bool(insn.code & 8)
        right = resize(state.register(insn.src), bits) if use_src else bv(insn.imm, bits)
        left = resize(state.register(insn.dst), bits) if op != 0xb0 else None
        if op == 0xb0 and use_src and insn.offset:
            if insn.offset not in (8, 16, 32) or insn.offset >= bits:
                raise Gap("unsupported_instruction", "invalid sign-extending MOV width")
            return z3.SignExt(bits - insn.offset, resize(right, insn.offset))
        if op in ALU:
            return ALU[op](left, right)
        if op == 0x30:
            quotient = left / right if insn.offset == 1 else z3.UDiv(left, right)
            return z3.If(right == 0, bv(0, bits), quotient)
        if op == 0x90:
            remainder = z3.SRem(left, right) if insn.offset == 1 else z3.URem(left, right)
            return z3.If(right == 0, left, remainder)
        shift = right & (bits - 1)
        if op == 0x60:
            return left << shift
        if op == 0x70:
            return z3.LShR(left, shift)
        if op == 0xc0:
            return left >> shift
        raise Gap("unsupported_instruction", f"opcode {insn.code:#x}")

    def step(self, state, insn):
        code, dst, src = insn.code, insn.dst, insn.src
        next_pc = state.pc + 1
        cls, op = code & 7, code & 0xf0
        if insn.high is not None:
            value = self.maps[insn.imm].vma if src == 1 else (
                (insn.imm & 0xffffffff) | ((insn.high & 0xffffffff) << 32)
            )
            state.write_register(dst, bv(value, 64))
            next_pc += 1
        elif cls in (4, 7):
            state.write_register(dst, self.alu(state, insn, 32 if cls == 4 else 64))
        elif cls in (1, 2, 3) and code & 0xe0 == 0x60:
            width = {0: 4, 8: 2, 16: 1, 24: 8}[code & 0x18]
            if cls == 1:
                address = state.register(src) + insn.offset
                state.write_register(dst, self.load(state, address, width))
            else:
                address = state.register(dst) + insn.offset
                value = bv(insn.imm, 64) if cls == 2 else state.register(src)
                self.store(state, address, width, value)
        elif code == 0x85 and src == 0:
            return [(successor, next_pc) for successor in self.helper(state, insn.imm)]
        elif code in (0x05, 0x06):
            next_pc += insn.offset if code == 0x05 else insn.imm
        elif cls in (5, 6) and op in JUMPS:
            bits = 64 if cls == 5 else 32
            left = resize(state.register(dst), bits)
            right = resize(state.register(src), bits) if code & 8 else bv(insn.imm, bits)
            return self.branch(state, JUMPS[op](left, right), next_pc + insn.offset, next_pc)
        else:
            raise Gap("unsupported_instruction", f"opcode {code:#x}")
        return [(state, next_pc)]

    def run(self, initial):
        pending, exits = [initial], []
        forks = 1
        while pending:
            state = pending.pop()
            try:
                while True:
                    insn = self.instructions.get(state.pc)
                    if insn is None:
                        raise Gap("exception", "program counter does not identify an instruction")
                    if state.steps >= self.max_steps:
                        raise Gap("step_budget", "instruction budget exhausted")
                    state.steps += 1
                    if insn.code == 0x95:
                        state.register(0)
                        start, end = map(unpack, (state.context[:4], state.context[4:8]))
                        self.require(state, z3.And(
                            z3.UGE(start, PACKET), z3.UGE(end, start),
                            z3.ULE(end, bv(PACKET, 32) + state.length),
                        ), "exit context references an invalid packet range")
                        exits.append(state)
                        break
                    successors = self.step(state, insn)
                    forks += max(0, len(successors) - 1)
                    for successor, target in successors:
                        if target <= state.pc and successor.back_edges == self.max_back_edges:
                            self.record(successor, "loop_budget", f"back edge to slot {target}")
                        elif forks > self.max_paths and len(successors) > 1:
                            self.record(successor, "path_budget", "path budget exhausted")
                        else:
                            successor.back_edges += int(target <= state.pc)
                            successor.pc = target
                            pending.append(successor)
                    if not pending or len(successors) != 1 or pending[-1] is not successors[0][0]:
                        break
                    state = pending.pop()
            except Gap as err:
                self.record(state, err.kind, str(err))
            except Infeasible:
                pass
        return exits, self.gaps
