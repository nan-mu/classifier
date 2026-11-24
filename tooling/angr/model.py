"""XDP input, observation and bytecode types shared by the two analyzers."""

from dataclasses import dataclass, field, replace
import struct

import z3


CONTEXT = 0x100
PACKET = 0x10000
FRAME = 0x20000
MAP_VALUES = 0x40000
CONTEXT_BYTES = 24

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
