"""Execute relocated XDP code in angr using the pinned Heimdall lifter."""

from dataclasses import dataclass
from io import BytesIO

import angr
from angr.calling_conventions import SimCC, SimRegArg
import claripy
from claripy.errors import ClaripySolverInterruptError
import z3

from heimdall import ArchExtendedBPF, REVISION
from heimdall.instrs_ebpf import BPF_CALLER_SAVE_BASE, BPF_CALL_STACK_BASE, BPF_EXIT_SENTINEL
from machine import CONTEXT, FRAME, MAP_VALUES, PACKET, Entry, Gap, State, bv, unpack


CODE_BASE = 0x200000
LE = "Iend_LE"
BE = "Iend_BE"
Z3 = claripy.backends.z3


class LookupConvention(SimCC):
    ARCH = ArchExtendedBPF
    ARG_REGS = ["R1", "R2", "R3", "R4", "R5"]
    RETURN_VAL = SimRegArg("R0", 8)


def to_angr(value):
    # The pinned backend preserves the sorts and names of declared inputs.
    return Z3._abstract(z3.simplify(value))


def to_z3(value):
    return Z3.convert(value)


def bytes_from(state, address, size):
    if not size:
        return []
    value = state.memory.load(address, size, endness=BE, inspect=False)
    if value.concrete:
        return [bv(byte, 8) for byte in value.concrete_value.to_bytes(size, "big")]
    return [to_z3(value.get_byte(i)) for i in range(size)]


def initialize_bytes(state, address, values):
    if not values:
        return
    if all(z3.is_bv_value(value) for value in values):
        payload = claripy.BVV(bytes(value.as_long() for value in values))
        state.memory.store(address, payload, endness=BE, inspect=False)
    else:
        state.memory.store(address, to_angr(unpack(values)), endness=LE, inspect=False)


def unique(state, value, purpose):
    if isinstance(value, int):
        return value
    if value.concrete:
        return value.concrete_value
    choices = state.solver.eval_upto(value, 2)
    if len(choices) != 1:
        raise Gap("symbolic_address", f"{purpose} has no unique value: {value}")
    return choices[0]


@dataclass(frozen=True)
class MapCell:
    address: int
    width: int
    present: claripy.ast.Bool


class Lookup(angr.SimProcedure):
    """The fixed helper reads its key from the current XDP memory."""

    NO_RET = True

    def __init__(self, world, **kwargs):
        super().__init__(**kwargs)
        self.world = world

    def run(self):
        state = self.state
        pc = (self.addr - CODE_BASE) // 8
        state.globals["pc"] = pc
        self.world.instruction(state)
        handle = unique(state, state.regs.R1, "lookup map handle")
        map_ = self.world.maps.get(handle)
        if map_ is None:
            raise Gap("exception", f"slot {pc}: lookup handle has no ELF map binding")
        address = unique(state, state.regs.R2, "lookup key address")
        self.world.region(state, address, map_.key_bytes)
        key = state.memory.load(address, map_.key_bytes, endness=LE, inspect=False)
        if key.variables - self.world.input_names:
            raise Gap("exception", f"slot {pc}: lookup key depends on undefined data")
        cells = state.globals["map_cells"]
        if key.concrete or map_.array:
            key_int = unique(state, key, "ARRAY index")
            key_hex = key_int.to_bytes(map_.key_bytes, "little").hex()
            cell = cells.get((map_.name, key_hex))
            if cell is None and map_.array and key_int < map_.capacity:
                cell = self.world.add_cell(state, (map_.name, key_hex), map_.default(key_hex))
            result = claripy.BVV(0, 64) if cell is None else claripy.If(
                cell.present, claripy.BVV(cell.address, 64), claripy.BVV(0, 64))
        else:
            key_hex = None
            result = claripy.BVV(0, 64)
            for (name, named_key), cell in cells.items():
                if name == map_.name:
                    same = key == int.from_bytes(bytes.fromhex(named_key), "little")
                    result = claripy.If(same & cell.present, claripy.BVV(cell.address, 64), result)
        self.world.event(state, {
            "pc": pc, "kind": "helper", "helper": 1, "name": "map_lookup_elem",
            "resource": "map", "map": map_.name, "key": key_hex if key_hex is not None else to_z3(key),
            "key_width": map_.key_bytes, "key_value": to_z3(key),
            "present": to_z3(result != 0), "result": to_z3(result),
        })
        state.regs.R0 = result
        for i in range(1, 6):
            setattr(state.regs, f"R{i}", claripy.BVS(f"clobbered_r{i}", 64))
        self.jump(self.addr + 8)


class UnsupportedHelper(angr.SimProcedure):
    NO_RET = True

    def __init__(self, helper, **kwargs):
        super().__init__(**kwargs)
        self.helper = helper

    def run(self):
        raise Gap("unknown_helper", f"helper {self.helper} has no XDP model")


class XdpWorld:
    def __init__(self, domain, maps, limits, instructions):
        self.domain = domain
        self.maps = {map_.vma: map_ for map_ in maps}
        self.limits = limits
        self.instructions = instructions
        self.length = to_angr(domain.length)
        self.input_names = set().union(*(to_angr(value).variables for value in (
            domain.length, *domain.packet,
            *(value for entry in domain.entries.values() for value in (entry.present, entry.value)),
        ) if not (z3.is_bv_value(value) or z3.is_true(value) or z3.is_false(value))))

    def initial(self, project):
        state = project.factory.blank_state(addr=project.entry)
        state.solver.timeout = self.limits.timeout_ms
        state.regs.R1 = CONTEXT
        state.regs.R10 = FRAME
        state.regs.call_depth = 1
        state.memory.store(BPF_CALL_STACK_BASE, claripy.BVV(BPF_EXIT_SENTINEL, 64), endness=LE)
        state.memory.store(BPF_CALLER_SAVE_BASE, claripy.BVV(0, 80 * 8), endness=LE)
        initialize_bytes(state, CONTEXT, self.domain.context)
        initialize_bytes(state, PACKET, self.domain.packet)
        state.solver.add(to_angr(self.domain.guard))
        state.globals["events"] = ()
        state.globals["map_cells"] = {}
        state.globals["pc"] = (project.entry - CODE_BASE) // 8
        state.globals["steps"] = 0
        state.globals["back_edges"] = 0
        for identity, entry in self.domain.entries.items():
            self.add_cell(state, identity, entry)
        state.inspect.b("instruction", when=angr.BP_BEFORE, action=self.on_instruction)
        state.inspect.b("mem_read", when=angr.BP_BEFORE, action=self.on_read)
        state.inspect.b("mem_write", when=angr.BP_BEFORE, action=self.on_write)
        return state

    def add_cell(self, state, identity, entry):
        cells = state.globals["map_cells"]
        at = MAP_VALUES + 256 * len(cells)
        if at + 256 > BPF_CALL_STACK_BASE:
            raise Gap("exception", "XDP map value address space exhausted")
        cell = MapCell(at, entry.value.size() // 8, to_angr(entry.present))
        state.memory.store(at, to_angr(entry.value), endness=LE, inspect=False)
        state.globals["map_cells"] = {**cells, identity: cell}
        return cell

    def instruction(self, state):
        state.globals["steps"] += 1
        if state.globals["steps"] > self.limits.max_steps:
            raise Gap("step_budget", "instruction budget exhausted")

    def on_instruction(self, state):
        state.globals["pc"] = (state.inspect.instruction - CODE_BASE) // 8
        self.instruction(state)

    def require(self, state, condition, detail):
        if condition.is_false():
            raise Gap("exception", detail)
        if not condition.is_true() and state.solver.satisfiable(extra_constraints=[~condition]):
            raise Gap("exception", detail)

    def region(self, state, start, width, *, exit_read=False):
        end = start + width
        if PACKET <= start and end <= PACKET + len(self.domain.packet):
            self.require(state, claripy.UGE(self.length, end - PACKET), "packet access beyond data_end")
            return "packet", start - PACKET, None
        if CONTEXT <= start and end <= CONTEXT + len(self.domain.context):
            return "context", start - CONTEXT, None
        if FRAME - 512 <= start and end <= FRAME:
            return "stack", start, None
        if exit_read and (BPF_CALL_STACK_BASE <= start and end <= BPF_CALL_STACK_BASE + 8
                          or BPF_CALLER_SAVE_BASE <= start and end <= BPF_CALLER_SAVE_BASE + 80):
            return "internal", start, None
        for identity, cell in state.globals["map_cells"].items():
            if cell.address <= start and end <= cell.address + cell.width:
                self.require(state, cell.present, "access to an absent map value")
                return "map", start - cell.address, identity
        raise Gap("exception", f"memory range {start:#x}..{end:#x} outside XDP state")

    def on_read(self, state):
        address = unique(state, state.inspect.mem_read_address, "read address")
        width = unique(state, state.inspect.mem_read_length, "read width")
        insn = self.instructions.get(state.globals["pc"])
        self.region(state, address, width, exit_read=insn is not None and insn.code == 0x95)

    def on_write(self, state):
        address = unique(state, state.inspect.mem_write_address, "write address")
        value = state.inspect.mem_write_expr
        width = value.size() // 8
        resource, offset, identity = self.region(state, address, width)
        if resource == "stack":
            return
        if value.variables - self.input_names:
            raise Gap("exception", f"{resource} write depends on undefined data")
        event = {"pc": state.globals["pc"], "kind": "write", "resource": resource,
                 "offset": offset, "width": width, "value": to_z3(value)}
        if identity is not None:
            event.update(map=identity[0], key=identity[1])
        self.event(state, event)

    @staticmethod
    def event(state, event):
        state.globals["events"] += (event,)

    def guard(self, state):
        # Guard terms are over exactly the symbols declared by the spec.
        unknown = set().union(*(term.variables for term in state.solver.constraints)) - self.input_names
        if unknown:
            raise Gap("exception", f"execution depended on undeclared symbols: {sorted(unknown)}")
        return to_z3(claripy.And(*state.solver.constraints))

    def exit(self, state):
        guard = self.guard(state)
        context = bytes_from(state, CONTEXT, len(self.domain.context))
        start, end = unpack(context[:4]), unpack(context[4:8])
        self.require(state, to_angr(z3.And(
            z3.UGE(start, PACKET), z3.UGE(end, start),
            z3.ULE(end, bv(PACKET, 32) + self.domain.length),
        )), "exit context references an invalid packet range")
        values = {}
        for key, cell in state.globals["map_cells"].items():
            value = state.memory.load(cell.address, cell.width, endness=LE, inspect=False)
            values[key] = Entry(to_z3(cell.present), to_z3(value))
        action = state.regs.R0
        if action.variables - self.input_names:
            raise Gap("exception", "XDP action depends on an undefined register")
        packet = bytes_from(state, PACKET, len(self.domain.packet))
        return State(packet, self.domain.length, context, [to_z3(action)], values, guard,
                     pc=state.globals["pc"], steps=state.globals["steps"],
                     back_edges=state.globals["back_edges"], events=list(state.globals["events"]))


class AngrBackend:
    name = "angr/Heimdall"
    versions = {"angr": angr.__version__, "claripy": claripy.__version__, "heimdall": REVISION}

    def __init__(self, image, entry_offset, instructions):
        self.image = image
        self.entry_offset = entry_offset
        self.instructions = instructions

    def run(self, domain, maps, limits):
        world = XdpWorld(domain, maps, limits, self.instructions)
        project = angr.Project(
            BytesIO(self.image), arch=ArchExtendedBPF(LE), auto_load_libs=False,
            main_opts={"backend": "blob", "base_addr": CODE_BASE,
                       "entry_point": CODE_BASE + self.entry_offset},
        )
        for pc, insn in self.instructions.items():
            if insn.code == 0x85:
                cc = LookupConvention(project.arch)
                proc = Lookup(world, cc=cc) if insn.imm == 1 else UnsupportedHelper(insn.imm, cc=cc)
                project.hook(CODE_BASE + pc * 8, proc, length=8)
        pending = [world.initial(project)]
        exits, gaps = [], []
        forks = 1

        def record(state, kind, detail):
            try:
                guard = world.guard(state)
            except Gap:
                guard = domain.guard
            gaps.append({"kind": kind, "detail": detail, "guard": guard,
                         "pc": state.globals["pc"], "steps": state.globals["steps"],
                         "back_edges": state.globals["back_edges"]})

        while pending:
            state = pending.pop()
            try:
                address = unique(state, state.regs.ip, "instruction pointer")
                if address == BPF_EXIT_SENTINEL:
                    if self.instructions[state.globals["pc"]].code != 0x95:
                        raise Gap("exception", "exit sentinel reached without EXIT")
                    exits.append(world.exit(state))
                    continue
                pc = (address - CODE_BASE) // 8
                if (address - CODE_BASE) % 8 or pc not in self.instructions:
                    raise Gap("exception", f"not an XDP instruction slot: {address:#x}")
                state.globals["pc"] = pc
                next_states = project.factory.successors(state)
                if next_states.unconstrained_successors:
                    record(state, "symbolic_address", "unconstrained instruction pointer")
                successors = next_states.flat_successors
                if not successors and not next_states.unconstrained_successors:
                    record(state, "exception", "angr stopped before XDP EXIT")
                forks += max(0, len(successors) - 1)
                for successor in successors:
                    target = unique(successor, successor.regs.ip, "instruction pointer")
                    backwards = (CODE_BASE <= target <= CODE_BASE + successor.globals["pc"] * 8)
                    if backwards and successor.globals["back_edges"] >= limits.max_back_edges:
                        record(successor, "loop_budget", f"back edge to slot {(target-CODE_BASE)//8}")
                    elif len(successors) > 1 and forks > limits.max_paths:
                        record(successor, "path_budget", "path budget exhausted")
                    else:
                        successor.globals["back_edges"] += int(backwards)
                        pending.append(successor)
            except Gap as err:
                record(state, err.kind, str(err))
            except ClaripySolverInterruptError as err:
                record(state, "solver_timeout", str(err))
            except (angr.errors.AngrError, angr.errors.SimError, NotImplementedError) as err:
                record(state, "exception", f"{type(err).__name__}: {err}")
        return exits, gaps
