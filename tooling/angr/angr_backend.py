"""Execute relocated XDP code in angr using the pinned Heimdall lifter."""

from dataclasses import dataclass
from io import BytesIO

import angr
from angr.procedures.definitions import SimSyscallLibrary
import claripy
from claripy.errors import ClaripySolverInterruptError
import z3

from angr_ebpf.instrs_ebpf import BPF_CALLER_SAVE_BASE, BPF_CALL_STACK_BASE, BPF_EXIT_SENTINEL
from angr_ebpf.load_ebpf import ExtendedBPF
from angr_ebpf.simos_ebpf import BpfMapLookupElem, EbpfMapManager, SimOsEbpf
from heimdall_formula import guarded_returns, patch_map_relocations, path_predicate
from model import CONTEXT, FRAME, MAP_VALUES, PACKET, Entry, Gap, State, bv, unpack


REVISION = "90b4605e1c6ddae7ae5ead9738d5c1ff8e2843ad"
LE = "Iend_LE"
BE = "Iend_BE"
Z3 = claripy.backends.z3


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


class XdpLookup(BpfMapLookupElem):
    def run(self, map_fd_ptr, key_ptr):
        index = unique(self.state, map_fd_ptr, "lookup map handle")
        if index not in self.state.globals["world"].maps:
            raise Gap("exception", f"lookup handle {index} has no ELF map binding")
        result = super().run(map_fd_ptr, key_ptr)
        for i in range(1, 6):
            setattr(self.state.regs, f"R{i}", claripy.BVS(f"clobbered_r{i}", 64))
        return result


class XdpMaps(EbpfMapManager):
    def lookup_elem(self, state, map_info, key_bvv):
        world = state.globals["world"]
        return world.lookup(state, world.maps[map_info["index"]], key_bvv)


XDP_SYSCALLS = SimSyscallLibrary()
XDP_SYSCALLS.set_library_names("eBPF")
XDP_SYSCALLS.add("bpf_map_lookup_elem", XdpLookup)
XDP_SYSCALLS.add_number_mapping_from_dict("abi", {1: "bpf_map_lookup_elem"})


class XdpSimOS(SimOsEbpf):
    def __init__(self, project):
        super().__init__(project, syscall_library=XDP_SYSCALLS)


class XdpWorld:
    def __init__(self, domain, maps, limits, instructions, section_base):
        self.domain = domain
        self.maps = {map_.vma: map_ for map_ in maps}
        self.limits = limits
        self.instructions = instructions
        self.section_base = section_base
        self.length = to_angr(domain.length)
        self.input_names = set().union(*(to_angr(value).variables for value in (
            domain.length, *domain.packet,
            *(value for entry in domain.entries.values() for value in (entry.present, entry.value)),
        ) if not (z3.is_bv_value(value) or z3.is_true(value) or z3.is_false(value))))

    def initial(self, project, entry):
        state = project.factory.blank_state(addr=entry)
        state.solver.timeout = self.limits.timeout_ms
        state.regs.R1 = CONTEXT
        state.regs.R10 = FRAME
        state.memory.store(BPF_CALLER_SAVE_BASE, claripy.BVV(0, 80 * 8), endness=LE)
        initialize_bytes(state, CONTEXT, self.domain.context)
        initialize_bytes(state, PACKET, self.domain.packet)
        state.solver.add(to_angr(self.domain.guard))
        state.globals["events"] = ()
        state.globals["map_cells"] = {}
        state.globals["pc"] = (entry - self.section_base) // 8
        state.globals["world"] = self
        map_manager = XdpMaps()
        for index, map_ in self.maps.items():
            map_manager.create_map(index, map_.key_bytes, map_.value_bytes, map_.capacity,
                                   "array" if map_.array else "hash", map_.name)
        state.register_plugin("ebpf_map", map_manager)
        state.globals["steps"] = 0
        state.globals["back_edges"] = 0
        for identity, entry in self.domain.entries.items():
            self.add_cell(state, identity, entry)
        state.inspect.b("instruction", when=angr.BP_BEFORE, action=self.on_instruction)
        state.inspect.b("mem_read", when=angr.BP_BEFORE, action=self.on_read)
        state.inspect.b("mem_read", when=angr.BP_AFTER, action=self.on_read_value)
        state.inspect.b("reg_read", when=angr.BP_AFTER, action=self.on_register_value)
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

    def lookup(self, state, map_, key):
        pc = state.globals["pc"]
        if key.variables - self.input_names:
            raise Gap("exception", f"slot {pc}: lookup key depends on undefined data")
        cells = state.globals["map_cells"]
        if key.concrete or map_.array:
            key_int = unique(state, key, "ARRAY index")
            key_hex = key_int.to_bytes(map_.key_bytes, "little").hex()
            cell = cells.get((map_.name, key_hex))
            if cell is None and map_.array and key_int < map_.capacity:
                cell = self.add_cell(state, (map_.name, key_hex), map_.default(key_hex))
            result = claripy.BVV(0, 64) if cell is None else claripy.If(
                cell.present, claripy.BVV(cell.address, 64), claripy.BVV(0, 64))
        else:
            key_hex = None
            result = claripy.BVV(0, 64)
            for (name, named_key), cell in cells.items():
                if name == map_.name:
                    same = key == int.from_bytes(bytes.fromhex(named_key), "little")
                    result = claripy.If(same & cell.present, claripy.BVV(cell.address, 64), result)
        self.event(state, {
            "pc": pc, "kind": "helper", "helper": 1, "name": "map_lookup_elem",
            "resource": "map", "map": map_.name, "key": key_hex if key_hex is not None else to_z3(key),
            "key_width": map_.key_bytes, "key_value": to_z3(key),
            "present": to_z3(result != 0), "result": to_z3(result),
        })
        return result

    def on_instruction(self, state):
        delta = state.inspect.instruction - self.section_base
        pc, remainder = divmod(delta, 8)
        if remainder or pc not in self.instructions:
            raise Gap("exception", f"not an XDP instruction slot: {state.inspect.instruction:#x}")
        previous = state.globals["pc"]
        if state.globals["steps"] and pc <= previous:
            state.globals["back_edges"] += 1
            if state.globals["back_edges"] > self.limits.max_back_edges:
                raise Gap("loop_budget", f"back edge to slot {pc}")
        state.globals["pc"] = pc
        state.globals["steps"] += 1
        if state.globals["steps"] > self.limits.max_steps:
            raise Gap("step_budget", "instruction budget exhausted")
        insn = self.instructions[pc]
        if insn.code == 0x85 and insn.imm != 1:
            raise Gap("unknown_helper", f"slot {pc}: helper {insn.imm} has no XDP model")
        cls, mode = insn.code & 7, insn.code & 0xe0
        if ((cls == 0 and insn.code != 0x18)
                or (cls in (1, 2, 3) and mode != 0x60)):
            raise Gap("unsupported_instruction", f"slot {pc}: unsupported XDP opcode {insn.code:#04x}")

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

    def on_read_value(self, state):
        if state.inspect.mem_read_expr.variables - self.input_names:
            raise Gap("exception", "memory read depends on undefined data")

    def on_register_value(self, state):
        if state.inspect.reg_read_expr.variables - self.input_names:
            raise Gap("exception", "register read depends on undefined data")

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
        return to_z3(path_predicate(state))

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

    def __init__(self, data, expected, maps, instructions, artifact):
        self.instructions = instructions
        try:
            self.project = angr.Project(
                BytesIO(data), auto_load_libs=False,
                main_opts={"backend": ExtendedBPF}, simos=XdpSimOS,
            )
            loader = self.project.loader
            symbol = loader.main_object.get_symbol(artifact["entry"])
            if symbol is None or symbol.is_import:
                raise ValueError("CLE did not resolve the XDP entry symbol")
            self.entry = symbol.rebased_addr
            self.section_base = self.entry - artifact["entry_offset"]
            patch_map_relocations(self.project, artifact["bindings"], [m.name for m in maps])
            if loader.memory.load(self.section_base, len(expected)) != expected:
                raise ValueError("CLE XDP bytes differ from the validated ELF and map bindings")
        except (angr.errors.AngrError, KeyError) as err:
            raise ValueError(f"CLE eBPF ELF load failed: {err}") from err
        artifact.update(cle_backend=type(loader.main_object).__name__,
                        simos=type(self.project.simos).__name__,
                        entry_address=self.entry, section_address=self.section_base)

    @staticmethod
    def return_formula(exits):
        output = claripy.BVS("xdp_action", 32, explicit_name=True)
        paths = ((to_angr(state.guard), to_angr(state.regs[0])[31:0]) for state in exits)
        return to_z3(guarded_returns(paths, output))

    def run(self, domain, maps, limits):
        world = XdpWorld(domain, maps, limits, self.instructions, self.section_base)
        state = world.initial(self.project, self.entry)
        simgr = self.project.factory.simulation_manager(
            state, save_unconstrained=True,
            resilience=(Gap, angr.errors.AngrError, claripy.errors.ClaripyError, NotImplementedError),
        )
        exits, gaps = [], []

        def limit_paths(manager):
            used = len(manager.deadended) + len(manager.errored) + len(manager.unconstrained)
            capacity = max(0, limits.max_paths - used)
            manager.stashes.setdefault("path_budget", []).extend(manager.active[capacity:])
            del manager.active[capacity:]
            return manager

        def record(state, kind, detail):
            try:
                guard = world.guard(state)
            except Gap:
                guard = domain.guard
            gaps.append({"kind": kind, "detail": detail, "guard": guard,
                         "pc": state.globals["pc"], "steps": state.globals["steps"],
                         "back_edges": state.globals["back_edges"]})

        simgr.run(n=limits.max_steps + 2, step_func=limit_paths)
        for state in simgr.deadended:
            try:
                if (state.addr != BPF_EXIT_SENTINEL
                        or self.instructions[state.globals["pc"]].code != 0x95):
                    raise Gap("exception", f"angr stopped before XDP EXIT at {state.addr:#x}")
                exits.append(world.exit(state))
            except Gap as err:
                record(state, err.kind, str(err))
            except ClaripySolverInterruptError as err:
                record(state, "solver_timeout", str(err))
        for err in simgr.errored:
            kind = err.error.kind if isinstance(err.error, Gap) else "exception"
            if isinstance(err.error, ClaripySolverInterruptError):
                kind = "solver_timeout"
            record(err.state, kind, str(err.error))
        for stash, states in simgr.stashes.items():
            if stash in {"deadended", "unsat"}:
                continue
            kind = {"active": "step_budget", "unconstrained": "symbolic_address",
                    "path_budget": "path_budget"}.get(stash, "exception")
            for state in states:
                record(state, kind, f"unfinished XDP state in angr stash {stash}")
        return exits, gaps
