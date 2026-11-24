"""XDP subset of HEIMDALL's c2rust_translation/generate_formula.py.

Source at 90b4605e1c6ddae7ae5ead9738d5c1ff8e2843ad. See README.md and
angr_ebpf/LICENSE.
"""

import claripy


def patch_map_relocations(project, bindings, map_symbol_names):
    """Patch the validated R_BPF_64_64 map LDDWs in CLE's loaded image."""
    # HEIMDALL's patch_ebpf_relocations resolves sites by ELF file offset
    # and writes the map manager's sequential index into the LDDW immediate.
    map_indices = {name: i for i, name in enumerate(map_symbol_names)}
    for binding in bindings:
        patch_addr = project.loader.main_object.offset_to_addr(binding["file_offset"])
        if patch_addr is None or project.loader.memory.load(patch_addr, 1) != b"\x18":
            raise ValueError(f"slot {binding['pc']}: CLE did not load the map LDDW")
        map_idx = map_indices[binding["symbol"]]
        project.loader.memory.store(patch_addr + 4, map_idx.to_bytes(4, "little"))
        # XDP accepts the ELF pseudo-map source field. The lifter consumes
        # an ordinary LDDW of the resolved index.
        regs = project.loader.memory.load(patch_addr + 1, 1)[0]
        project.loader.memory.store(patch_addr + 1, bytes([regs & 15]))
        binding.update(address=patch_addr, map_index=map_idx)


def path_predicate(state):
    return claripy.And(*state.solver.constraints)


def guarded_returns(paths, output):
    """Disjoin the guarded return expressions as in generate_formula_for_program."""
    return claripy.Or(*(claripy.And(guard, output == value) for guard, value in paths))
