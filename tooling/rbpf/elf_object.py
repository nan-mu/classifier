"""Load the XDP section and its BTF map references from a release ELF object."""

from dataclasses import dataclass
from io import BytesIO
import struct

from elftools.common.exceptions import ELFError
from elftools.elf.elffile import ELFFile
from elftools.elf.relocation import RelocationSection
from elftools.elf.sections import SymbolTableSection

from machine import Map, decode


@dataclass(frozen=True)
class BtfType:
    kind: int
    name: str
    value: int
    data: tuple


class Btf:
    # Payload sizes in u32 words after the common btf_type header.
    FIXED = {1: 1, 3: 3, 14: 1, 17: 1}
    PER_ITEM = {4: 3, 5: 3, 6: 2, 13: 2, 15: 3, 19: 3}
    MODIFIERS = {8, 9, 10, 11, 18}

    def __init__(self, data):
        if len(data) < 24:
            raise ValueError("truncated BTF header")
        magic, version, flags, header, typ_off, typ_len, str_off, str_len = struct.unpack_from(
            "<HBB5I", data
        )
        if (magic != 0xeb9f or version != 1 or flags or header < 24
                or header + max(typ_off + typ_len, str_off + str_len) > len(data)):
            raise ValueError("invalid BTF header or sections")
        self.strings = data[header + str_off:header + str_off + str_len]
        start = header + typ_off
        end = start + typ_len
        self.types = [None]
        while start < end:
            if end - start < 12:
                raise ValueError("truncated BTF type header")
            name, info, value = struct.unpack_from("<III", data, start)
            kind, count = (info >> 24) & 31, info & 0xffff
            if not 1 <= kind <= 19:
                raise ValueError(f"unknown BTF kind {kind}")
            words = self.FIXED.get(kind, 0) + self.PER_ITEM.get(kind, 0) * count
            start += 12
            if start + 4 * words > end:
                raise ValueError("truncated BTF type payload")
            payload = struct.unpack_from(f"<{words}I", data, start)
            start += 4 * words
            self.types.append(BtfType(kind, self.string(name), value, payload))

    def string(self, offset):
        end = self.strings.find(b"\0", offset)
        if end < 0:
            raise ValueError("invalid BTF string offset")
        return self.strings[offset:end].decode("utf-8")

    def type(self, type_id):
        seen = set()
        while 0 < type_id < len(self.types) and type_id not in seen:
            seen.add(type_id)
            item = self.types[type_id]
            if item.kind not in self.MODIFIERS:
                return item
            type_id = item.value
        raise ValueError(f"invalid BTF type chain at ID {type_id}")

    def map(self, name, address, symbol_size):
        definitions = []
        for section in self.types[1:]:
            if section.kind != 15 or section.name != ".maps":
                continue
            for var_id, _, _ in zip(*[iter(section.data)] * 3):
                var = self.type(var_id)
                if var.kind == 14 and var.name == name:
                    definitions.append(self.type(var.value))
        if len(definitions) != 1 or definitions[0].kind != 4:
            raise ValueError(f"{name}: missing or ambiguous BTF map struct in .maps")
        definition = definitions[0]
        if definition.value != symbol_size:
            raise ValueError(f"{name}: BTF map struct size differs from ELF symbol")
        members = {}
        for label, type_id, _ in zip(*[iter(definition.data)] * 3):
            field = self.string(label)
            if field in members:
                raise ValueError(f"{name}: duplicate BTF map field {field}")
            members[field] = self.type(type_id)

        def referent(field):
            ptr = members.get(field)
            if ptr is None or ptr.kind != 2:
                raise ValueError(f"{name}: BTF map field {field} must be a pointer")
            return self.type(ptr.value)

        def number(field):
            array = referent(field)
            if array.kind != 3:
                raise ValueError(f"{name}: BTF field {field} is not an encoded constant")
            return array.data[2]

        def size(field):
            item = referent(field)
            if item.kind not in (1, 4, 5, 6, 16, 19) or not 1 <= item.value <= 256:
                raise ValueError(f"{name}: unsupported BTF size for {field}")
            return item.value

        kind, capacity = number("type"), number("max_entries")
        key, value = size("key"), size("value")
        if kind not in (1, 2) or capacity < 1 or kind == 2 and key != 4:
            raise ValueError(f"{name}: unsupported map type, capacity or ARRAY key width")
        return Map(name, kind, capacity, address, key, value)


def validate_register_fields(instructions):
    for pc, insn in instructions.items():
        code = insn.code
        cls, op = code & 7, code & 0xf0
        register_source = bool(code & 8)
        writes_register = cls in (1, 4, 7) or code == 0x18
        if writes_register and insn.dst == 10:
            raise ValueError(f"slot {pc}: write to the XDP frame pointer")
        if cls in (5, 6) and op == 0x80 and (code != 0x85 or insn.src != 0):
            raise ValueError(f"slot {pc}: only immediate XDP helper calls are supported")
        # Heimdall covers the ordinary forms used by this release. Reject
        # reserved ALU fields and signed DIV/MOD or MOVSX forms at this seam.
        if cls in (4, 7):
            if op == 0xd0:
                if insn.src or insn.offset or insn.imm not in (16, 32, 64) or cls == 7:
                    raise ValueError(f"slot {pc}: unsupported or invalid END encoding")
            elif (insn.offset or register_source and insn.imm
                  or not register_source and insn.src
                  or op == 0x80 and (register_source or insn.imm)):
                raise ValueError(f"slot {pc}: invalid or unsupported ALU encoding ({code:#04x})")
        elif cls in (5, 6) and op not in (0, 0x80, 0x90):
            if register_source and insn.imm or not register_source and insn.src:
                raise ValueError(f"slot {pc}: nonzero reserved jump field")
        elif cls in (1, 2, 3) and code & 0xe0 == 0x60:
            if cls == 2 and insn.src or cls != 2 and insn.imm:
                raise ValueError(f"slot {pc}: nonzero reserved memory field")


def load_xdp(data):
    try:
        elf = ELFFile(BytesIO(data))
        if (elf.elfclass != 64 or not elf.little_endian
                or elf["e_type"] != "ET_REL" or elf["e_machine"] != "EM_BPF"):
            raise ValueError("expected ELF64 little-endian ET_REL / EM_BPF")
        sections = list(elf.iter_sections())
        candidates = [(i, section) for i, section in enumerate(sections)
                      if section.name == "xdp" or section.name.startswith("xdp/")]
        if len(candidates) != 1:
            raise ValueError("expected one XDP entry section")
        index, section = candidates[0]
        if section["sh_type"] != "SHT_PROGBITS" or not section["sh_flags"] & 4:
            raise ValueError(f"{section.name}: XDP section is not executable")
        symbols = elf.get_section_by_name(".symtab")
        if not isinstance(symbols, SymbolTableSection):
            raise ValueError("missing ELF symbol table")
        functions = [sym for sym in symbols.iter_symbols()
                     if sym["st_shndx"] == index and sym["st_info"]["type"] == "STT_FUNC"
                     and sym["st_info"]["bind"] == "STB_GLOBAL"]
        code = section.data()
        if len(functions) != 1:
            raise ValueError(f"{section.name}: expected a unique global XDP entry symbol")
        entry = functions[0]
        if entry["st_value"] % 8 or not 0 <= entry["st_value"] < len(code):
            raise ValueError(f"{section.name}: invalid entry offset")

        image, maps, bindings = relocate(elf, sections, index, code)
        instructions = decode(image, 0)
        validate_register_fields(instructions)
        if entry["st_value"] // 8 not in instructions:
            raise ValueError(f"{section.name}: entry is not an instruction slot")
        return image, maps, instructions, {
            "section": section.name, "entry": entry.name,
            "entry_offset": entry["st_value"], "bindings": bindings,
        }, code
    except (ELFError, struct.error, IndexError) as err:
        raise ValueError(f"invalid eBPF ELF object: {err}") from err


def relocate(elf, sections, index, code):
    image = bytearray(code)
    bindings, maps = [], {}
    slots = set()
    btf = None
    for relocations in sections:
        if not isinstance(relocations, RelocationSection) or relocations["sh_info"] != index:
            continue
        symbols = elf.get_section(relocations["sh_link"])
        if not isinstance(symbols, SymbolTableSection):
            raise ValueError(f"{relocations.name}: missing relocation symbol table")
        for reloc in relocations.iter_relocations():
            offset = reloc["r_offset"]
            site = f"{relocations.name}+{offset:#x}"
            if (reloc["r_info_type"] != 1 or offset % 8 or offset + 16 > len(image)
                    or offset in slots or image[offset] != 0x18
                    or image[offset + 1] >> 4 not in (0, 1)
                    or image[offset + 2:offset + 16] != bytes(14)
                    or reloc.is_RELA() and reloc["r_addend"] != 0):
                raise ValueError(f"{site}: expected R_BPF_64_64 at an unbound lddw")
            slots.add(offset)
            symbol = symbols.get_symbol(reloc["r_info_sym"])
            target = symbol["st_shndx"]
            if (not isinstance(target, int) or not 0 < target < len(sections)
                    or sections[target].name != ".maps" or not symbol.name
                    or symbol["st_info"]["type"] != "STT_OBJECT"
                    or symbol["st_size"] < 1
                    or symbol["st_value"] + symbol["st_size"] > sections[target].data_size):
                raise ValueError(f"{site}: symbol {symbol.name!r} is not a .maps object")
            if btf is None:
                section = elf.get_section_by_name(".BTF")
                if section is None:
                    raise ValueError(f"{site}: .BTF is required for map definitions")
                btf = Btf(section.data())
            identity = (target, symbol["st_value"], symbol.name)
            if identity not in maps:
                try:
                    maps[identity] = btf.map(symbol.name, 0x500000 + 8 * len(maps), symbol["st_size"])
                except ValueError as err:
                    raise ValueError(f"{site}: {err}") from err
            map_ = maps[identity]
            # Heimdall consumes an ordinary LDDW of the handle. Preserve
            # the original symbol and slot in the report.
            image[offset + 1] &= 15
            struct.pack_into("<I", image, offset + 4, map_.vma)
            bindings.append({"section": relocations.name, "offset": offset,
                             "pc": offset // 8, "symbol": symbol.name, "map": map_.name})
    if len({map_.name for map_ in maps.values()}) != len(maps):
        raise ValueError("duplicate logical map name across XDP relocations")
    return bytes(image), tuple(maps.values()), bindings
