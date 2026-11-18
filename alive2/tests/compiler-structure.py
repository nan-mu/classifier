#!/usr/bin/env python3
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import struct
import subprocess
import tempfile


def insn(op, dst=0, src=0, off=0, imm=0):
    return struct.pack('<BBhi', op, dst | src << 4, off, imm)


def elf(code, with_map=False):
    sections = [('fixture', 1, 4, code, 0, 0, 8, 0), ('.shstrtab', 3, 0, b'', 0, 0, 1, 0)]
    if with_map:
        symbol = bytes(24) + struct.pack('<IBBHQQ', 1, 0x11, 0, 6, 0, 16)
        sections += [('.symtab', 2, 0, symbol, 4, 1, 8, 24),
                     ('.strtab', 3, 0, b'\0counter\0', 0, 0, 1, 0),
                     ('.relfixture', 9, 0, struct.pack('<QQ', 0, (1 << 32) | 1), 3, 1, 8, 16),
                     ('.maps', 1, 3, bytes(16), 0, 0, 8, 0)]
    names = b'\0' + b''.join(name.encode() + b'\0' for name, *_ in sections)
    data, headers = bytearray(64), [bytes(64)]
    for name, kind, flags, body, link, info, align, size in sections:
        if name == '.shstrtab':
            body = names
        headers.append(struct.pack('<IIQQQQIIQQ', names.index(name.encode()), kind, flags, 0, len(data), len(body), link, info, align, size))
        data.extend(body)
    data[:16] = b'\x7fELF\x02\x01\x01' + bytes(9)
    struct.pack_into('<HHIQQQIHHHHHH', data, 16, 1, 247, 1, 0, 0, len(data), 0, 64, 0, 0, 64, len(headers), 2)
    return data + b''.join(headers)



FIXTURES = {
    'memoryattrs': [insn(0x18, dst=1), insn(0), insn(0xbf, dst=2, src=10), insn(0x07, dst=2, imm=-8), insn(0xb7, dst=3, imm=7), insn(0x63, dst=2, src=3), insn(0x85, imm=1), insn(0x79), insn(0x95)],
    'arithmetic': [insn(0xb7, imm=5), insn(0x07, imm=3), insn(0x95)],
    'condition': [insn(0xb7, imm=4), insn(0x15, off=1, imm=0), insn(0x95), insn(0x95)],
    'forward_jump': [insn(0x05, off=0), insn(0xb7, imm=8), insn(0x95)],
    'phi': [insn(0xb7, imm=4), insn(0x15, off=2, imm=0), insn(0xb7, imm=2), insn(0x05, off=1), insn(0xb7, imm=3), insn(0x95)],
    'loop_phi': [insn(0xb7, imm=0), insn(0x07, imm=1), insn(0x55, off=-2, imm=2), insn(0x95)],
    'i32div': [insn(0xb7, imm=9), insn(0xb7, dst=2, imm=2), insn(0x3c, src=2), insn(0x95)],
}


def run(args):
    result = subprocess.run([str(a) for a in args], capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr
    return result.stdout


def object_rows(text):
    rows = []
    block = None
    for line in text.splitlines():
        if line.startswith('bb '):
            block = line[3:]
        elif line.startswith('  '):
            rows.append((block, line.strip().split(' text=', 1)[0]))
    return rows


PROLOGUE = [
    ('%entry', 'alloca %stack ty=ptr ops=imm:i64:512 targets='),
    ('%entry', 'gep %fp ty=ptr ops=%stack:ptr,imm:i64:512 targets='),
    ('%entry', 'br br ty=void ops= targets=%s0'),
]
EXPECTED = {
    'memoryattrs': PROLOGUE + [
        ('%s0', 'gep %v0 ty=ptr ops=%fp:ptr,imm:i64:-8 targets='),
        ('%s0', 'trunc %v1 ty=i32 ops=imm:i64:7 targets='),
        ('%s0', 'store store ty=void ops=%v1:i32,%v0:ptr targets='),
        ('%s0', 'call %v2 ty=ptr ops=%map_counter:ptr,%v0:ptr targets= callee=bpf_map_lookup_elem attrs= memory(argmem: read, inaccessiblemem: readwrite)'),
        ('%s0', 'load %v3 ty=i64 ops=%v2:ptr targets='),
        ('%s0', 'ret return ty=i64 ops=%v3:i64 targets='),
    ],
    'arithmetic': PROLOGUE + [
        ('%s0', 'add %v0 ty=i64 ops=imm:i64:5,imm:i64:3 targets='),
        ('%s0', 'ret return ty=i64 ops=%v0:i64 targets='),
    ],
    'condition': PROLOGUE + [
        ('%s0', 'icmp %v0 ty=i1 ops=imm:i64:4,imm:i64:0 targets= predicate=0'),
        ('%s0', 'br br ty=void ops=%v0:i1 targets=%s3,%s2'),
        ('%s3', 'ret return ty=i64 ops=imm:i64:4 targets='),
        ('%s2', 'ret return ty=i64 ops=imm:i64:4 targets='),
    ],
    'forward_jump': PROLOGUE + [
        ('%s0', 'br br ty=void ops= targets=%s1'),
        ('%s1', 'ret return ty=i64 ops=imm:i64:8 targets='),
    ],
    'phi': PROLOGUE + [
        ('%s0', 'icmp %v0 ty=i1 ops=imm:i64:4,imm:i64:0 targets= predicate=0'),
        ('%s0', 'br br ty=void ops=%v0:i1 targets=%s4,%s2'),
        ('%s4', 'br br ty=void ops= targets=%s5'),
        ('%s2', 'br br ty=void ops= targets=%s5'),
        ('%s5', 'phi %s5_r0 ty=i64 ops=imm:i64:2,imm:i64:3 targets= incoming=[imm:i64:2,%s2][imm:i64:3,%s4]'),
        ('%s5', 'ret return ty=i64 ops=%s5_r0:i64 targets='),
    ],
    'loop_phi': PROLOGUE + [
        ('%s0', 'br br ty=void ops= targets=%s1'),
        ('%s1', 'phi %s1_r0 ty=i64 ops=imm:i64:0,%v0:i64 targets= incoming=[imm:i64:0,%s0][%v0:i64,%s1]'),
        ('%s1', 'add %v0 ty=i64 ops=%s1_r0:i64,imm:i64:1 targets='),
        ('%s1', 'icmp %v1 ty=i1 ops=%v0:i64,imm:i64:2 targets= predicate=1'),
        ('%s1', 'br br ty=void ops=%v1:i1 targets=%s1,%s3'),
        ('%s3', 'ret return ty=i64 ops=%v0:i64 targets='),
    ],
    'i32div': PROLOGUE + [
        ('%s0', 'trunc %v0 ty=i32 ops=imm:i64:9 targets='),
        ('%s0', 'trunc %v1 ty=i32 ops=imm:i64:2 targets='),
        ('%s0', 'icmp %v2 ty=i1 ops=%v1:i32,imm:i32:0 targets= predicate=0'),
        ('%s0', 'br br ty=void ops=%v2:i1 targets=%d3,%d4'),
        ('%d3', 'br br ty=void ops= targets=%d5'),
        ('%d4', 'udiv %v6 ty=i32 ops=%v0:i32,%v1:i32 targets='),
        ('%d4', 'br br ty=void ops= targets=%d5'),
        ('%d5', 'phi %v7 ty=i32 ops=imm:i32:0,%v6:i32 targets= incoming=[imm:i32:0,%d3][%v6:i32,%d4]'),
        ('%d5', 'zext %v8 ty=i64 ops=%v7:i32 targets='),
        ('%d5', 'ret return ty=i64 ops=%v8:i64 targets='),
    ],
}


def validate_origin(metadata, text, raw):
    assert metadata['origin_revision'] == 2
    rows = metadata['instructions']
    slots = {r['slot'] for r in rows}
    assert len(slots) == len(rows)
    covered = set()
    for row in rows:
        data = bytes.fromhex(row['bytes'])
        assert len(data) == (16 if raw[row['offset']] == 0x18 else 8)
        assert data == raw[row['offset']:row['offset'] + len(data)]
        covered.update(range(row['offset'], row['offset'] + len(data)))
        assert row['decoded'] is not None
        decoded = next(iter(row['decoded'].values()))
        assert decoded['index'] == row['slot']
    assert covered == set(range(len(raw)))
    records = metadata['generated_instructions']
    ids = {r['id'] for r in records}
    assert len(ids) == len(records)
    emitted, block = [], None
    blocks = set()
    for line in text.splitlines():
        line = line.strip()
        if line.endswith(':'):
            block = line[:-1]
            blocks.add(block)
        elif block and line and line != '}':
            emitted.append((block, line))
    assert Counter(emitted) == Counter((r['block'], r['text']) for r in records)
    definitions = {r['result'] for r in records if r['result']}
    assert len(definitions) == sum(bool(r['result']) for r in records)
    expected_names = set(re.findall(r'%[a-zA-Z_][a-zA-Z_0-9]*', text.split('{', 1)[0])) | definitions
    edges = []
    for record in records:
        assert record['slot'] is None or record['slot'] in slots
        assert record['block'] in blocks
        assert record['opcode'] == record['text'].split(' = ')[-1].split()[0]
        for target in record['targets']:
            assert target in blocks
            edges.append({'from': record['block'], 'to': target, 'instruction': record['id']})
        for incoming in record['phi_inputs']:
            assert incoming['predecessor'] in blocks
            assert set(incoming['source_slots']) <= slots
        if record['opcode'] == 'phi':
            assert record['phi_inputs']
            for incoming in record['phi_inputs']:
                assert any(r['block'] == incoming['predecessor'] and record['block'] in r['targets'] for r in records)
        references = set(re.findall(r'%[a-zA-Z_][a-zA-Z_0-9]*', record['text']))
        assert references <= expected_names | {'%' + b for b in blocks}
    assert edges == metadata['generated_cfg_edges']
    source_blocks = {b['start'] for b in metadata['source_cfg_blocks']}
    assert set(slot for b in metadata['source_cfg_blocks'] for slot in b['slots']) == slots
    assert all(a in source_blocks and b in source_blocks for a, b in metadata['source_cfg_edges'])
    for row in rows:
        assert row['generated_instruction_ids'] == [r['id'] for r in records if r['slot'] == row['slot']]
        assert set(row['ir']) == {r['result'] for r in records if r['slot'] == row['slot'] and r['result']}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--loader', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='alive-structure-') as directory:
        root = Path(directory)
        for name, code in FIXTURES.items():
            original, alive, origin, report = [root / (name + ext) for ext in ['.o', '.alive', '.json', '.toml']]
            original.write_bytes(elf(b''.join(code), with_map=name == 'memoryattrs'))
            run([args.compiler, 'compile', original, '--out', alive, '--origin', origin, '--report', report, '--source-root', args.source_root])
            structure = run([args.loader, '--inspect', alive])
            expected_header = ['fn fixture i64', 'mem memory(argmem: readwrite, inaccessiblemem: readwrite)']
            if name == 'memoryattrs':
                expected_header += ['decl bpf_map_lookup_elem ptr args 2 mem memory(argmem: read, inaccessiblemem: readwrite) types=ptr;ptr;']
            expected_header += ['in %ctx ptr', 'in %pkt ptr', 'in %pkt_base i64']
            if name == 'memoryattrs':
                expected_header += ['in %map_counter ptr']
            assert structure.split('bb ', 1)[0].splitlines() == expected_header
            rows = object_rows(structure)
            assert rows == EXPECTED[name], (name, rows)
            metadata = json.loads(origin.read_text())
            validate_origin(metadata, alive.read_text(), b''.join(code))
            if name == 'loop_phi':
                phi = next(r for r in metadata['generated_instructions'] if r['opcode'] == 'phi')
                assert phi['slot'] == 1
                assert phi['phi_inputs'] == [
                    {'value': '0', 'predecessor': 's0', 'source_slots': [0]},
                    {'value': '%v0', 'predecessor': 's1', 'source_slots': [1]},
                ]
                assert [1, 1] in metadata['source_cfg_edges']
            if name == 'phi':
                phi = next(r for r in metadata['generated_instructions'] if r['opcode'] == 'phi')
                assert phi['slot'] == 5
                assert phi['phi_inputs'] == [
                    {'value': '2', 'predecessor': 's2', 'source_slots': [2]},
                    {'value': '3', 'predecessor': 's4', 'source_slots': [4]},
                ]
    print(f'{len(FIXTURES)} independent compiler-to-loader structural fixtures passed')


if __name__ == '__main__':
    main()
