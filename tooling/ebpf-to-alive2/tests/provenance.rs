use ebpf_to_alive2::{decode, lift, Func};

fn instruction(opcode: u8, dst: u8, src: u8, off: i16, imm: i32) -> [u8; 8] {
    let mut bytes = [opcode, dst | (src << 4), 0, 0, 0, 0, 0, 0];
    bytes[2..4].copy_from_slice(&off.to_le_bytes());
    bytes[4..8].copy_from_slice(&imm.to_le_bytes());
    bytes
}

fn program(code: &[[u8; 8]]) -> Func {
    let bytes = code.concat();
    Func {
        name: "provenance".into(),
        section: "xdp".into(),
        insns: decode(&bytes).expect("decode"),
        bytes,
        relocs: vec![],
    }
}

#[test]
fn integers_and_truncated_packet_addresses_cannot_be_dereferenced() {
    let scalar = program(&[
        instruction(0xb7, 2, 0, 0, 128),
        instruction(0x71, 0, 2, 0, 0),
        instruction(0x95, 0, 0, 0, 0),
    ]);
    assert!(lift(&scalar)
        .err()
        .unwrap()
        .contains("not a dereferenceable pointer"));
    let truncated = program(&[
        instruction(0x61, 2, 1, 0, 0),
        instruction(0xbc, 3, 2, 0, 0),
        instruction(0x71, 0, 3, 0, 0),
        instruction(0x95, 0, 0, 0, 0),
    ]);
    assert!(lift(&truncated)
        .err()
        .unwrap()
        .contains("not a dereferenceable pointer"));
}

#[test]
fn stack_spill_preserves_context_provenance_and_offset() {
    let func = program(&[
        instruction(0xbf, 2, 1, 0, 0),
        instruction(0x07, 2, 0, 0, 4),
        instruction(0x7b, 10, 2, -8, 0),
        instruction(0x79, 3, 10, -8, 0),
        instruction(0x61, 4, 3, -4, 0),
        instruction(0x71, 0, 4, 0, 0),
        instruction(0x95, 0, 0, 0, 0),
    ]);
    let compiled = lift(&func).expect("typed context spill");
    assert!(compiled.alive.contains(" = load ptr,"));
    assert!(compiled.alive.contains("store ptr "));
    assert!(compiled.alive.contains(" = gep ptr %pkt,"));
}

#[test]
fn partial_overwrite_cannot_preserve_a_spilled_pointer() {
    let func = program(&[
        instruction(0x7b, 10, 1, -8, 0),
        instruction(0x72, 10, 0, -7, 1),
        instruction(0x79, 2, 10, -8, 0),
        instruction(0x61, 0, 2, 0, 0),
        instruction(0x95, 0, 0, 0, 0),
    ]);
    assert!(lift(&func)
        .err()
        .unwrap()
        .contains("incompatible pointer spill"));
}

#[test]
fn pointer_integer_join_is_rejected() {
    let func = program(&[
        instruction(0x15, 1, 0, 2, 0),
        instruction(0x61, 2, 1, 0, 0),
        instruction(0x05, 0, 0, 1, 0),
        instruction(0xb7, 2, 0, 0, 123),
        instruction(0x71, 0, 2, 0, 0),
        instruction(0x95, 0, 0, 0, 0),
    ]);
    assert!(lift(&func)
        .err()
        .unwrap()
        .contains("different value on another"));
}

#[test]
fn mov32_does_not_read_an_uninitialized_destination() {
    let func = program(&[
        instruction(0xb7, 2, 0, 0, -1),
        instruction(0xbc, 0, 2, 0, 0),
        instruction(0x95, 0, 0, 0, 0),
    ]);
    let compiled = lift(&func).expect("mov32");
    assert!(compiled.alive.contains("trunc i64 -1 to i32"));
    assert!(compiled.alive.contains(" = zext i32 "));
}

#[test]
fn empty_or_unreachable_programs_return_errors() {
    assert!(lift(&program(&[]))
        .err()
        .unwrap()
        .contains("no instructions"));
    let func = program(&[
        instruction(0xb7, 0, 0, 0, 0),
        instruction(0x95, 0, 0, 0, 0),
        instruction(0xb7, 0, 0, 0, 1),
        instruction(0x95, 0, 0, 0, 0),
    ]);
    assert!(lift(&func).err().unwrap().contains("unreachable"));
}
