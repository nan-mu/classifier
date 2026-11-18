use ebpf_to_alive2::{decode, lift, load_function, Func, Status};

fn op(code: u8, dst: u8, src: u8, off: i16, imm: i32) -> [u8; 8] {
    let mut raw = [code, dst | src << 4, 0, 0, 0, 0, 0, 0];
    raw[2..4].copy_from_slice(&off.to_le_bytes());
    raw[4..].copy_from_slice(&imm.to_le_bytes());
    raw
}
fn program(code: &[[u8; 8]]) -> Func {
    let bytes = code.concat();
    Func {
        name: "outcomes".into(),
        section: "xdp".into(),
        insns: decode(&bytes).unwrap(),
        bytes,
        relocs: vec![],
    }
}
fn helper(code: &[[u8; 8]]) -> Func {
    let mut func = load_function(
        include_bytes!("../../../alive2/corpus/bpf/just_drop/bpf.o"),
        None,
    )
    .unwrap();
    func.bytes = code.concat();
    func.insns = decode(&func.bytes).unwrap();
    func.relocs.truncate(1);
    func.relocs[0].slot = 0;
    func
}

#[test]
fn categories_and_locations_are_typed() {
    assert_eq!(
        load_function(b"bad ELF", None).unwrap_err().status,
        Status::InvalidElf
    );
    let error = decode(&op(0xb7, 11, 0, 0, 0)).unwrap_err();
    assert_eq!(
        (error.status, error.stage, error.slot, error.register),
        (Status::InvalidInstruction, "decode", Some(0), Some(11))
    );
    let error = decode(&op(0x85, 0, 1, 0, 0)).unwrap_err();
    assert_eq!((error.status, error.slot), (Status::Unsupported, Some(0)));
    let error = lift(&program(&[op(0x95, 0, 0, 0, 0)])).err().unwrap();
    assert_eq!(
        (error.status, error.slot, error.register),
        (Status::Unsupported, Some(0), Some(0))
    );
    let error = lift(&program(&[op(0x05, 0, 0, 1, 0)])).err().unwrap();
    assert_eq!(
        (error.status, error.stage, error.slot),
        (Status::InvalidInstruction, "cfg", Some(0))
    );
}

#[test]
fn packet_facts_survive_mov64_but_not_narrow_or_sign_extending_moves() {
    for (code, off, accepted) in [
        (0xbf, 0, true),
        (0xbc, 0, false),
        (0xbf, 8, false),
        (0xbf, 16, false),
        (0xbf, 32, false),
    ] {
        let func = program(&[
            op(0x61, 2, 1, 0, 0),
            op(code, 3, 2, off, 0),
            op(0x71, 0, 3, 0, 0),
            op(0x95, 0, 0, 0, 0),
        ]);
        let result = lift(&func);
        if accepted {
            assert!(result.is_ok());
        } else {
            let error = result.err().unwrap();
            assert_eq!(
                (error.status, error.slot, error.register),
                (Status::Unsupported, Some(2), Some(3))
            );
        }
    }
}

#[test]
fn lookup_result_is_dereferenceable_and_helper_arguments_are_clobbered() {
    let prefix = [
        op(0x18, 1, 0, 0, 0),
        op(0, 0, 0, 0, 0),
        op(0xbf, 2, 10, 0, 0),
        op(0x07, 2, 0, 0, -8),
        op(0x85, 0, 0, 0, 1),
    ];
    let mut code = prefix.to_vec();
    code.extend([op(0x79, 0, 0, 0, 0), op(0x95, 0, 0, 0, 0)]);
    assert!(lift(&helper(&code)).is_ok());
    for reg in 1..=5 {
        let mut code = prefix.to_vec();
        code.extend([op(0xbf, 0, reg, 0, 0), op(0x95, 0, 0, 0, 0)]);
        let error = lift(&helper(&code)).err().unwrap();
        assert_eq!(
            (error.status, error.slot, error.register),
            (Status::Unsupported, Some(5), Some(reg))
        );
    }
}

#[test]
fn scalar_pointer_mixture_and_conflicting_phi_are_classified() {
    let code = [
        op(0xb7, 0, 0, 0, 1),
        op(0x0f, 0, 1, 0, 0),
        op(0x71, 0, 0, 0, 0),
        op(0x95, 0, 0, 0, 0),
    ];
    assert_eq!(
        lift(&program(&code)).err().unwrap().status,
        Status::Unsupported
    );
    let code = [
        op(0xb7, 0, 0, 0, 1),
        op(0x15, 0, 0, 2, 0),
        op(0xbf, 0, 1, 0, 0),
        op(0x05, 0, 0, 1, 0),
        op(0xb7, 0, 0, 0, 2),
        op(0x95, 0, 0, 0, 0),
    ];
    assert_eq!(
        lift(&program(&code)).err().unwrap().status,
        Status::Unsupported
    );
}

#[test]
fn phi_origin_uses_expanded_division_predecessor_and_source_definitions() {
    let func = program(&[
        op(0xb7, 0, 0, 0, 9),
        op(0x15, 0, 0, 2, 0),
        op(0x34, 0, 0, 0, 2),
        op(0x05, 0, 0, 1, 0),
        op(0xb7, 0, 0, 0, 3),
        op(0x95, 0, 0, 0, 0),
    ]);
    let compiled = lift(&func).unwrap();
    let phi = compiled
        .generated
        .iter()
        .find(|inst| inst.result.as_deref() == Some("%s5_r0"))
        .unwrap();
    assert_eq!(phi.slot, Some(5));
    let division = phi
        .phi_inputs
        .iter()
        .find(|input| input.source_slots == [2])
        .unwrap();
    assert!(division.predecessor.starts_with('d'));
    assert!(compiled
        .generated
        .iter()
        .any(|inst| inst.block == division.predecessor && inst.targets == ["s5"]));
    assert_eq!(
        phi.phi_inputs
            .iter()
            .find(|input| input.predecessor == "s4")
            .unwrap()
            .source_slots,
        [4]
    );
    assert_eq!(
        compiled
            .origin_insns
            .iter()
            .find(|(slot, _)| *slot == 0)
            .unwrap()
            .1,
        Vec::<String>::new()
    );
}
