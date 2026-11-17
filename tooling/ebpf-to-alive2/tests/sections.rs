use ebpf_to_alive2::{load_function, parse, ElfError};

fn corpus(name: &str) -> Vec<u8> {
    let path = format!(
        "{}/../../alive2/corpus/bpf/{name}/bpf.o",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read(path).unwrap_or_else(|err| panic!("read {name}: {err}"))
}

fn code_names(bytes: &[u8]) -> Vec<(String, u64)> {
    let object = parse(bytes).expect("bpf object");
    object
        .code_sections()
        .map(|section| (section.name.clone(), section.size))
        .collect()
}

#[test]
fn div2_code_is_xdp_not_empty_text() {
    let names = code_names(&corpus("div2"));
    assert_eq!(names, vec![("xdp".to_string(), 0xe8)]);
}

#[test]
fn just_drop_code_is_xdp1() {
    let names = code_names(&corpus("just_drop"));
    assert_eq!(names, vec![("xdp1".to_string(), 0x110)]);
}

#[test]
fn executable_and_big_endian_elf_are_rejected() {
    let mut bytes = corpus("div2");
    bytes[16..18].copy_from_slice(&2u16.to_le_bytes());
    assert_eq!(parse(&bytes), Err(ElfError::NotRelocatable));
    bytes[16..18].copy_from_slice(&1u16.to_le_bytes());
    bytes[5] = 2;
    assert_eq!(parse(&bytes), Err(ElfError::NotLittleEndian));
}

#[test]
fn partial_symbol_and_relocation_entries_return_errors() {
    for kind in [2, 9] {
        let mut bytes = corpus("just_drop");
        let object = parse(&bytes).unwrap();
        let index = object
            .sections
            .iter()
            .position(|section| section.sh_type == kind)
            .unwrap();
        let size = object.sections[index].size;
        let table = u64::from_le_bytes(bytes[40..48].try_into().unwrap()) as usize;
        bytes[table + index * 64 + 32..table + index * 64 + 40]
            .copy_from_slice(&(size - 1).to_le_bytes());
        assert!(load_function(&bytes, None)
            .err()
            .unwrap()
            .contains("partial entry"));
    }
}

#[test]
fn named_entry_cannot_accidentally_include_other_functions() {
    let mut bytes = corpus("just_drop");
    let object = parse(&bytes).unwrap();
    let table = object
        .sections
        .iter()
        .find(|section| section.sh_type == 2)
        .unwrap();
    let code = object
        .sections
        .iter()
        .position(|section| section.is_code())
        .unwrap();
    let at = table.offset as usize + 24;
    bytes[at + 4] = 2;
    bytes[at + 6..at + 8].copy_from_slice(&(code as u16).to_le_bytes());
    let error = load_function(&bytes, Some("xdp_prog1")).err().unwrap();
    assert!(error.contains("multiple functions"), "{error}");
}

#[test]
fn function_must_cover_the_selected_section() {
    let mut bytes = corpus("just_drop");
    let object = parse(&bytes).unwrap();
    let table = object
        .sections
        .iter()
        .find(|section| section.sh_type == 2)
        .unwrap();
    let at = (table.offset as usize..(table.offset + table.size) as usize)
        .step_by(24)
        .find(|at| bytes[*at + 4] & 0xf == 2)
        .unwrap();
    bytes[at + 8..at + 16].copy_from_slice(&8u64.to_le_bytes());
    assert!(load_function(&bytes, None)
        .err()
        .unwrap()
        .contains("does not span"));
}
#[test]
fn truncated_and_non_bpf_fail() {
    assert_eq!(parse(&[]), Err(ElfError::Truncated));
    assert_eq!(parse(&[0; 64]), Err(ElfError::BadMagic));
    let mut bytes = corpus("div2");
    bytes[18] = 0;
    bytes[19] = 0;
    assert_eq!(parse(&bytes), Err(ElfError::NotBpf));
}
