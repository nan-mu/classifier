use ebpf_to_alive2::{parse, ElfError};

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
fn truncated_and_non_bpf_fail() {
    assert_eq!(parse(&[]), Err(ElfError::Truncated));
    assert_eq!(parse(&[0; 64]), Err(ElfError::BadMagic));
    let mut bytes = corpus("div2");
    bytes[18] = 0;
    bytes[19] = 0;
    assert_eq!(parse(&bytes), Err(ElfError::NotBpf));
}
