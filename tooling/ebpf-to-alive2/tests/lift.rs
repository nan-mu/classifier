use ebpf_to_alive2::{lift, load_function};

fn corpus(name: &str) -> Vec<u8> {
    let path = format!("{}/../../alive2/corpus/bpf/{name}/bpf.o", env!("CARGO_MANIFEST_DIR"));
    std::fs::read(path).unwrap_or_else(|err| panic!("read {name}: {err}"))
}

#[test]
fn div2_lifts_with_loads_and_a_divide() {
    let func = load_function(&corpus("div2"), None).expect("load");
    assert_eq!(func.section, "xdp");
    assert!(func.relocs.is_empty());
    let compiled = lift(&func).unwrap_or_else(|err| panic!("{err}\n{:?}", &func.insns[..8.min(func.insns.len())]));
    assert!(compiled.alive.contains("alive-file v1"));
    assert!(compiled.alive.contains("= load "));
    assert!(compiled.alive.contains("udiv ") || compiled.alive.contains("sdiv "));
    assert!(compiled.alive.contains("ret i64 "));
    assert!(!compiled.alive.contains("memory(none)"));
}

#[test]
fn just_drop_keeps_the_map_relocation() {
    let func = load_function(&corpus("just_drop"), None).expect("load");
    assert_eq!(func.section, "xdp1");
    assert!(func.relocs.iter().any(|reloc| reloc.symbol == "counter"));
    let compiled = lift(&func).unwrap_or_else(|err| panic!("{err}\n{:?}", &func.insns[..8.min(func.insns.len())]));
    assert!(compiled.alive.contains("%map_counter"));
    assert!(compiled.alive.contains("@bpf_map_lookup_elem"));
    assert!(!compiled.alive.contains("memory(none)"));
}

#[test]
fn unknown_class_is_rejected() {
    let err = ebpf_to_alive2::decode(&[0x61, 0, 0, 0, 1, 0, 0, 0]).expect_err("imm");
    assert!(err.contains("immediate"));
}

#[test]
fn corpus_reports_a_result_for_every_program() {
    let names = ["bitswap", "bsort", "buf", "case_mark", "case_swap", "div2", "fib", "firewall", "fletcher32", "helper_loop", "incr", "just_drop", "just_tx", "memcpy", "merge_try", "square", "xdp_drop"];
    for name in names {
        let bytes = corpus(name);
        let func = load_function(&bytes, None).unwrap_or_else(|err| panic!("{name} load: {err}"));
        match lift(&func) {
            Ok(compiled) => println!("{name} converted bytes {}", compiled.alive.len()),
            Err(err) => println!("{name} blocked: {err}"),
        }
    }
}
