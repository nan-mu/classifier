//! RV32IMC prefixgen from `just_tx.elf`.

use classifier::rv32::Environment;
use classifier::{Arch, prefixgen_rv32_elf, write_prefixgen};
use std::path::PathBuf;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn just_tx_elf_prefixgen_prog_format() {
    let env = Environment::from_toml(
        &std::fs::read_to_string(root().join("config/esp32c3.environment.toml")).unwrap(),
    )
    .unwrap();
    let insns = prefixgen_rv32_elf(&root().join("example/just_tx.elf"), &env).expect("prefixgen");
    assert_eq!(insns.len(), 79);

    let line0 = insns[0].emit_line(2);
    assert!(
        line0.starts_with(" 0: 4111    , "),
        "compressed machine field: {line0}"
    );
    assert!(line0.contains("w2 += 0xfffffff0"), "{line0}");
    assert!(!line0.contains("#x"), "{line0}");

    let out = std::env::temp_dir().join(format!("classifier-just-tx-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&out);
    write_prefixgen(&out, Arch::Rv32imc, &insns).unwrap();
    assert!(out.join("rv32imc/prefixgen/prog.txt").is_file());
}
