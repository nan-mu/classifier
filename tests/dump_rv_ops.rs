//! Manual dump helper. Ignored in the default suite; run with
//! `cargo test --test dump_rv_ops -- --ignored --nocapture`.

use classifier::prefixgen::{
    extract_rv32_image_from_path, prefixgen_rv32, split_rv32imc, U32OrU16,
};
use classifier::Environment;
use std::path::Path;

#[test]
#[ignore = "diagnostic dump; not part of the regression gate"]
fn dump_rv() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let env = Environment::load(&root.join("config/esp32c3.environment.toml")).unwrap();
    let image = extract_rv32_image_from_path(&root.join("example/just_tx.elf")).unwrap();
    let raw = split_rv32imc(&image).unwrap();
    let insns = prefixgen_rv32(&image, &env).unwrap();
    let target: riscv_isa::Target = "RV32IMC".parse().unwrap();
    for (i, (r, insn)) in raw.iter().zip(insns.iter()).enumerate() {
        let bytes = match r {
            U32OrU16::U16(w) => w.to_le_bytes().to_vec(),
            U32OrU16::U32(w) => w.to_le_bytes().to_vec(),
        };
        let (ins, _) = riscv_isa::decode_le_bytes(&bytes, &target).unwrap();
        println!("IDX {i} INS {ins:?} LINE {}", insn.emit_line(2));
    }
}
