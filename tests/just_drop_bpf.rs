//! End-to-end prefixgen from `bpf.o`.

use classifier::{Arch, prefixgen_bpf_object, write_prefixgen};
use std::path::PathBuf;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn bpf_o_prefixgen_has_real_machine_codes() {
    let insns = prefixgen_bpf_object(&root().join("example/bpf.o")).expect("prefixgen bpf.o");
    assert_eq!(insns.len(), 58);

    let line0 = insns[0].emit_line(2);
    // Memory-order hex of `b4 00 00 00 01 00 00 00`.
    assert!(
        line0.starts_with(" 0: b400000001000000, "),
        "expected real opcode, got: {line0}"
    );
    assert!(line0.contains("w0 = 0x1"), "{line0}");
    assert!(!line0.contains("#x"), "{line0}");

    // lddw at 34 + empty continuation 35.
    assert_eq!(insns[34].index, 34);
    assert_eq!(insns[35].index, 35);
    assert!(insns[35].prefix.is_empty());

    let out = std::env::temp_dir().join(format!("classifier-bpf-o-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&out);
    write_prefixgen(&out, Arch::Bpf, &insns).unwrap();
    let text = std::fs::read_to_string(out.join("bpf/prefixgen/prog.txt")).unwrap();
    assert!(text.lines().next().unwrap().starts_with(" 0: b400000001000000, "));
    assert!(!text.contains("0: 0000000000000000,"));
}
