use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let lean_prefix = Command::new("lean")
        .args(["--print-prefix"])
        .output()
        .expect("lean --print-prefix");
    assert!(lean_prefix.status.success());
    let lean_prefix = String::from_utf8(lean_prefix.stdout).unwrap();
    let lean_prefix = lean_prefix.trim();

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let repo_root = manifest_dir.parent().unwrap();
    let lake_lib = repo_root.join(".lake/build/lib");
    let lean_lib = PathBuf::from(lean_prefix).join("lib/lean");

    #[cfg(target_os = "macos")]
    {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lake_lib.display());
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());
    }
    #[cfg(target_os = "linux")]
    {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lake_lib.display());
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());
    }

    let bin = repo_root.join("esp32c3.bin");
    let decoder = repo_root.join("decode_imc.py");
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let out_rs = out_dir.join("esp32c3_insns.rs");
    let generated = Command::new("python3")
        .arg(&decoder)
        .arg("--compact-rust")
        .arg(&bin)
        .output()
        .expect("python3 decode_imc.py --compact-rust");
    assert!(
        generated.status.success(),
        "decode_imc.py failed: {}",
        String::from_utf8_lossy(&generated.stderr)
    );
    fs::write(&out_rs, generated.stdout).expect("write esp32c3_insns.rs");

    println!("cargo:rerun-if-changed={}", bin.display());
    println!("cargo:rerun-if-changed={}", decoder.display());
}
