use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let lean_root = manifest_dir.parent().unwrap().parent().unwrap();

    let lean_prefix = Command::new("lean")
        .args(["--print-prefix"])
        .output()
        .expect("lean --print-prefix");
    assert!(lean_prefix.status.success());
    let lean_prefix = String::from_utf8(lean_prefix.stdout).unwrap();
    let lean_prefix = lean_prefix.trim();

    let lake_lib = lean_root.join(".lake/build/lib");
    let lean_lib = PathBuf::from(lean_prefix).join("lib/lean");
    let lean_include = PathBuf::from(lean_prefix).join("include");

    cc::Build::new()
        .file(manifest_dir.join("shim.c"))
        .include(&lean_include)
        .compile("lean_binding_shim");

    println!("cargo:rustc-link-search=native={}", lake_lib.display());
    println!("cargo:rustc-link-search=native={}", lean_lib.display());
    println!("cargo:rustc-link-lib=dylib=classifier_RV32IMC");
    println!("cargo:rustc-link-lib=dylib=classifier_CommonMath");
    println!("cargo:rustc-link-lib=dylib=leanshared");
    println!("cargo:rustc-link-lib=dylib=Init_shared");

    #[cfg(target_os = "macos")]
    {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lake_lib.display());
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());
    }

    println!("cargo:rerun-if-changed={}", manifest_dir.join("shim.c").display());
    println!("cargo:rerun-if-changed={}", lake_lib.display());
    println!("cargo:rerun-if-changed={}", lean_root.join("lakefile.lean").display());
}
