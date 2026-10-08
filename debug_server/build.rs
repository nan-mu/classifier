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

    let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let lake_lib = manifest_dir.parent().unwrap().join(".lake/build/lib");
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
}
