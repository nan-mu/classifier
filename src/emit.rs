//! Write prefixgen / path outputs under `out/<arch>/<task>/`.

use anyhow::{Context, Result};
use std::fs;
use std::path::Path;

use crate::pathgen::{Path as InsnPath, TASK_PATHGEN};
use crate::predicate::{index_column_width, Insn};
use crate::prefixgen::{Arch, TASK_PREFIXGEN};

/// Replace `out_root/<arch>/prefixgen/` with a single `prog.txt` + `manifest.txt`.
pub fn write_prefixgen(out_root: &Path, arch: Arch, insns: &[Insn]) -> Result<std::path::PathBuf> {
    let dir = out_root.join(arch.as_str()).join(TASK_PREFIXGEN);
    if dir.exists() {
        fs::remove_dir_all(&dir)
            .with_context(|| format!("remove {}", dir.display()))?;
    }
    fs::create_dir_all(&dir).with_context(|| format!("create {}", dir.display()))?;

    let width = index_column_width(insns);
    let mut body = String::new();
    for insn in insns {
        body.push_str(&insn.emit_line(width));
        body.push('\n');
    }
    let prog = dir.join("prog.txt");
    fs::write(&prog, &body).with_context(|| format!("write {}", prog.display()))?;

    let manifest = format!(
        "arch = {}\ntask = {TASK_PREFIXGEN}\ninsns = {}\n",
        arch.as_str(),
        insns.len()
    );
    fs::write(dir.join("manifest.txt"), manifest)
        .with_context(|| format!("write manifest under {}", dir.display()))?;
    Ok(prog)
}

/// Replace `out_root/<arch>/pathgen/` with Huffman-coded `{code}.txt` + `manifest.txt`.
///
/// `code` starts at `0`; each forward branch appends `1` (taken) or `0` (fallthrough).
pub fn write_pathgen(out_root: &Path, arch: Arch, paths: &[InsnPath]) -> Result<std::path::PathBuf> {
    let dir = out_root.join(arch.as_str()).join(TASK_PATHGEN);
    if dir.exists() {
        fs::remove_dir_all(&dir)
            .with_context(|| format!("remove {}", dir.display()))?;
    }
    fs::create_dir_all(&dir).with_context(|| format!("create {}", dir.display()))?;

    for path in paths {
        ensure_huffman_code(&path.code)?;
        let width = index_column_width(&path.insns);
        let mut body = String::new();
        for insn in &path.insns {
            body.push_str(&insn.emit_line(width));
            body.push('\n');
        }
        let file = dir.join(format!("{}.txt", path.code));
        fs::write(&file, &body).with_context(|| format!("write {}", file.display()))?;
    }

    let manifest = format!(
        "arch = {}\ntask = {TASK_PATHGEN}\npaths = {}\n",
        arch.as_str(),
        paths.len()
    );
    fs::write(dir.join("manifest.txt"), manifest)
        .with_context(|| format!("write manifest under {}", dir.display()))?;
    Ok(dir)
}

fn ensure_huffman_code(code: &str) -> Result<()> {
    anyhow::ensure!(
        !code.is_empty() && code.bytes().all(|b| b == b'0' || b == b'1'),
        "pathgen: invalid Huffman path code `{code}`"
    );
    Ok(())
}
