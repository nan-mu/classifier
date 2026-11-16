use crate::decode::{self, Insn};
use crate::elf::{self, Object, Section};

const SHT_REL: u32 = 9;
const SHT_SYMTAB: u32 = 2;
const R_BPF_64_64: u32 = 1;
const STT_FUNC: u8 = 2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reloc {
    pub slot: u32,
    pub symbol: String,
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub section: String,
    pub insns: Vec<Insn>,
    pub relocs: Vec<Reloc>,
    pub bytes: Vec<u8>,
}

pub fn load_function(bytes: &[u8], entry: Option<&str>) -> Result<Func, String> {
    let object = elf::parse(bytes).map_err(|err| format!("elf: {err:?}"))?;
    let code: Vec<&Section> = object.code_sections().collect();
    if code.is_empty() {
        return Err("no executable section with a non-zero size".into());
    }
    if code.len() > 1 && entry.is_none() {
        let names: Vec<_> = code.iter().map(|section| section.name.as_str()).collect();
        return Err(format!("multiple executable sections {names:?}; pass --entry"));
    }
    let mut chosen: Option<&Section> = None;
    let mut func_name = String::new();
    if let Some(want) = entry {
        for section in &code {
            if let Some(name) = func_named(&object, bytes, section, want)? {
                chosen = Some(section);
                func_name = name;
                break;
            }
        }
        if chosen.is_none() {
            return Err(format!("entry {want} is not a function in an executable section"));
        }
    } else {
        let section = code[0];
        let names = func_names(&object, bytes, section)?;
        if names.len() > 1 {
            return Err(format!("section {} has several functions {names:?}; pass --entry", section.name));
        }
        func_name = names.into_iter().next().unwrap_or_else(|| section.name.clone());
        chosen = Some(section);
    }
    let section = chosen.unwrap();
    let start = section.offset as usize;
    let end = start.checked_add(section.size as usize).ok_or("section size overflows")?;
    if end > bytes.len() {
        return Err(format!("section {} extends past the file", section.name));
    }
    let body = bytes[start..end].to_vec();
    let mut insns = decode::decode(&body)?;
    let relocs = relocs_for(&object, bytes, section)?;
    for reloc in &relocs {
        let Some(insn) = insns.iter_mut().find(|insn| insn.index() == reloc.slot) else {
            return Err(format!("relocation {} hits slot {} which is not an instruction", reloc.symbol, reloc.slot));
        };
        match insn {
            Insn::Lddw { pseudo, .. } => {
                if *pseudo != 0 {
                    return Err(format!("slot {}: LDDW pseudo {pseudo} plus relocation {} is not a raw map object", reloc.slot, reloc.symbol));
                }
            }
            _ => return Err(format!("relocation {} hits slot {} which is not LDDW", reloc.symbol, reloc.slot)),
        }
    }
    Ok(Func { name: sanitize(&func_name), section: section.name.clone(), insns, relocs, bytes: body })
}

fn sanitize(name: &str) -> String {
    let mut out = String::new();
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() { "prog".into() } else { out }
}

fn func_names(object: &Object, bytes: &[u8], section: &Section) -> Result<Vec<String>, String> {
    let index = section_index(object, section)?;
    let mut names = Vec::new();
    for sym in symbols(object, bytes)? {
        if sym.shndx == index && sym.kind == STT_FUNC {
            names.push(sym.name);
        }
    }
    Ok(names)
}

fn func_named(object: &Object, bytes: &[u8], section: &Section, want: &str) -> Result<Option<String>, String> {
    let names = func_names(object, bytes, section)?;
    Ok(names.into_iter().find(|name| name == want))
}

fn relocs_for(object: &Object, bytes: &[u8], section: &Section) -> Result<Vec<Reloc>, String> {
    let index = section_index(object, section)?;
    let symbols = symbols(object, bytes)?;
    let mut relocs = Vec::new();
    for rel_section in &object.sections {
        if rel_section.sh_type != SHT_REL || rel_section.info != index as u32 {
            continue;
        }
        if rel_section.entsize != 16 {
            return Err(format!("relocation section {} has entry size {}", rel_section.name, rel_section.entsize));
        }
        let start = rel_section.offset as usize;
        let size = rel_section.size as usize;
        let raw = bytes.get(start..start + size).ok_or("relocation section is truncated")?;
        for entry in raw.chunks(16) {
            let offset = u64::from_le_bytes(entry[0..8].try_into().unwrap());
            let info = u64::from_le_bytes(entry[8..16].try_into().unwrap());
            let kind = info as u32;
            let sym_index = (info >> 32) as usize;
            if kind != R_BPF_64_64 {
                return Err(format!("section {} has relocation type {kind}, which is not R_BPF_64_64", section.name));
            }
            if offset % 8 != 0 {
                return Err(format!("relocation offset {offset} is not instruction aligned"));
            }
            let symbol = symbols.get(sym_index).ok_or("relocation symbol index is out of range")?;
            relocs.push(Reloc { slot: (offset / 8) as u32, symbol: symbol.name.clone() });
        }
    }
    Ok(relocs)
}

struct Sym {
    name: String,
    kind: u8,
    shndx: u16,
}

fn symbols(object: &Object, bytes: &[u8]) -> Result<Vec<Sym>, String> {
    let Some(table) = object.sections.iter().find(|section| section.sh_type == SHT_SYMTAB) else {
        return Ok(Vec::new());
    };
    if table.entsize != 24 {
        return Err(format!("symbol entry size {} is not 24", table.entsize));
    }
    let strings = object.sections.get(table.link as usize).ok_or("symbol table has no string table")?;
    let str_bytes = bytes.get(strings.offset as usize..(strings.offset + strings.size) as usize).ok_or("symbol strings are truncated")?;
    let raw = bytes.get(table.offset as usize..(table.offset + table.size) as usize).ok_or("symbol table is truncated")?;
    let mut out = Vec::new();
    for entry in raw.chunks(24) {
        let name_off = u32::from_le_bytes(entry[0..4].try_into().unwrap()) as usize;
        let info = entry[4];
        let shndx = u16::from_le_bytes(entry[6..8].try_into().unwrap());
        let name = cstr(str_bytes, name_off).unwrap_or_default();
        out.push(Sym { name, kind: info & 0xf, shndx });
    }
    Ok(out)
}

fn cstr(bytes: &[u8], offset: usize) -> Option<String> {
    let rest = bytes.get(offset..)?;
    let end = rest.iter().position(|byte| *byte == 0)?;
    Some(String::from_utf8_lossy(&rest[..end]).into_owned())
}

fn section_index(object: &Object, section: &Section) -> Result<u16, String> {
    object.sections.iter().position(|item| std::ptr::eq(item, section)).map(|index| index as u16).ok_or_else(|| "section is not in this object".into())
}
