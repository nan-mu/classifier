const ELF_MAGIC: [u8; 4] = [0x7f, b'E', b'L', b'F'];
const ELFCLASS64: u8 = 2;
const ELFDATA2LSB: u8 = 1;
const EM_BPF: u16 = 247;
const SHT_PROGBITS: u32 = 1;
const SHF_EXECINSTR: u64 = 0x4;
const SHDR_SIZE: usize = 64;

#[derive(Debug, PartialEq, Eq)]
pub enum ElfError {
    Truncated,
    BadMagic,
    NotElf64,
    NotLittleEndian,
    NotBpf,
    NotRelocatable,
    BadVersion,
    BadSection,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Section {
    pub name: String,
    pub sh_type: u32,
    pub flags: u64,
    pub offset: u64,
    pub size: u64,
    pub link: u32,
    pub info: u32,
    pub entsize: u64,
}

impl Section {
    pub fn is_code(&self) -> bool {
        self.sh_type == SHT_PROGBITS && self.flags & SHF_EXECINSTR != 0 && self.size > 0
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Object {
    pub sections: Vec<Section>,
}

impl Object {
    pub fn code_sections(&self) -> impl Iterator<Item = &Section> {
        self.sections.iter().filter(|section| section.is_code())
    }
}

pub fn parse(bytes: &[u8]) -> Result<Object, ElfError> {
    if bytes.len() < 64 {
        return Err(ElfError::Truncated);
    }
    if bytes[0..4] != ELF_MAGIC {
        return Err(ElfError::BadMagic);
    }
    if bytes[4] != ELFCLASS64 {
        return Err(ElfError::NotElf64);
    }
    if bytes[5] != ELFDATA2LSB {
        return Err(ElfError::NotLittleEndian);
    }
    if read_u16(bytes, 18)? != EM_BPF {
        return Err(ElfError::NotBpf);
    }
    if read_u16(bytes, 16)? != 1 {
        return Err(ElfError::NotRelocatable);
    }
    if bytes[6] != 1 || read_u32(bytes, 20)? != 1 || read_u16(bytes, 52)? != 64 {
        return Err(ElfError::BadVersion);
    }
    let shoff = usize::try_from(read_u64(bytes, 40)?).map_err(|_| ElfError::BadSection)?;
    let shentsize = read_u16(bytes, 58)? as usize;
    let shnum = read_u16(bytes, 60)? as usize;
    let shstrndx = read_u16(bytes, 62)? as usize;
    if shentsize != SHDR_SIZE || shstrndx >= shnum {
        return Err(ElfError::BadSection);
    }
    let table_end = shoff
        .checked_add(shnum.checked_mul(SHDR_SIZE).ok_or(ElfError::BadSection)?)
        .ok_or(ElfError::BadSection)?;
    if table_end > bytes.len() {
        return Err(ElfError::Truncated);
    }

    let mut raw = Vec::with_capacity(shnum);
    for index in 0..shnum {
        let at = shoff + index * SHDR_SIZE;
        raw.push(RawSection {
            name_off: read_u32(bytes, at)?,
            sh_type: read_u32(bytes, at + 4)?,
            flags: read_u64(bytes, at + 8)?,
            offset: read_u64(bytes, at + 24)?,
            size: read_u64(bytes, at + 32)?,
            link: read_u32(bytes, at + 40)?,
            info: read_u32(bytes, at + 44)?,
            entsize: read_u64(bytes, at + 56)?,
        });
    }
    let strings = &raw[shstrndx];
    let str_off = strings.offset as usize;
    let str_end = str_off
        .checked_add(strings.size as usize)
        .ok_or(ElfError::BadSection)?;
    if str_end > bytes.len() {
        return Err(ElfError::Truncated);
    }
    let string_table = &bytes[str_off..str_end];

    let mut sections = Vec::with_capacity(raw.len());
    for section in raw {
        if section.sh_type != 8
            && section
                .offset
                .checked_add(section.size)
                .is_none_or(|end| end > bytes.len() as u64)
        {
            return Err(ElfError::Truncated);
        }
        sections.push(Section {
            name: name_at(string_table, section.name_off as usize)?,
            sh_type: section.sh_type,
            flags: section.flags,
            offset: section.offset,
            size: section.size,
            link: section.link,
            info: section.info,
            entsize: section.entsize,
        });
    }
    Ok(Object { sections })
}

struct RawSection {
    name_off: u32,
    sh_type: u32,
    flags: u64,
    offset: u64,
    size: u64,
    link: u32,
    info: u32,
    entsize: u64,
}

fn name_at(table: &[u8], offset: usize) -> Result<String, ElfError> {
    let rest = table.get(offset..).ok_or(ElfError::BadSection)?;
    let end = rest
        .iter()
        .position(|byte| *byte == 0)
        .ok_or(ElfError::BadSection)?;
    let name = std::str::from_utf8(&rest[..end]).map_err(|_| ElfError::BadSection)?;
    Ok(name.to_string())
}

fn read_u16(bytes: &[u8], at: usize) -> Result<u16, ElfError> {
    let chunk = bytes.get(at..at + 2).ok_or(ElfError::Truncated)?;
    Ok(u16::from_le_bytes(
        chunk.try_into().map_err(|_| ElfError::Truncated)?,
    ))
}

fn read_u32(bytes: &[u8], at: usize) -> Result<u32, ElfError> {
    let chunk = bytes.get(at..at + 4).ok_or(ElfError::Truncated)?;
    Ok(u32::from_le_bytes(
        chunk.try_into().map_err(|_| ElfError::Truncated)?,
    ))
}

fn read_u64(bytes: &[u8], at: usize) -> Result<u64, ElfError> {
    let chunk = bytes.get(at..at + 8).ok_or(ElfError::Truncated)?;
    Ok(u64::from_le_bytes(
        chunk.try_into().map_err(|_| ElfError::Truncated)?,
    ))
}
