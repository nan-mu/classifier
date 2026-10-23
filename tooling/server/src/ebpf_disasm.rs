//! Display-only eBPF disassembly for the Expand UI insn list.
//! Opcode families mirror Lean `EBPF.decodeInsnWord`; LDDW pairs join across words.

/// Pretty-print one raw 64-bit slot. Unknown encodings keep hex.
pub fn disasm_word(word: u64) -> String {
    match decode(word) {
        Some(text) => text,
        None => format!("{word:016x}"),
    }
}

/// Pretty-print a program image. LDDW upper halves become `/* lddw cont */`.
pub fn disasm_words(words: &[u64]) -> Vec<String> {
    let mut out = Vec::with_capacity(words.len());
    let mut i = 0;
    while i < words.len() {
        let word = words[i];
        let opcode = (word & 0xff) as u8;
        if opcode == 0x18 {
            if let Some(upper) = words.get(i + 1) {
                if upper & 0xffff_ffff == 0 {
                    let imm_lo = (word >> 32) as u32 as u64;
                    let imm_hi = *upper >> 32;
                    let bits = imm_lo | (imm_hi << 32);
                    let dst = ((word >> 8) & 0xf) as u8;
                    let src_type = ((word >> 12) & 0xf) as u8;
                    out.push(format!("{i:04} {}", format_lddw(dst, src_type, bits)));
                    out.push(format!("{:04} /* lddw cont */", i + 1));
                    i += 2;
                    continue;
                }
            }
        }
        out.push(format!("{i:04} {}", disasm_word(word)));
        i += 1;
    }
    out
}

fn format_lddw(dst: u8, src_type: u8, bits: u64) -> String {
    if src_type == 0 {
        format!("lddw r{dst}, 0x{bits:x}")
    } else {
        format!("lddw r{dst}, map_fd {bits}")
    }
}

fn decode(word: u64) -> Option<String> {
    let opcode = (word & 0xff) as u8;
    let dst = ((word >> 8) & 0xf) as u8;
    let src = ((word >> 12) & 0xf) as u8;
    let off = ((word >> 16) as i16) as i32;
    let imm = (word >> 32) as u32;
    let imm_i = imm as i32;

    if opcode == 0x95 {
        return if word == 0x95 {
            Some("exit".into())
        } else {
            None
        };
    }
    if opcode == 0x85 {
        return Some(format!("call {imm}"));
    }
    if opcode == 0x05 {
        return Some(format!("goto {off:+}"));
    }
    if opcode == 0x18 {
        return Some(format_lddw(dst, src, imm as u64));
    }

    match opcode {
        0x71 => Some(format!("r{dst} = *(u8 *)(r{src}{off:+})")),
        0x69 => Some(format!("r{dst} = *(u16 *)(r{src}{off:+})")),
        0x61 => Some(format!("r{dst} = *(u32 *)(r{src}{off:+})")),
        0x79 => Some(format!("r{dst} = *(u64 *)(r{src}{off:+})")),
        0x73 => Some(format!("*(u8 *)(r{dst}{off:+}) = r{src}")),
        0x6b => Some(format!("*(u16 *)(r{dst}{off:+}) = r{src}")),
        0x63 => Some(format!("*(u32 *)(r{dst}{off:+}) = r{src}")),
        0x7b => Some(format!("*(u64 *)(r{dst}{off:+}) = r{src}")),
        0xb4 => Some(format!("r{dst} = {imm_i}")),
        0xb7 => Some(format!("r{dst} = {imm_i}")),
        0xbc => Some(format!("w{dst} = w{src}")),
        0xbf => Some(format!("r{dst} = r{src}")),
        0x04 => Some(format!("w{dst} += {imm_i}")),
        0x07 => Some(format!("r{dst} += {imm_i}")),
        0x0c => Some(format!("w{dst} += w{src}")),
        0x0f => Some(format!("r{dst} += r{src}")),
        0x15 => Some(format!("if r{dst} == {imm_i} goto {off:+}")),
        0x1d => Some(format!("if r{dst} == r{src} goto {off:+}")),
        0x55 => Some(format!("if r{dst} != {imm_i} goto {off:+}")),
        0x5d => Some(format!("if r{dst} != r{src} goto {off:+}")),
        0x25 => Some(format!("if r{dst} > {imm_i} goto {off:+}")),
        0x2d => Some(format!("if r{dst} > r{src} goto {off:+}")),
        0x16 => Some(format!("if w{dst} == {imm_i} goto {off:+}")),
        0x1e => Some(format!("if w{dst} == w{src} goto {off:+}")),
        0x56 => Some(format!("if w{dst} != {imm_i} goto {off:+}")),
        0x5e => Some(format!("if w{dst} != w{src} goto {off:+}")),
        0x26 => Some(format!("if w{dst} > {imm_i} goto {off:+}")),
        0x2e => Some(format!("if w{dst} > w{src} goto {off:+}")),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn just_tx_head_reads_like_bpftool() {
        // LE words from just_tx.bpf.o head (bpftool-style).
        let words = [0x0000_0001_0000_00b4u64, 0x0000_0000_0004_1261u64];
        assert_eq!(disasm_word(words[0]), "r0 = 1");
        assert_eq!(disasm_word(words[1]), "r2 = *(u32 *)(r1+4)");
        let lines = disasm_words(&words);
        assert_eq!(lines[0], "0000 r0 = 1");
        assert_eq!(lines[1], "0001 r2 = *(u32 *)(r1+4)");
    }

    #[test]
    fn exit_call_lddw_pair() {
        assert_eq!(disasm_word(0x95), "exit");
        assert_eq!(disasm_word(0x0000_0001_0000_0085), "call 1");
        let lines = disasm_words(&[0x5566_7788_0000_0118, 0x1122_3344_0000_0000, 0x95]);
        assert_eq!(lines[0], "0000 lddw r1, 0x1122334455667788");
        assert_eq!(lines[1], "0001 /* lddw cont */");
        assert_eq!(lines[2], "0002 exit");
    }

    #[test]
    fn unknown_falls_back_to_hex() {
        assert_eq!(disasm_word(0xdead_beef_0000_00ff), "deadbeef000000ff");
    }
}
