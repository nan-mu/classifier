//! `.bin` → stable instruction table via `riscv_isa` (layout only, no semantics).

use std::collections::HashMap;

use anyhow::{bail, Result};
use riscv_isa::{decode_le_bytes, Instruction, Target};

/// One RV32IMC instruction sliced from a flat image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedInsn {
    /// Byte offset in the input image.
    pub offset: usize,
    /// Raw instruction bytes (memory order).
    pub bytes: Vec<u8>,
    /// Hex of [`Self::bytes`] (LE memory order for `-x`).
    pub hex: String,
}

/// Instruction with stable index and architectural address for the execution tree.
#[derive(Debug, Clone)]
pub struct DecodedInstruction {
    pub index: usize,
    pub offset: usize,
    /// `image_base + offset`.
    pub address: u32,
    pub bytes: Vec<u8>,
    pub len: usize,
    pub decoded: Instruction,
}

impl DecodedInstruction {
    pub fn to_decoded_insn(&self) -> DecodedInsn {
        DecodedInsn {
            offset: self.offset,
            bytes: self.bytes.clone(),
            hex: hex_of(&self.bytes),
        }
    }
}

/// Read-only instruction table: index ↔ address/offset.
#[derive(Debug, Clone)]
pub struct InstructionTable {
    insns: Vec<DecodedInstruction>,
    address_to_index: HashMap<u32, usize>,
    image_base: u32,
}

impl InstructionTable {
    pub fn from_bin(bin: &[u8], image_base: u32) -> Result<Self> {
        let raw = decode_rv32imc(bin)?;
        let target = rv32imc_target();
        let mut insns = Vec::with_capacity(raw.len());
        let mut address_to_index = HashMap::with_capacity(raw.len());
        for (index, d) in raw.into_iter().enumerate() {
            let Some((decoded, len)) = decode_le_bytes(&d.bytes, &target) else {
                bail!("instruction {index}: truncated opcode at offset {:#x}", d.offset);
            };
            debug_assert_eq!(len, d.bytes.len());
            let address = image_base.wrapping_add(d.offset as u32);
            address_to_index.insert(address, index);
            insns.push(DecodedInstruction {
                index,
                offset: d.offset,
                address,
                bytes: d.bytes,
                len,
                decoded,
            });
        }
        Ok(Self {
            insns,
            address_to_index,
            image_base,
        })
    }

    pub fn image_base(&self) -> u32 {
        self.image_base
    }

    pub fn len(&self) -> usize {
        self.insns.len()
    }

    pub fn is_empty(&self) -> bool {
        self.insns.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&DecodedInstruction> {
        self.insns.get(index)
    }

    pub fn index_of_address(&self, address: u32) -> Option<usize> {
        self.address_to_index.get(&address).copied()
    }

    /// First byte after the last instruction (architectural).
    pub fn code_end(&self) -> u32 {
        match self.insns.last() {
            Some(i) => i.address.wrapping_add(i.len as u32),
            None => self.image_base,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &DecodedInstruction> {
        self.insns.iter()
    }

    pub fn as_decoded_insns(&self) -> Vec<DecodedInsn> {
        self.insns.iter().map(DecodedInstruction::to_decoded_insn).collect()
    }
}

/// Decode a flat RV32IMC image into instructions (2- or 4-byte).
///
/// Length/partitioning uses [`riscv_isa::decode_le_bytes`] with target
/// `RV32IMC` (I+M+C, no A). Stops before a trailing `GPL\0` marker (xpost
/// compact image trailer) or errors when remaining bytes cannot form a
/// complete instruction. Unknown opcodes still advance by encoding length
/// (library yields `UNIMP`); raw bytes in [`DecodedInsn`] are unchanged.
pub fn decode_rv32imc(bin: &[u8]) -> Result<Vec<DecodedInsn>> {
    let end = code_end_bytes(bin);
    let target = rv32imc_target();
    let mut off = 0;
    let mut out = Vec::new();
    while off < end {
        let Some((_insn, len)) = decode_le_bytes(&bin[off..end], &target) else {
            bail!(
                "truncated instruction at offset {off:#x}: need 2 or 4 bytes, {rem} left",
                rem = end - off
            );
        };
        let bytes = bin[off..off + len].to_vec();
        out.push(DecodedInsn {
            offset: off,
            hex: hex_of(&bytes),
            bytes,
        });
        off += len;
    }
    Ok(out)
}

fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn rv32imc_target() -> Target {
    "RV32IMC"
        .parse()
        .expect("RV32IMC is a valid riscv_isa::Target")
}

fn code_end_bytes(bin: &[u8]) -> usize {
    if let Some(i) = find_gpl_trailer(bin) {
        return i;
    }
    bin.len()
}

fn find_gpl_trailer(bin: &[u8]) -> Option<usize> {
    bin.windows(4).position(|w| w == b"GPL\0")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_mixed_c_and_32() {
        let bin = [0x41, 0x11, 0x13, 0x05, 0x35, 0x00];
        let table = InstructionTable::from_bin(&bin, 0x1000).unwrap();
        assert_eq!(table.len(), 2);
        assert_eq!(table.get(0).unwrap().len, 2);
        assert_eq!(table.get(0).unwrap().offset, 0);
        assert_eq!(table.get(0).unwrap().address, 0x1000);
        assert_eq!(table.get(1).unwrap().len, 4);
        assert_eq!(table.get(1).unwrap().offset, 2);
        assert_eq!(table.get(1).unwrap().address, 0x1002);
        assert_eq!(table.index_of_address(0x1002), Some(1));
        assert_eq!(table.index_of_address(0x1001), None);
    }

    #[test]
    fn decode_stops_before_gpl() {
        let mut bin = vec![0x82, 0x80];
        bin.extend_from_slice(b"GPL\0trailer");
        let insns = decode_rv32imc(&bin).unwrap();
        assert_eq!(insns.len(), 1);
        assert_eq!(insns[0].hex, "8280");
    }

    #[test]
    fn mid_instruction_address_is_unmapped() {
        let bin = [0x13, 0x05, 0x35, 0x00]; // 4-byte addi
        let table = InstructionTable::from_bin(&bin, 0).unwrap();
        assert_eq!(table.index_of_address(0), Some(0));
        assert_eq!(table.index_of_address(1), None);
        assert_eq!(table.index_of_address(2), None);
        assert_eq!(table.index_of_address(3), None);
    }
}
