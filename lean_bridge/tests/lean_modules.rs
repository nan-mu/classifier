//! Integration tests that call Lean4 modules through the Rust FFI surface.

use lean_bridge::{common_math, rv32};

#[test]
fn common_math_add_wraps_at_32() {
    assert_eq!(common_math::add32(0xffff_ffff, 2), 1);
}

#[test]
fn common_math_sub_wraps() {
    assert_eq!(common_math::sub32(0, 1), 0xffff_ffff);
}

#[test]
fn common_math_and() {
    assert_eq!(common_math::and32(0b1100, 0b1010), 0b1000);
}

#[test]
fn common_math_divu_by_zero_is_all_ones() {
    assert_eq!(common_math::divu32(42, 0), 0xffff_ffff);
}

#[test]
fn common_math_tq_toward_zero() {
    // TQ(-7, 2) = -3 → bit pattern
    assert_eq!(common_math::tq32((-7i32) as u32, 2), (-3i32) as u32);
}

#[test]
fn path_demo_section18_budget() {
    assert!(common_math::path_demo_check());
    assert_eq!(common_math::path_demo_nodes(11), 12);
    assert_eq!(common_math::path_demo_nodes(10), 0);
}

#[test]
fn decode_addi() {
    // addi x1, x2, 5  → 0x00510093
    assert_eq!(rv32::decode32(0x0051_0093), rv32::tag::ADDI);
}

#[test]
fn decode_lui() {
    // lui x1, 0x1
    assert_eq!(rv32::decode32(0x0000_10b7), rv32::tag::LUI);
}

#[test]
fn decode_add() {
    // add x3, x1, x2 → 0x002081b3
    assert_eq!(rv32::decode32(0x0020_81b3), rv32::tag::ADD);
}

#[test]
fn decode_c_nop() {
    assert_eq!(rv32::decode16(0x0001), rv32::tag::C_NOP);
}

#[test]
fn value_addi_concrete() {
    // x2=10, addi x1, x2, 5 → 15
    assert_eq!(rv32::value_addi(10, 5, 2, 1), 15);
}

#[test]
fn value_addi_sign_extend_imm() {
    // imm = -1 as 12-bit (0xfff), rs1=5 → 4
    assert_eq!(rv32::value_addi(5, 0xfff, 2, 1), 4);
}

#[test]
fn value_addi_to_x0_is_discarded() {
    assert_eq!(rv32::value_addi(10, 5, 2, 0), 0);
}

#[test]
fn value_add_concrete() {
    assert_eq!(rv32::value_add(7, 9, 1, 2, 3), 16);
}

#[test]
fn value_lui() {
    // uimm20=1 → 0x1000
    assert_eq!(rv32::value_lui(1, 1), 0x1000);
}

#[test]
fn value_auipc() {
    // pc=0x1000, uimm20=1 → 0x1000 + 0x1000 = 0x2000
    assert_eq!(rv32::value_auipc(0x1000, 1, 1), 0x2000);
}

#[test]
fn value_div_by_zero() {
    assert_eq!(rv32::value_div(100, 0), 0xffff_ffff);
}

#[test]
fn ecall_is_rejected() {
    assert!(rv32::ecall_rejects());
}

#[test]
fn expr_override_replaces_same_key_keeps_others() {
    assert!(rv32::expr_override_keeps());
}
