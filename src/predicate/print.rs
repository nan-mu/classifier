//! Unique BPF-assembly-style renderer for [`super::Predicate`].

use super::{
    Address, AluOp, BitVec, Condition, Operand, Predicate, PredicateNode, Prefix, Reg,
};

pub fn print_prefix(prefix: &Prefix) -> String {
    prefix
        .0
        .iter()
        .filter_map(|n| {
            let s = print_predicate(&n.predicate);
            if s.is_empty() {
                None
            } else {
                Some(s)
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

pub fn print_node(node: &PredicateNode) -> String {
    print_predicate(&node.predicate)
}

pub fn print_predicate(p: &Predicate) -> String {
    match p {
        Predicate::Empty => String::new(),
        Predicate::Set { dst, src } => format!("{dst} = {}", print_operand(src)),
        Predicate::AluAssign { dst, op, rhs } => {
            format!("{dst} {}= {}", alu_infix(*op), print_operand(rhs))
        }
        Predicate::Alu {
            dst,
            op,
            lhs,
            rhs,
        } => format!(
            "{dst} = {} {} {}",
            print_operand(lhs),
            alu_infix(*op),
            print_operand(rhs)
        ),
        Predicate::AluCall {
            dst,
            name,
            lhs,
            rhs,
        } => format!(
            "{dst} = {name}({}, {})",
            print_operand(lhs),
            print_operand(rhs)
        ),
        Predicate::Load { dst, width, addr } => {
            format!("{dst} = *({} *)({})", width.as_str(), print_address(addr))
        }
        Predicate::Store { width, addr, src } => {
            format!(
                "*({} *)({}) = {}",
                width.as_str(),
                print_address(addr),
                print_operand(src)
            )
        }
        Predicate::Assert {
            condition,
            expected,
        } => format!(
            "assert ({}) == {}",
            print_condition(condition),
            expected
        ),
        Predicate::IfGoto { condition, offset } => {
            format!("if {} goto {offset}", print_condition(condition))
        }
        Predicate::Goto { offset } => format!("goto {offset}"),
        Predicate::Call { target } => format!("call {target}"),
        Predicate::Exit => "exit".into(),
        Predicate::Trap { reason } => format!("trap {reason}"),
    }
}

fn print_operand(op: &Operand) -> String {
    match op {
        Operand::Reg(r) => r.to_string(),
        Operand::Imm(bv) => print_bitvec(*bv),
    }
}

pub fn print_bitvec(bv: BitVec) -> String {
    // `0x` + lowercase hex without leading zeros. Values like `0xfffffff0`
    // keep their full digit run because they do not start with `0`.
    let hex = match bv {
        BitVec::Bv8(v) => format!("{v:x}"),
        BitVec::Bv16(v) => format!("{v:x}"),
        BitVec::Bv32(v) => format!("{v:x}"),
        BitVec::Bv64(v) => format!("{v:x}"),
    };
    format!("0x{hex}")
}

fn print_address(addr: &Address) -> String {
    match addr.offset {
        None => addr.base.to_string(),
        Some(off) => format!("{} + {}", addr.base, print_bitvec(off)),
    }
}

fn print_condition(c: &Condition) -> String {
    format!(
        "{} {} {}",
        print_operand(&c.lhs),
        c.op.as_str(),
        print_operand(&c.rhs)
    )
}

fn alu_infix(op: AluOp) -> &'static str {
    match op {
        AluOp::Add => "+",
        AluOp::Sub => "-",
        AluOp::Mul => "*",
        AluOp::And => "&",
        AluOp::Or => "|",
        AluOp::Xor => "^",
        AluOp::Shl => "<<",
        AluOp::Lshr => ">>",
        AluOp::Ashr => "s>>",
        AluOp::Div => "s/",
        AluOp::Divu => "/",
        AluOp::Rem => "s%",
        AluOp::Remu => "%",
        AluOp::Slt | AluOp::Sltu | AluOp::Mulh | AluOp::Mulhu | AluOp::Mulhsu => {
            unreachable!("use AluCall for non-infix ops")
        }
    }
}

#[allow(dead_code)]
pub fn reg_w(n: u32) -> Reg {
    Reg::w(n)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate::{MemWidth, Origin, PredicateId};

    #[test]
    fn prints_smt_immediates_and_padding_shapes() {
        let mut prefix = Prefix::new();
        prefix.push(
            PredicateId(0),
            Predicate::AluAssign {
                dst: Reg::w(2),
                op: AluOp::Add,
                rhs: Operand::Imm(BitVec::Bv32(0xfffffff0)),
            },
            Origin::stage("prefixgen"),
        );
        assert_eq!(print_prefix(&prefix), "w2 += 0xfffffff0");

        let small = Predicate::Set {
            dst: Reg::w(0),
            src: Operand::Imm(BitVec::Bv32(1)),
        };
        assert_eq!(print_predicate(&small), "w0 = 0x1");

        let load = Predicate::Load {
            dst: Reg::w(9),
            width: MemWidth::U32,
            addr: Address {
                base: Reg::w(10),
                offset: None,
            },
        };
        assert_eq!(print_predicate(&load), "w9 = *(u32 *)(w10)");
    }
}
