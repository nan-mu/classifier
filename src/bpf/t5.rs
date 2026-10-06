//! T5: return-value induction.

use super::text::{
    core_stmt, is_r0_definition, join_line, parse_helper_r0, parse_r0_imm, split_line,
};

fn t5_1(path: &[String]) -> Vec<String> {
    let mut out = path.to_vec();
    // find final exit
    let Some(exit_pos) = out.iter().rposition(|l| {
        split_line(l).is_some_and(|(_, b)| core_stmt(b) == "exit" || b == "exit")
    }) else {
        return out;
    };

    for i in (0..exit_pos).rev() {
        let Some((index, body)) = split_line(&out[i]) else {
            continue;
        };
        if !is_r0_definition(body) {
            continue;
        }
        if body.contains("return value {") {
            break;
        }
        if let Some(imm) = parse_r0_imm(body) {
            out[i] = join_line(index, &format!("{body}, return value {{ {imm} }}"));
            break;
        }
        if parse_helper_r0(body).is_some() {
            out[i] = join_line(index, &format!("{body}, return value {{ V }}"));
            break;
        }
        // unrecognized R0 def — stop without annotation
        break;
    }
    out
}

fn t5_2(path: &[String]) -> Vec<String> {
    let mut out = path.to_vec();
    let Some(exit_pos) = out.iter().rposition(|l| {
        split_line(l).is_some_and(|(_, b)| core_stmt(b) == "exit" || b == "exit")
    }) else {
        return out;
    };

    let mut ret_val: Option<String> = None;
    for line in out[..exit_pos].iter().rev() {
        let Some((_, body)) = split_line(line) else {
            continue;
        };
        if let Some(start) = body.find("return value {") {
            let rest = &body[start + "return value {".len()..];
            if let Some(end) = rest.find('}') {
                ret_val = Some(rest[..end].trim().to_string());
                break;
            }
        }
        if is_r0_definition(body) {
            break;
        }
    }

    if let Some(val) = ret_val {
        let Some((index, _)) = split_line(&out[exit_pos]) else {
            return out;
        };
        out[exit_pos] = join_line(index, &format!("return {val}"));
    }
    out
}

/// T5 = t5_2 ∘ t5_1.
pub fn t5(path: &[String]) -> Vec<String> {
    t5_2(&t5_1(path))
}
