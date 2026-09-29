//! Operand helpers for inline-asm lowering: register-class → LLVM constraint
//! mapping and `{name}` placeholder rewriting.
//!
//! Ordering contract with the raw-block `$` escaping owned by the `@naked`
//! lane (design A.3.1): that escaping turns a literal `$` into `$$` and MUST
//! run BEFORE `rewrite_asm_placeholders`, because the `$N` this function emits
//! is an LLVM operand reference and must not itself be escaped.

/// Map a Simple register class or explicit register name to an LLVM
/// constraint code. `reg` (and its aliases) become the generic `r`; any other
/// identifier is treated as an explicit register, `{name}`.
pub fn asm_constraint_for(reg: &str) -> String {
    match reg {
        "reg" | "reg_abcd" | "general" => "r".to_string(),
        "freg" | "vreg" | "xmm_reg" | "ymm_reg" | "zmm_reg" => "x".to_string(),
        explicit => format!("{{{}}}", explicit),
    }
}

/// Rewrite every `{name}` placeholder to LLVM's `$N`, where `N` is the
/// operand's index in the constraint list (outputs first, then inputs).
/// Unnamed placeholders `{0}`, `{1}` index operands positionally in the same
/// order. Text that is not a known placeholder is left untouched.
/// Design A.3.1: raw `asm { }` text is opaque, so every `$` the author wrote
/// must reach LLVM as a literal `$$` (LLVM's template engine reads a bare
/// `$N` as an operand reference and aborts with "Bad $ operand number").
///
/// This MUST run BEFORE `rewrite_asm_placeholders`: that function INSERTS the
/// `$N` references, and escaping afterwards would rewrite them to `$$N` and
/// silently unbind every operand.
pub fn escape_raw_asm_dollars(line: &str) -> String {
    if !line.contains('$') {
        return line.to_string();
    }
    line.replace('$', "$$")
}

pub fn rewrite_asm_placeholders(line: &str, index: &[(Option<String>, usize)]) -> String {
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(open) = rest.find('{') {
        out.push_str(&rest[..open]);
        let after = &rest[open + 1..];
        let Some(close) = after.find('}') else {
            out.push_str(&rest[open..]);
            return out;
        };
        let key = &after[..close];
        let resolved = if let Ok(pos) = key.parse::<usize>() {
            index.get(pos).map(|(_, slot)| *slot)
        } else {
            index
                .iter()
                .find(|(name, _)| name.as_deref() == Some(key))
                .map(|(_, slot)| *slot)
        };
        match resolved {
            Some(slot) => out.push_str(&format!("${}", slot)),
            None => {
                out.push('{');
                out.push_str(key);
                out.push('}');
            }
        }
        rest = &after[close + 1..];
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_placeholder_rewrites_to_slot() {
        let idx = vec![(Some("result".to_string()), 0)];
        assert_eq!(
            rewrite_asm_placeholders("csrr {result}, sstatus", &idx),
            "csrr $0, sstatus"
        );
    }

    #[test]
    fn positional_and_mixed() {
        let idx = vec![(Some("v".to_string()), 0), (None, 1)];
        assert_eq!(rewrite_asm_placeholders("csrw sstatus, {1}", &idx), "csrw sstatus, $1");
        assert_eq!(rewrite_asm_placeholders("mov {v}, {1}", &idx), "mov $0, $1");
    }

    #[test]
    fn unknown_placeholder_left_alone() {
        assert_eq!(rewrite_asm_placeholders("mov {zzz}, 1", &[]), "mov {zzz}, 1");
    }

    #[test]
    fn constraint_mapping() {
        assert_eq!(asm_constraint_for("reg"), "r");
        assert_eq!(asm_constraint_for("eax"), "{eax}");
        assert_eq!(asm_constraint_for("a0"), "{a0}");
    }

    #[test]
    fn dollar_is_doubled_before_placeholder_rewriting() {
        assert_eq!(escape_raw_asm_dollars("and $~0xF, %rsp"), "and $$~0xF, %rsp");
        assert_eq!(escape_raw_asm_dollars("xor %rbp, %rbp"), "xor %rbp, %rbp");
    }

    #[test]
    fn escaping_then_rewriting_keeps_placeholders_unescaped() {
        // The ordering contract: a literal `$` in operand-bound text is
        // escaped, while the `$0` the rewriter inserts stays a live operand.
        let index = vec![(Some("out".to_string()), 0usize)];
        let escaped = escape_raw_asm_dollars("mov $1, {out}");
        assert_eq!(escaped, "mov $$1, {out}");
        assert_eq!(rewrite_asm_placeholders(&escaped, &index), "mov $$1, $0");
    }
}
