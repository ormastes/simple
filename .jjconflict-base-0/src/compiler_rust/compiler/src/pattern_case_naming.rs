//! Shared spelling test for a bare identifier in `case` position.
//!
//! Bug: `doc/08_tracking/bug/case_bare_ident_is_irrefutable_binding_2026-08-01.md`
//!
//! A bare `case <Ident>:` arm whose identifier is not a variant of the matched
//! enum silently becomes an **irrefutable binding**: it matches every remaining
//! value, binds it, and makes every later arm -- including `case _:` --
//! unreachable, with no diagnostic. Simple's convention is Capitalized (or
//! `SCREAMING_SNAKE_CASE`) = type/variant/const and lowercase = binding, so an
//! identifier spelled that way can never have been an intended binder.
//!
//! This predicate lives in one place because **two independent engines** decide
//! the same question and must not drift apart:
//!
//! * `hir/lower/stmt_lowering.rs` `lower_pattern_condition_stmt` -- the JIT /
//!   native lane, keyed on the subject's static `TypeId`.
//! * `interpreter_patterns.rs` `Pattern::Identifier` -- the tree-walk
//!   interpreter, keyed on the runtime `Value::Enum`.
//!
//! Both must refuse. A refusal on only one of them is worse than no fix at all:
//! a JIT-side HIR error is caught by the `[jit-fallback]` path, which drops the
//! whole module to the interpreter, so the program still computes the same wrong
//! answer -- only now ~100-1000x slower. Measured 2026-08-02.

/// `Foo`, `FAdd`, `WS_OPCODE_TEXT`, `_MAX` -> true.
/// `other`, `x2`, `_`, `_tmp`, `""` -> false.
///
/// Membership uses `char::is_ascii_uppercase`, never a `>= 'A' && <= 'Z'` range
/// comparison: see the JIT text-ordering pointer-compare defect recorded in the
/// same bug doc, which made exactly that shape silently false on derived text.
/// Do not "simplify" this to a range check without re-measuring.
pub fn case_name_is_spelled_like_a_variant(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if first.is_ascii_uppercase() {
        return true;
    }
    // `SCREAMING_SNAKE_CASE` may legitimately start with `_`; a lone `_` is the
    // wildcard and `_tmp` is a deliberately-unused binding, so both stay false.
    first == '_'
        && name.len() > 1
        && name
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        && name.chars().any(|c| c.is_ascii_uppercase())
}

#[cfg(test)]
mod tests {
    use super::case_name_is_spelled_like_a_variant as spelled;

    #[test]
    fn variant_spellings_are_recognized() {
        // Real variant names, and the two shapes from the bug doc's probes.
        for name in ["Foo", "FAdd", "Red", "ContractOld", "WS_OPCODE_TEXT", "_MAX_LEN"] {
            assert!(spelled(name), "{name} should read as a variant/const name");
        }
    }

    #[test]
    fn genuine_bindings_are_left_alone() {
        // Lowercase names are real bindings; `_` is the wildcard; `_tmp` is an
        // intentionally-unused binder. None may be reported.
        for name in ["other", "x", "x2", "value", "_", "_tmp", "_x", ""] {
            assert!(!spelled(name), "{name} is a binding and must not be reported");
        }
    }
}
