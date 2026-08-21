//! Regression matrix for
//! `doc/08_tracking/bug/parser_trailing_operator_line_continuation_2026-07-13.md`.
//!
//! A condition that continues onto the next line via a trailing binary operator
//! and then resolves to a SINGLE-LINE (colon-suffixed, same-source-line) body
//! used to fail with "expected expression, found Dedent". The multi-line-body
//! form of the same condition always worked, which is why the defect survived
//! the 2026-08-04 rejoined-continuation fix.
//!
//! Live instances that this unblocks:
//! `src/compiler/00.common/assurance/formal_delivery_gates.spl:147-149,205-207`.
#[cfg(test)]
mod trailing_operator_single_line_body {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    // ---- The failing shape: single-line body after a continued condition ----

    /// The bug record's own 2026-08-21 minimal repro, verbatim.
    #[test]
    fn or_continuation_single_line_body() {
        let src = "fn f(a: bool, c: text) -> i64:\n\
                   \x20   if a or\n\
                   \x20           c == \"\": return 1\n\
                   \x20   2\n";
        assert!(parses(src), "or-continuation with single-line body must parse");
    }

    /// `and` must behave identically to `or` — the record confirms the defect
    /// is operator-independent.
    #[test]
    fn and_continuation_single_line_body() {
        let src = "fn f(a: bool, c: text) -> i64:\n\
                   \x20   if a and\n\
                   \x20           c == \"\": return 1\n\
                   \x20   2\n";
        assert!(parses(src), "and-continuation with single-line body must parse");
    }

    /// `not` on the continued operand — the record bisected this variant.
    #[test]
    fn not_operand_single_line_body() {
        let src = "fn f(a: bool, c: text) -> i64:\n\
                   \x20   if not a or\n\
                   \x20           c == \"\": return 1\n\
                   \x20   2\n";
        assert!(parses(src), "not-operand continuation with single-line body must parse");
    }

    /// Three-way chain, so the continuation carries more than one operator.
    #[test]
    fn three_way_chain_single_line_body() {
        let src = "fn f(a: bool, b: bool, c: text) -> i64:\n\
                   \x20   if a or\n\
                   \x20           b or\n\
                   \x20           c == \"\": return 1\n\
                   \x20   2\n";
        assert!(parses(src), "three-way chain with single-line body must parse");
    }

    /// Integer `>` operand rather than a text `==` operand.
    #[test]
    fn int_comparison_operand_single_line_body() {
        let src = "fn f(a: bool, n: i64) -> i64:\n\
                   \x20   if a or\n\
                   \x20           n > 0: return 1\n\
                   \x20   2\n";
        assert!(parses(src), "int-comparison operand with single-line body must parse");
    }

    /// A continuation line SHALLOWER than the body column exercises the other
    /// branch of the dedent-reconciliation described in `parser_helpers.rs`.
    #[test]
    fn shallow_continuation_column_single_line_body() {
        let src = "fn f(a: bool, c: text) -> i64:\n\
                   \x20   if a or\n\
                   \x20     c == \"\": return 1\n\
                   \x20   2\n";
        assert!(parses(src), "shallow continuation column with single-line body must parse");
    }

    /// `while` shares `parse_condition_block` with `if`, so it must not be a
    /// one-construct fix.
    #[test]
    fn while_continuation_single_line_body() {
        let src = "fn f(a: bool, c: text) -> i64:\n\
                   \x20   while a or\n\
                   \x20           c == \"\": return 1\n\
                   \x20   2\n";
        assert!(parses(src), "while-continuation with single-line body must parse");
    }

    /// The single-line body is the LAST statement of the function, so the
    /// condition's pseudo-dedent and the function block's dedent coincide.
    #[test]
    fn single_line_body_as_last_statement() {
        let src = "fn f(a: bool, c: text) -> i64:\n\
                   \x20   if a or\n\
                   \x20           c == \"\": return 1\n";
        assert!(parses(src), "single-line body as last statement must parse");
    }

    // ---- Controls: shapes the record confirms already PASS ----

    /// Multi-line indented body — passed before the fix, must still pass.
    #[test]
    fn control_multi_line_body_still_parses() {
        let src = "fn f(a: bool, c: text) -> i64:\n\
                   \x20   if a or\n\
                   \x20           c == \"\":\n\
                   \x20       return 1\n\
                   \x20   2\n";
        assert!(parses(src), "multi-line body regressed");
    }

    /// Bare trailing-operator statement — passed before the fix, must still pass.
    #[test]
    fn control_bare_trailing_operator_statement_still_parses() {
        let src = "fn f(a: bool, b: bool) -> bool:\n\
                   \x20   a and\n\
                   \x20       b\n";
        assert!(parses(src), "bare trailing-operator statement regressed");
    }

    /// Boundary the fix must not cross: an UNcontinued condition with a
    /// single-line body followed by a sibling statement still ends where it
    /// should, i.e. `2` is a statement of `f`, not swallowed into the `if`.
    #[test]
    fn control_uncontinued_single_line_body_still_parses() {
        let src = "fn f(a: bool) -> i64:\n\
                   \x20   if a: return 1\n\
                   \x20   2\n";
        assert!(parses(src), "uncontinued single-line body regressed");
    }
}
