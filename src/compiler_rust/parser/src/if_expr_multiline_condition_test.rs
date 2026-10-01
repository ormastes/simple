//! Regression matrix for
//! `doc/08_tracking/bug/backslash_lambda_multiline_inline_body_dedent_2026-08-28.md`
//! ("second defect" section).
//!
//! An inline `if`/`else` **expression** (used as a value, e.g. `val x = if
//! cond: a else: b`) whose **condition** trails a binary operator onto a
//! later line before the colon used to fail with "found Dedent". This is
//! the expression-form sibling of the statement-form `if` bug fixed by
//! `parser_trailing_operator_line_continuation_2026-07-13.md` — the
//! statement form reconciles the condition's deferred pseudo-dedent via
//! `reconcile_inline_body_deferred_dedents` / `drain_available_deferred_dedents`,
//! but `parse_if_expr`'s inline-then-branch path never called either, so the
//! deferred dedent leaked into whatever followed the `if`-expression.
//!
//! Minimized from `src/compiler/50.mir/hwir/riscv_scalar_fence_owner.spl`.
#[cfg(test)]
mod if_expr_multiline_condition {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    // ---- The failing shape: if-EXPRESSION with a multi-line condition ----

    /// The bug record's own minimized repro, verbatim.
    #[test]
    fn or_continuation_if_expr_inline_both_branches() {
        let src = "fn main():\n\
                   \x20   val x = if 1 == 1 or\n\
                   \x20       1 == 2: \"a\" else: \"b\"\n\
                   \x20   print(x)\n";
        assert!(parses(src), "or-continuation if-expression condition must parse");
    }

    #[test]
    fn and_continuation_if_expr_inline_both_branches() {
        let src = "fn main():\n\
                   \x20   val x = if 1 == 1 and\n\
                   \x20       1 == 2: \"a\" else: \"b\"\n\
                   \x20   print(x)\n";
        assert!(parses(src), "and-continuation if-expression condition must parse");
    }

    /// Three-way `or` chain matching the original triage report's shape
    /// (`field[0] == "event_id" or field[0] == "decode_event_id" or\n    ...`).
    #[test]
    fn multi_or_chain_condition_continuation() {
        let src = "fn main():\n\
                   \x20   val output_name = if 1 == 1 or 1 == 2 or\n\
                   \x20       1 == 3: \"completion\" else: \"other\"\n\
                   \x20   print(output_name)\n";
        assert!(parses(src), "multi-or-chain condition continuation must parse");
    }

    /// No `else` at all — inline then-branch only, condition continues.
    #[test]
    fn or_continuation_if_expr_no_else() {
        let src = "fn main():\n\
                   \x20   val x = if 1 == 1 or\n\
                   \x20       1 == 2: \"a\"\n\
                   \x20   print(x)\n";
        assert!(
            parses(src),
            "if-expression with no else, continued condition, must parse"
        );
    }

    /// The `if`-expression used directly as a call argument (matches the
    /// original defect site's call-argument context for the lambda bug).
    #[test]
    fn or_continuation_if_expr_as_call_arg() {
        let src = "fn main():\n\
                   \x20   print(if 1 == 1 or\n\
                   \x20       1 == 2: \"a\" else: \"b\")\n";
        assert!(
            parses(src),
            "if-expression as call argument, continued condition, must parse"
        );
    }

    /// Parenthesized continuation neighbor: the condition itself wraps in
    /// parens rather than relying on a trailing operator — must already work
    /// (bracket depth suppresses newlines) and must keep working.
    #[test]
    fn control_parenthesized_condition_continuation() {
        let src = "fn main():\n\
                   \x20   val x = if (1 == 1 or\n\
                   \x20       1 == 2): \"a\" else: \"b\"\n\
                   \x20   print(x)\n";
        assert!(parses(src), "parenthesized multi-line condition must parse");
    }

    // ---- Neighbors: while / match must not regress ----

    #[test]
    fn control_while_multiline_condition_still_parses() {
        let src = "fn main():\n\
                   \x20   var i = 0\n\
                   \x20   while i == 0 or\n\
                   \x20       i == 1:\n\
                   \x20       i = i + 1\n";
        assert!(parses(src), "while with continued condition must still parse");
    }

    #[test]
    fn control_match_guard_multiline_condition_still_parses() {
        let src = "fn main():\n\
                   \x20   val v = 1\n\
                   \x20   match v:\n\
                   \x20       n if n == 1 or\n\
                   \x20           n == 2: print(\"a\")\n\
                   \x20       _: print(\"b\")\n";
        assert!(parses(src), "match guard with continued condition must still parse");
    }

    // ---- Controls: must keep passing ----

    /// Single-line condition, inline both branches — never touched forced
    /// indentation or deferred-dedent machinery, must keep working.
    #[test]
    fn control_single_line_condition_if_expr() {
        let src = "fn main():\n\
                   \x20   val x = if 1 == 1: \"a\" else: \"b\"\n\
                   \x20   print(x)\n";
        assert!(parses(src), "single-line condition if-expression must parse");
    }

    /// Block-form then/else branches with a multi-line condition — exercised
    /// by the 2026-07-13 fix already, must keep working.
    #[test]
    fn control_block_form_multiline_condition() {
        let src = "fn main():\n\
                   \x20   if 1 == 1 or\n\
                   \x20       1 == 2:\n\
                   \x20       print(\"a\")\n\
                   \x20   else:\n\
                   \x20       print(\"b\")\n";
        assert!(parses(src), "block-form if with continued condition must parse");
    }

    // ---- Block-form if-EXPRESSION with an equal-column condition continuation ----

    /// Block-form then/else branches whose condition continuation column is
    /// EQUAL to the body column (`riscv_scalar_csr_owner.spl`'s exact shape).
    /// The lexer emits no fresh Indent for the body in this shape — the
    /// condition continuation's own pseudo-Indent already opened that level
    /// — which `expect(Indent)` did not account for, failing with "expected
    /// Indent, found <first body token>". Statement-form `if` already
    /// handles this via `parse_condition_block`; the if-EXPRESSION path did
    /// not.
    #[test]
    fn block_form_equal_column_condition_continuation() {
        let src = "fn main():\n\
                   \x20   val x = if 1 == 1 or\n\
                   \x20       1 == 2:\n\
                   \x20       \"a\"\n\
                   \x20   else:\n\
                   \x20       \"b\"\n\
                   \x20   print(x)\n";
        assert!(parses(src), "block-form equal-column condition continuation must parse");
    }

    /// Same shape but with a multi-statement then-branch, to confirm the
    /// full block body (not just its first statement) is parsed.
    #[test]
    fn block_form_equal_column_multi_statement_body() {
        let src = "fn main():\n\
                   \x20   val x = if 1 == 1 or\n\
                   \x20       1 == 2:\n\
                   \x20       var y = 1\n\
                   \x20       y + 1\n\
                   \x20   else:\n\
                   \x20       0\n\
                   \x20   print(x)\n";
        assert!(
            parses(src),
            "block-form equal-column with multi-statement body must parse"
        );
    }

    /// The riscv_scalar_csr_owner.spl block-form shape reproduced verbatim.
    #[test]
    fn control_csr_owner_block_form_shape() {
        let src = "fn main():\n\
                   \x20   val field = [\"event_id\"]\n\
                   \x20   val output_name = if field[0] == \"event_id\" or field[0] == \"decode_event_id\" or\n\
                   \x20       field[0] == \"illegal_valid\":\n\
                   \x20       \"completion_\" + field[0]\n\
                   \x20   else:\n\
                   \x20       field[0]\n\
                   \x20   print(output_name)\n";
        assert!(parses(src), "csr_owner block-form shape must parse");
    }

    /// The riscv_scalar_fence_owner.spl shape reproduced verbatim (adapted
    /// field-access to a simple array literal to stay self-contained).
    #[test]
    fn control_original_triage_shape() {
        let src = "fn main():\n\
                   \x20   val field = [\"event_id\"]\n\
                   \x20   val output_name = if field[0] == \"event_id\" or field[0] == \"decode_event_id\" or\n\
                   \x20       field[0] == \"illegal_valid\": \"completion_\" + field[0] else: field[0]\n\
                   \x20   print(output_name)\n";
        assert!(parses(src), "original triage report shape must parse");
    }
}
