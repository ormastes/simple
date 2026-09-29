//! Regression matrix for
//! `doc/08_tracking/bug/backslash_lambda_multiline_inline_body_dedent_2026-08-28.md`.
//!
//! A `\arg: expr` (or `fn(arg): expr`) lambda whose body is an INLINE
//! expression (starts on the same source line as the colon) that continues
//! onto later lines via a trailing binary operator (e.g. `and`/`or`) used to
//! fail with "expected expression, found Dedent" whenever the lambda itself
//! was a call argument (so forced indentation was active). Root cause: both
//! `parse_lambda_body` (backslash/move lambdas) and `parse_primary_lambda`'s
//! `fn(...)` branch called `self.lexer.disable_forced_indentation()` AFTER
//! `parse_expression()` instead of before, so the lexer emitted a forced
//! Indent/Dedent pair for the body's continuation line(s) that
//! `parse_expression()` never expected and could not consume.
#[cfg(test)]
mod lambda_multiline_inline_body {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    // ---- The failing shape: backslash lambda as a call argument ----

    /// The minimized repro (6 lines) isolated from
    /// `hwir_riscv_scalar_runtime_lsu_composition_spec.spl` (2026-08-28 lane).
    #[test]
    fn backslash_lambda_call_arg_two_line_and() {
        let src = "fn call(f: (i64)->bool) -> bool:\n\
                   \x20   [1, 2].any(f)\n\
                   fn main():\n\
                   \x20   val rows = [1, 2]\n\
                   \x20   val x = rows.any(\\row: row == 1 and\n\
                   \x20       row == 2)\n\
                   \x20   print(x)\n";
        assert!(
            parses(src),
            "backslash lambda inline body with and-continuation as a call arg must parse"
        );
    }

    /// Same shape as the real spec: multiple `and`-joined continuation lines.
    #[test]
    fn backslash_lambda_call_arg_three_line_and() {
        let src = "fn main():\n\
                   \x20   val rows = [1, 2]\n\
                   \x20   val x = rows.any(\\row: row == 1 and\n\
                   \x20       row == 2 and\n\
                   \x20       row == 3)\n\
                   \x20   print(x)\n";
        assert!(parses(src), "three-line and-continuation inline lambda body must parse");
    }

    /// `or` must behave identically to `and`.
    #[test]
    fn backslash_lambda_call_arg_or_continuation() {
        let src = "fn main():\n\
                   \x20   val rows = [1, 2]\n\
                   \x20   val x = rows.any(\\row: row == 1 or\n\
                   \x20       row == 2)\n\
                   \x20   print(x)\n";
        assert!(
            parses(src),
            "or-continuation inline lambda body as a call arg must parse"
        );
    }

    /// Two-parameter lambda, still an inline body that continues.
    #[test]
    fn backslash_lambda_two_params_continuation() {
        let src = "fn main():\n\
                   \x20   val rows = [1, 2]\n\
                   \x20   val x = rows.reduce(\\acc, row: acc == 1 and\n\
                   \x20       row == 2, 0)\n\
                   \x20   print(x)\n";
        assert!(
            parses(src),
            "two-param backslash lambda with continuation body must parse"
        );
    }

    /// Nested lambdas: the outer lambda's inline body itself contains a call
    /// with another multi-line-continued inline lambda body.
    #[test]
    fn nested_backslash_lambdas_with_continuation() {
        let src = "fn main():\n\
                   \x20   val rows = [1, 2]\n\
                   \x20   val x = rows.any(\\row: rows.any(\\inner: inner == row and\n\
                   \x20           inner == 1) and\n\
                   \x20       row == 2)\n\
                   \x20   print(x)\n";
        assert!(
            parses(src),
            "nested backslash lambdas with continuation bodies must parse"
        );
    }

    /// The `fn(...)` lambda spelling shares the same (separately gated) bug
    /// in `parser/src/expressions/primary/lambdas.rs`.
    #[test]
    fn fn_lambda_call_arg_and_continuation() {
        let src = "fn main():\n\
                   \x20   val rows = [1, 2]\n\
                   \x20   val x = rows.any(fn(row): row == 1 and\n\
                   \x20       row == 2)\n\
                   \x20   print(x)\n";
        assert!(
            parses(src),
            "fn(...) lambda inline body with and-continuation as a call arg must parse"
        );
    }

    /// `move \x: expr` shares `parse_lambda_body` with plain backslash lambdas.
    #[test]
    fn move_backslash_lambda_call_arg_continuation() {
        let src = "fn main():\n\
                   \x20   val rows = [1, 2]\n\
                   \x20   val x = rows.any(move \\row: row == 1 and\n\
                   \x20       row == 2)\n\
                   \x20   print(x)\n";
        assert!(
            parses(src),
            "move backslash lambda inline body with continuation must parse"
        );
    }

    // ---- Controls: shapes that already passed before the fix ----

    /// Single-line lambda body (no continuation) — must still parse.
    #[test]
    fn control_single_line_backslash_lambda_still_parses() {
        let src = "fn main():\n\
                   \x20   val rows = [1, 2]\n\
                   \x20   val x = rows.any(\\row: row == 1)\n\
                   \x20   print(x)\n";
        assert!(parses(src), "single-line backslash lambda regressed");
    }

    /// Genuine block-body lambda (colon followed by newline+indent) — must
    /// still parse; this is the case the forced-indentation machinery exists
    /// for and must not regress.
    #[test]
    fn control_block_body_backslash_lambda_still_parses() {
        let src = "fn main():\n\
                   \x20   val rows = [1, 2]\n\
                   \x20   val x = rows.any(\\row:\n\
                   \x20       val ok = row == 1\n\
                   \x20       ok)\n\
                   \x20   print(x)\n";
        assert!(parses(src), "block-body backslash lambda regressed");
    }

    /// A plain (non-call-argument) backslash lambda assigned to a `val`,
    /// with a continuation — this path never went through forced
    /// indentation and must still parse.
    #[test]
    fn control_plain_val_backslash_lambda_continuation_still_parses() {
        let src = "fn main():\n\
                   \x20   val f = \\row: row == 1 and\n\
                   \x20       row == 2\n\
                   \x20   print(f)\n";
        assert!(parses(src), "plain val backslash lambda with continuation regressed");
    }

    /// Trailing comma before the closing paren, after the continued body —
    /// a neighboring shape to the dedent-before-bracket-close class.
    #[test]
    fn backslash_lambda_call_arg_trailing_comma_before_close() {
        let src = "fn call(f: (i64)->bool, n: i64) -> bool:\n\
                   \x20   f(n)\n\
                   fn main():\n\
                   \x20   val x = call(\\row: row == 1 and\n\
                   \x20       row == 2, 3)\n\
                   \x20   print(x)\n";
        assert!(
            parses(src),
            "trailing comma after continued inline lambda body must parse"
        );
    }
}
