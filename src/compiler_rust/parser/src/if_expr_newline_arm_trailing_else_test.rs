//! Regression matrix for
//! `doc/08_tracking/bug/riscv_scalar_product_vhdl_else_parse_2026-08-12.md`.
//!
//! An inline `if`/`else` **expression** whose then-arm starts on the line
//! after the colon but has the `else:` (or a mid-chain `elif ...:`) trailing
//! on the arm's own line — e.g.
//!
//! ```simple
//! val kind = if accepted_valid:
//!     "acceptance_to_composition" else: "skid_to_composition"
//! ```
//!
//! used to fail with "expected expression, found Else": the block-form
//! then-branch loop in `parse_if_expr` only stopped at `Dedent`/`EOF`, so the
//! trailing `else` was fed to `parse_item` as the start of another body
//! statement. The self-hosted compiler accepts both this and the block form;
//! the seed parser now does too (the loop breaks on `Else`/`Elif` as well).
//!
//! Minimized from
//! `src/compiler/50.mir/hwir/riscv_scalar_product_composition.spl` and
//! `src/compiler/70.backend/backend/riscv_scalar_product_to_vhdl.spl`.
#[cfg(test)]
mod if_expr_newline_arm_trailing_else {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    /// The bug record's own minimized repro shape: newline-started then-arm
    /// with `else:` trailing on the arm's line.
    #[test]
    fn newline_arm_trailing_else() {
        let src = "fn pick(flag: bool) -> text:\n\
                   \x20   val r = if flag:\n\
                   \x20       \"yes\" else: \"no\"\n\
                   \x20   r\n";
        assert!(parses(src), "newline-started then-arm with trailing else must parse");
    }

    /// Same shape inside a struct-literal field (the original defect site in
    /// riscv_scalar_product_composition.spl was a binding `kind:` argument).
    #[test]
    fn newline_arm_trailing_else_in_field_position() {
        let src = "struct B:\n\
                   \x20   kind: text\n\
                   \x20   width: i32\n\
                   \n\
                   fn mk(flag: bool) -> B:\n\
                   \x20   B(kind: if flag:\n\
                   \x20       \"a\" else: \"b\", width: 1)\n";
        assert!(parses(src), "trailing else inside a field argument must parse");
    }

    /// Mid-chain `elif` trailing on the then-arm's own line (`if c1:\n arm1
    /// elif c2: arm2 else: arm3`) — the shape called out in the seed-grammar
    /// workaround commit as also rejected.
    #[test]
    fn newline_arm_trailing_elif_chain() {
        let src = "fn pick(flag: bool, kind: text) -> text:\n\
                   \x20   val r = if kind == \"a\":\n\
                   \x20       \"a1\" elif kind == \"b\": \"b1\" else: \"b2\"\n\
                   \x20   r\n";
        assert!(parses(src), "elif trailing on a newline-started then-arm must parse");
    }

    /// An elif whose OWN then-arm is newline-started with a same-line
    /// trailing else (`elif c:\n    arm else: arm`), ending the chain.
    #[test]
    fn elif_newline_arm_trailing_else() {
        let src = "fn pick(flag: bool, kind: text) -> text:\n\
                   \x20   val r = if kind == \"a\":\n\
                   \x20       \"a1\"\n\
                   \x20   elif kind == \"b\":\n\
                   \x20       \"b1\" else: \"b2\"\n\
                   \x20   r\n";
        assert!(parses(src), "elif with newline-arm trailing else must parse");
    }

    /// The exact arm-nesting depth of the original report: nested inline if
    /// in a newline-started arm of an outer if-expression, outer `else:`
    /// trailing at the outer arm's column.
    #[test]
    fn nested_newline_arm_trailing_else() {
        let src = "fn pick(flag: bool, kind: text) -> text:\n\
                   \x20   val r = if kind == \"a\":\n\
                   \x20       if flag: \"p\" else: \"q\"\n\
                   \x20   elif kind == \"b\": \"b1\"\n\
                   \x20   else: \"b2\"\n\
                   \x20   r\n";
        assert!(parses(src), "nested newline-arm trailing else chain must parse");
    }

    // ---- Statement-form if: same trailing-else grammar on block bodies ----

    /// The statement-level shape of the bug record's repro:
    /// `if flag:\n    "yes" else: "no"` as a bare statement.
    #[test]
    fn stmt_block_body_trailing_else() {
        let src = "fn main():\n\
                   \x20   if 1 == 1:\n\
                   \x20       print(\"yes\") else: print(\"no\")\n";
        assert!(parses(src), "statement if with trailing else on the arm line must parse");
    }

    /// Statement-form with a trailing `elif` on the then-arm line and a
    /// normally-indented elif body.
    #[test]
    fn stmt_block_body_trailing_elif() {
        let src = "fn main():\n\
                   \x20   if 1 == 1:\n\
                   \x20       print(\"a\") elif 1 == 2:\n\
                   \x20       print(\"b\")\n";
        assert!(parses(src), "statement if with trailing elif on the arm line must parse");
    }

    /// Statement-form chain where BOTH the then-arm and the elif body end on
    /// same-line trailing else/elif — two INDENTs are closed after the chain.
    #[test]
    fn stmt_block_body_trailing_elif_else_both_unclosed() {
        let src = "fn main():\n\
                   \x20   if 1 == 1:\n\
                   \x20       print(\"a\") elif 1 == 2:\n\
                   \x20       print(\"b\") else: print(\"c\")\n\
                   \x20   print(\"done\")\n";
        assert!(
            parses(src),
            "statement chain with two trailing-else-terminated bodies must parse"
        );
    }

    /// Statement-form trailing else followed by a sibling statement of the
    /// enclosing block — the arm's Dedent must not swallow the block's own
    /// closing Dedent.
    #[test]
    fn stmt_trailing_else_then_sibling_statement() {
        let src = "fn main():\n\
                   \x20   if 1 == 1:\n\
                   \x20       print(\"a\") else: print(\"b\")\n\
                   \x20   print(\"after\")\n";
        assert!(parses(src), "sibling statement after a trailing-else if must parse");
    }

    /// Statement-form if is the last statement of the function — the arm's
    /// Dedent must not swallow the function body's own closing Dedent.
    #[test]
    fn stmt_trailing_else_at_fn_end() {
        let src = "fn main():\n\
                   \x20   if 1 == 1:\n\
                   \x20       print(\"a\") else: print(\"b\")\n";
        assert!(parses(src), "trailing-else if at the end of a function body must parse");
    }

    // ---- Controls: must keep passing ----

    /// A stray `else` with no `if` must still be rejected (the block-body
    /// break hands it to the statement parser, which errors).
    #[test]
    fn control_stray_else_still_rejected() {
        let src = "fn main():\n\
                   \x20   print(\"a\") else: print(\"b\")\n";
        assert!(!parses(src), "a stray else must still be a parse error");
    }

    /// Same-line then-arm with same-line else — never touched the block-form
    /// loop, must keep working.
    #[test]
    fn control_fully_inline() {
        let src = "fn main():\n\
                   \x20   val x = if 1 == 1: \"a\" else: \"b\"\n\
                   \x20   print(x)\n";
        assert!(parses(src), "fully inline if-expression must parse");
    }

    /// Canonical block form (else on its own line, arm on the following
    /// line) — the accepted workaround shape, must keep working.
    #[test]
    fn control_block_form() {
        let src = "fn main():\n\
                   \x20   val x = if 1 == 1:\n\
                   \x20       \"a\"\n\
                   \x20   else:\n\
                   \x20       \"b\"\n\
                   \x20   print(x)\n";
        assert!(parses(src), "canonical block form must parse");
    }

    /// Multi-statement newline-started then-arm followed by a trailing else
    /// on the LAST arm statement's line — the break must only fire between
    /// statements, not swallow a legitimately-started body statement.
    #[test]
    fn multi_statement_arm_still_parsed() {
        let src = "fn main():\n\
                   \x20   val x = if 1 == 1:\n\
                   \x20       var y = 2\n\
                   \x20       y\n\
                   \x20   else:\n\
                   \x20       0\n\
                   \x20   print(x)\n";
        assert!(parses(src), "multi-statement block then-arm must keep parsing");
    }
}
