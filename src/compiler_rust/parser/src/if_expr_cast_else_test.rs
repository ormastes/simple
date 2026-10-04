//! Regression for
//! `doc/08_tracking/bug/jit_if_expr_branch_as_i64_cast_yields_3_2026-10-04.md`.
//!
//! `if c: x as T else: v` used to parse as `if c: (x as T else: v)` -- the
//! `CastElse` fallback form -- leaving the `if` with no else branch. The
//! interpreter then returned nil on the false path and the JIT produced the
//! constants 3/0. The pure-Simple parser has no `CastElse`, so the two front
//! ends disagreed on 48 sites in `src/`. Inside an inline then-branch the
//! `else:` now belongs to the `if`; elsewhere `CastElse` is unchanged.
#[cfg(test)]
mod if_expr_cast_else {
    fn ast(src: &str) -> String {
        let module = crate::Parser::new(src).parse().expect("source must parse");
        format!("{:?}", module)
    }

    #[test]
    fn inline_if_then_cast_keeps_the_if_else() {
        let dump = ast("fn f(g: i32) -> i64:\n    val s: i64 = if g > 0: g as i64 else: 5\n    s\n");
        assert!(!dump.contains("CastElse"), "the else must not become a cast fallback: {dump}");
        assert!(dump.contains("else_branch: Some"), "the if must keep its else branch: {dump}");
    }

    #[test]
    fn parenthesised_multiline_if_then_cast_keeps_the_if_else() {
        let src = "fn f(g: i32) -> i64:\n    var c: i64 = 0\n    c = c + (if g > 0:\n        g as i64\n    else:\n        5)\n    c\n";
        let dump = ast(src);
        assert!(!dump.contains("CastElse"), "{dump}");
        assert!(dump.contains("else_branch: Some"), "{dump}");
    }

    #[test]
    fn cast_else_outside_an_if_is_unchanged() {
        let dump = ast("fn f(g: i32) -> i64:\n    val s = g as i64 else: \\: 0\n    s\n");
        assert!(dump.contains("CastElse"), "plain `as T else:` keeps the fallback form: {dump}");
    }

    #[test]
    fn cast_else_in_a_call_argument_inside_the_then_branch_is_unchanged() {
        let dump = ast("fn f(g: i32) -> i64:\n    val s = if g > 0: h(g as i64 else: \\: 0) else: 5\n    s\n");
        assert!(dump.contains("CastElse"), "a nested call argument keeps its own fallback: {dump}");
        assert!(dump.contains("else_branch: Some"), "{dump}");
    }

    /// Statement-position inline `if` (the tail of a block-form if-expression,
    /// FontRenderer.get_glyph_advance_milli's shape) took a different parse
    /// path that did not mark the then-branch.
    #[test]
    fn nested_statement_position_inline_if_cast_keeps_the_if_else() {
        let src = "fn f(a: i64, r: i32) -> i32:\n    val x = if r > 0:\n        if a > 0: a as i32 else: r * 1000\n    else:\n        7\n    x\n";
        let dump = ast(src);
        assert!(!dump.contains("CastElse"), "{dump}");
        assert_eq!(dump.matches("else_branch: Some").count(), 2, "both ifs keep their else: {dump}");
    }

    /// Generalisation: a bare statement-level inline `if` with a cast branch.
    #[test]
    fn statement_inline_if_cast_keeps_the_if_else() {
        let src = "fn f(a: i64) -> i32:\n    if a > 0: a as i32 else: 0\n";
        let dump = ast(src);
        assert!(!dump.contains("CastElse"), "{dump}");
        assert!(dump.contains("else_branch: Some"), "{dump}");
    }

    #[test]
    fn else_branch_cast_is_unchanged() {
        let dump = ast("fn f(g: i32) -> i64:\n    val s: i64 = if g < 0: 5 else: g as i64\n    s\n");
        assert!(!dump.contains("CastElse"), "{dump}");
        assert!(dump.contains("else_branch: Some"), "{dump}");
    }
}
