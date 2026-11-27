//! Regression matrix for
//! `doc/08_tracking/bug/seed_elif_inline_assign_2026-11-27.md`.
//!
//! A lane reported that the seed rejects a one-line `elif c: x = v` statement
//! arm. It did not reproduce on current source (both the seed and the
//! pure-Simple parser accept it); these tests pin the accepted shapes so a
//! future seed parser change cannot regress them silently.
#[cfg(test)]
mod elif_inline_assign {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    #[test]
    fn inline_if_elif_else_assign() {
        let src = "fn f(c: i64) -> i64:\n\
                   \x20   var x = 0\n\
                   \x20   if c == 1: x = 10\n\
                   \x20   elif c == 2: x = 20\n\
                   \x20   else: x = 30\n\
                   \x20   x\n";
        assert!(parses(src), "one-line if/elif/else assignment arms must parse");
    }

    #[test]
    fn block_if_then_inline_elif_assign() {
        let src = "fn g(c: bool, d: bool) -> i64:\n\
                   \x20   var x = 0\n\
                   \x20   if c:\n\
                   \x20       x = 1\n\
                   \x20   elif d: x = 2\n\
                   \x20   else:\n\
                   \x20       x = 3\n\
                   \x20   x\n";
        assert!(parses(src), "inline elif after a block then-arm must parse");
    }

    #[test]
    fn inline_elif_field_index_and_compound_assign() {
        let src = "fn h(c: bool, d: bool, a: [i64]):\n\
                   \x20   var x = 0\n\
                   \x20   if c: a[0] = 1\n\
                   \x20   elif d: self_x = 2\n\
                   \x20   elif x == 0: x += 3\n";
        assert!(parses(src), "inline elif with index/compound assignment must parse");
    }

    #[test]
    fn inline_elif_after_nested_inline_if() {
        let src = "fn k(c: bool, d: bool, i: i64) -> i64:\n\
                   \x20   var x = 0\n\
                   \x20   if i == 1:\n\
                   \x20       if c: x = 5\n\
                   \x20   elif d: x = i\n\
                   \x20   x\n";
        assert!(parses(src), "inline elif after a nested inline if must bind to the outer if");
    }

    #[test]
    fn module_level_inline_elif_assign() {
        let src = "var m = 0\nif false: m = 1\nelif true: m = 2\n";
        assert!(parses(src), "module-level inline elif assignment must parse");
    }
}
