//! Regression: an inline `if c: X as T else: Y` lost its else arm because the
//! postfix `as T` parser took `else:` as its cast-fallback suffix
//! (`X as T else: fallback` -> `Expr::CastElse`), leaving the `if` with
//! `else_branch: None`. See
//! doc/08_tracking/bug/inline_if_then_arm_as_cast_drops_else_2026-10-05.md.

#[cfg(test)]
mod inline_if_as_cast_else {
    fn ast(src: &str) -> String {
        let module = crate::Parser::new(src).parse().expect("parse");
        format!("{:?}", module.items)
    }

    /// The inline if keeps an else arm and no cast swallowed it.
    fn assert_else_kept(src: &str) {
        let dbg = ast(src);
        assert!(
            !dbg.contains("CastElse"),
            "cast swallowed the if's else in {src:?}: {dbg}"
        );
        assert!(!dbg.contains("else_branch: None"), "else arm dropped in {src:?}: {dbg}");
        assert!(dbg.contains("else_branch: Some"), "no if-else parsed in {src:?}: {dbg}");
    }

    #[test]
    fn then_arm_cast_in_val() {
        assert_else_kept("fn g(c: bool, x: i64) -> i64:\n    val v = if c: x as i64 else: 7\n    v\n");
    }

    #[test]
    fn then_arm_indexed_cast() {
        assert_else_kept("fn g(c: bool, a: [u8]) -> i64:\n    val v = if c: a[1] as i64 else: 7\n    v\n");
    }

    #[test]
    fn both_arms_cast_as_tail_statement() {
        assert_else_kept("fn g(c: bool, a: [u8], i: i64, j: i64) -> i64:\n    if c: a[i] as i64 else: a[j] as i64\n");
    }

    #[test]
    fn else_arm_cast_only() {
        assert_else_kept("fn g(c: bool, x: i32) -> i64:\n    val v = if c: 7 else: x as i64\n    v\n");
    }

    #[test]
    fn method_call_cast_in_return() {
        assert_else_kept("fn g(c: bool, v: [u8]) -> i64:\n    return if c: v.len() as i64 else: 7\n");
    }

    #[test]
    fn cast_in_call_argument() {
        assert_else_kept("fn g(c: bool, x: i64) -> i64:\n    id(if c: x as i64 else: 7)\n");
    }

    #[test]
    fn array_and_generic_cast_types() {
        assert_else_kept("fn g(c: bool, v: any) -> any:\n    val a = if c: v as [u8] else: []\n    a\n");
        assert_else_kept("fn g(c: bool, v: any) -> any:\n    val a = if c: v as Option<i64> else: nil\n    a\n");
    }

    #[test]
    fn chained_and_nested_casts() {
        assert_else_kept("fn g(c: bool, x: i64) -> i64:\n    val v = if c: x as i32 as i64 else: 7\n    v\n");
        assert_else_kept(
            "fn g(a: bool, b: bool, x: i64) -> i64:\n    if a: x as i64 else: if b: (x + 1) as i64 else: 9\n",
        );
        assert_else_kept(
            "fn g(a: bool, b: bool, x: i64) -> i64:\n    val v = if a: x as i64 elif b: x as i32 as i64 else: 9\n    v\n",
        );
    }

    #[test]
    fn then_keyword_form() {
        assert_else_kept("fn g(c: bool, x: i64) -> i64:\n    val v = if c then x as i64 else 7\n    v\n");
    }

    #[test]
    fn inline_statement_arms() {
        let dbg = ast("fn g(c: bool, x: i64) -> i64:\n    var r = 0\n    if c: r = x as i64 else: r = 7\n    r\n");
        assert!(!dbg.contains("CastElse"), "{dbg}");
        assert!(dbg.contains("else_block: Some"), "{dbg}");
    }

    #[test]
    fn ternary_condition_cast() {
        let dbg = ast("fn g(n: i64) -> i64:\n    val v = 1 if n as bool else 2\n    v\n");
        assert!(!dbg.contains("CastElse"), "{dbg}");
        assert!(dbg.contains("else_branch: Some"), "{dbg}");
    }

    /// Outside an inline-if then arm the `as T else: fallback` suffix is unchanged.
    #[test]
    fn standalone_cast_else_still_parses() {
        assert!(ast("fn g(x: any) -> i64:\n    val v = x as i64 else: fallback\n    v\n").contains("CastElse"));
        assert!(
            ast("fn g(c: bool, x: any) -> i64:\n    val v = if c: 7 else: x as i64 else: fallback\n    v\n")
                .contains("CastElse")
        );
        assert!(
            ast("fn g(c: bool, x: any) -> i64:\n    if c:\n        val v = x as i64 else: fallback\n        return v\n    0\n")
                .contains("CastElse")
        );
    }
}
