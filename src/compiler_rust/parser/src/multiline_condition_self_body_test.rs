#[cfg(test)]
mod multiline_condition_self_body {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    fn err(src: &str) -> String {
        match crate::Parser::new(src).parse() {
            Ok(_) => String::new(),
            Err(e) => format!("{:?}", e),
        }
    }

    /// An `if`/`while` whose condition uses a multi-line operator continuation
    /// at the SAME column as the body emits no fresh `Indent` for the body, so
    /// `header_continuation_is_equal_column` must recognise the body's first
    /// token as a statement start. `is_statement_start` listed `Identifier` and
    /// `Me` but NOT `Self_`, so a body beginning `self.x = ...` fell through to
    /// `expect(Indent)` and failed with "expected Indent, found Self_".
    ///
    /// A body whose first statement started with anything else — including an
    /// ordinary identifier — parsed fine, which is what made this look like an
    /// indentation problem rather than a token-list omission.
    ///
    /// Item 23 of doc/08_tracking/bug/
    /// unit_sweep_language_and_interpreter_gaps_2026-08-26.md.
    #[test]
    fn equal_column_continuation_with_self_led_body_parses() {
        let src = "fn f(self: S) -> R:\n    if self.x ==\n            A.Armed and\n        self.y == 1:\n        self.z = 1\n        return Ok(1)\n    Err(-1)\n";
        assert!(parses(src), "self-led body must parse: {}", err(src));
        assert!(
            parses("fn f(self: S) -> R:\n    while a:\n        if self.x ==\n                A.Armed and\n            self.y == 1:\n            self.z =\n                A.C\n            return Ok(1)\n        b()\n    Err(-1)\n"),
            "self-led body nested inside a while must parse"
        );
        assert!(
            parses("fn f(self: S) -> R:\n    while a:\n        if self.x == A.Armed and\n            self.y == 1:\n            self.z = 1\n            return Ok(1)\n        b()\n    Err(-1)\n"),
            "uniform-column continuation with a self-led body must parse"
        );
    }

    /// `_` is the other token the list was missing (`_ = f()` discards a value).
    #[test]
    fn equal_column_continuation_with_underscore_led_body_parses() {
        assert!(
            parses("fn f(a: bool, b: bool) -> R:\n    if a and\n        b:\n        _ = g()\n        return Ok(1)\n    Err(-1)\n"),
            "`_`-led body after an equal-column continuation must parse"
        );
    }

    /// The flat-body shape (`is_statement_start`'s other caller) gains the same
    /// two tokens: `if cond:` with the single-statement body at the SAME column.
    #[test]
    fn flat_body_with_self_and_underscore_parses() {
        assert!(
            parses("fn f(self: S):\n    if a:\n    self.x = 1\n"),
            "flat `self`-led body must parse"
        );
        assert!(
            parses("fn f(self: S):\n    if a:\n    _ = g()\n"),
            "flat `_`-led body must parse"
        );
    }

    /// Shapes that already worked must keep working — these are what hid the
    /// defect, so a regression here would be invisible without them.
    #[test]
    fn previously_working_shapes_still_parse() {
        assert!(
            parses("fn f(self: S) -> R:\n    if self.x ==\n            A.Armed and\n        self.y == 1:\n        g()\n        return Ok(1)\n    Err(-1)\n"),
            "identifier-led body regressed"
        );
        assert!(
            parses("fn f(self: S) -> R:\n    if self.x ==\n            A.Armed:\n        self.z = 1\n    Err(-1)\n"),
            "deeper-column continuation with a self-led body regressed"
        );
        assert!(
            parses("fn f(a: bool, b: bool) -> R:\n    if a and\n        b:\n        return Ok(1)\n    Err(-1)\n"),
            "equal-column continuation with a return-led body regressed"
        );
    }

    /// Trailing-colon TYPE ANNOTATION continuation: the type wraps to the next
    /// line, with the initializer still on it. Failed with "expected identifier,
    /// found Newline". This is the second half of item 23; the bug record's
    /// suspicion of a `.?` or `==`/`!=` continuation was wrong — it is the type
    /// annotation that wraps.
    #[test]
    fn trailing_colon_type_annotation_continuation_parses() {
        let src = "var g_service:\n    ServiceV1? = nil\n";
        assert!(parses(src), "wrapped var type must parse: {}", err(src));
        assert!(
            parses("val g_x:\n    i64 = 1\nval g_y:\n    i64 = 2\n"),
            "two consecutive wrapped-type declarations must parse"
        );
        assert!(
            parses("fn f() -> i64:\n    val x:\n        i64 = 1\n    x\n"),
            "wrapped type on a local declaration must parse"
        );
        assert!(
            parses("var g_a:\n    ServiceV1? = nil\nfn f() -> i64:\n    1\n"),
            "a declaration after a wrapped-type var must not be swallowed"
        );
    }

    /// The non-wrapped forms must be untouched.
    #[test]
    fn same_line_type_annotations_still_parse() {
        assert!(parses("var g_x: i64 = 1\n"), "same-line typed var regressed");
        assert!(
            parses("val g_y: ServiceV1? = nil\n"),
            "same-line optional type regressed"
        );
        assert!(
            parses("fn f() -> i64:\n    val x: i64 = 1\n    x\n"),
            "local typed val regressed"
        );
    }

    /// The fix must not weaken the grammar: a colon with no type after it on
    /// either line is still an error.
    #[test]
    fn malformed_type_annotations_still_rejected() {
        assert!(
            !parses("var g_x:\n= 1\n"),
            "a wrapped type annotation with no type must still be rejected"
        );
        assert!(
            !parses("var g_x: = 1\n"),
            "a same-line type annotation with no type must still be rejected"
        );
    }
}
