#[cfg(test)]
mod multiline_shapes {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    /// Two consecutive trailing-`=` continuations. The dedent drain consumed
    /// the RHS line's terminating Newline, erasing the statement boundary, so
    /// the no-paren-call scan then swallowed the next statement and died on its
    /// `=` with "expected expression, found Assign". A single continuation
    /// parsed fine, which is what hid this.
    /// See doc/08_tracking/bug/
    /// parser_consecutive_trailing_equals_continuations_2026-08-04.md.
    #[test]
    fn consecutive_trailing_equals_continuations_parse() {
        assert!(
            parses("fn f(c: C, v: text):\n    c.a =\n        v\n    c.b =\n        v\n"),
            "two consecutive multi-line assignments must parse"
        );
        assert!(
            parses("fn f(c: C, v: text):\n    c.a =\n        v\n    c.b =\n        g(\n            c)\n"),
            "multi-line assign followed by multi-line-call assign must parse"
        );
    }

    /// A single continuation followed by a keyword-led statement always worked;
    /// keep it green so the reordering cannot regress the no-paren-call form.
    #[test]
    fn single_trailing_equals_and_no_paren_call_still_parse() {
        assert!(
            parses("fn f(c: C, v: text):\n    c.a =\n        v\n    return c\n"),
            "single multi-line assignment regressed"
        );
        assert!(
            parses("fn f(x: i64):\n    val y = double 5\n    y\n"),
            "no-paren call in assignment regressed"
        );
    }

    /// Trailing-`->` signature continuation: the arrow stays on the parameter
    /// line and the return type wraps to the next. The leading form
    /// (`->` starting the next line) was already handled; this one failed with
    /// "expected identifier, found Newline".
    #[test]
    fn trailing_arrow_signature_continuation_parses() {
        assert!(
            parses("fn f(\n        a: text,\n        b: text) ->\n        Result<text, text>:\n    Ok(a)\n"),
            "trailing-arrow return type must parse"
        );
    }

    /// Guard both pre-existing arrow forms.
    #[test]
    fn other_arrow_forms_still_parse() {
        assert!(
            parses("fn f(\n        a: text,\n        b: text) -> Result<text, text>:\n    Ok(a)\n"),
            "same-line arrow regressed"
        );
        assert!(
            parses("fn f(a: text)\n        -> text:\n    a\n"),
            "leading arrow regressed"
        );
    }

    /// Inline `if cond: <assignment>`. The block form always worked; the
    /// inline form parsed its body as an expression and rejected the `=`.
    /// See doc/08_tracking/bug/parser_inline_if_assignment_body_2026-08-04.md.
    #[test]
    fn inline_if_assignment_body_parses() {
        assert!(
            parses("fn f(d: D, k: text):\n    if k == \"t\": d[k] = true\n"),
            "inline if with assignment body must parse"
        );
        assert!(
            parses("fn f(d: D, e: D, k: text):\n    if k == \"t\": d[k] = true\n    else: e[k] = true\n"),
            "inline if/else with assignment bodies must parse"
        );
        assert!(
            parses("fn f(d: D, k: text):\n    if k == \"a\": d[k] = 1\n    elif k == \"b\": d[k] = 2\n    else: d[k] = 3\n"),
            "inline if/elif/else with assignment bodies must parse"
        );
    }

    /// The inline `if` must still work as a ternary-style EXPRESSION, and as a
    /// plain call statement — the two shapes the assignment path branches away
    /// from.
    #[test]
    fn inline_if_expression_and_call_forms_still_parse() {
        assert!(
            parses("fn f(x: i64) -> i64:\n    if x < 0: -x\n    else: x\n"),
            "inline if expression form regressed"
        );
        assert!(
            parses("fn f(k: text):\n    if k == \"t\": g(k)\n"),
            "inline if call statement regressed"
        );
    }

    /// `val x = if <condition spanning lines>:` — the statement form drained
    /// the compensating DEDENT but the expression form did not, so it hit the
    /// DEDENT where it wanted the body's INDENT.
    /// See doc/08_tracking/bug/
    /// parser_if_expression_multiline_condition_dedent_2026-08-04.md.
    #[test]
    fn if_expression_with_multiline_condition_parses() {
        assert!(
            parses("fn f(a: text, b: text) -> text:\n    val r = if a == \"x\" and\n            b == \"y\":\n        a\n    else:\n        b\n    r\n"),
            "if-expression with multi-line condition must parse"
        );
        assert!(
            parses("fn f(a: text, b: text) -> text:\n    val r = if a == \"x\" and\n            b == \"y\":\n        a\n    elif a == \"z\" and\n            b == \"w\":\n        b\n    else:\n        a\n    r\n"),
            "if-expression with multi-line condition and elif must parse"
        );
    }

    /// Guard the single-line-condition if-expression and the statement form
    /// that already worked.
    #[test]
    fn single_line_condition_forms_still_parse() {
        assert!(
            parses(
                "fn f(a: text, b: text) -> text:\n    val r = if a == \"x\":\n        a\n    else:\n        b\n    r\n"
            ),
            "single-line-condition if-expression regressed"
        );
        assert!(
            parses("fn f(a: text, b: text) -> text:\n    if a == \"x\" and\n            b == \"y\":\n        return a\n    b\n"),
            "statement if with multi-line condition regressed"
        );
    }
}
