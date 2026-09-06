#[cfg(test)]
mod rejoined_continuation {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    /// A continuation that nests deeper and then rejoins the outer
    /// continuation level TWICE used to die on the DEDENT before the second
    /// operand with "expected expression, found Dedent". One nesting always
    /// worked, which is why this survived so long.
    /// See doc/08_tracking/bug/
    /// parser_rejects_rejoined_nested_operator_continuation_2026-08-04.md.
    #[test]
    fn rejoined_nested_continuation_parses() {
        let src = "fn g(x: text) -> text:\n    x\n\
                   fn f(a: text, b: text) -> bool:\n\
                   \x20   a == b and\n\
                   \x20       a ==\n\
                   \x20           g(b) and\n\
                   \x20       a ==\n\
                   \x20           g(b)\n";
        assert!(parses(src), "rejoined nested continuation must parse");
    }

    /// The single-nesting form was already accepted; keep it that way so the
    /// dedent-absorption fix cannot regress the case it was built around.
    #[test]
    fn single_nested_continuation_still_parses() {
        let src = "fn g(x: text) -> text:\n    x\n\
                   fn f(a: text, b: text) -> bool:\n\
                   \x20   a == b and\n\
                   \x20       a ==\n\
                   \x20           g(b)\n";
        assert!(parses(src), "single nested continuation regressed");
    }

    /// The real shape this was found on: a long `and` chain mixing flat
    /// comparisons with two deeper-nested ones, as an implicit-return body.
    /// Reduced from src/lib/common/crypto/x25519_mlkem768/
    /// measurement_qualification.spl `_qualification_observation_matches`.
    #[test]
    fn observation_matches_shape_parses() {
        let src = "fn clock(o: text) -> text:\n    o\n\
                   fn m(t: text, o: text) -> bool:\n\
                   \x20   t == o and\n\
                   \x20       t == o and\n\
                   \x20       t == o and\n\
                   \x20       t ==\n\
                   \x20           o and\n\
                   \x20       t ==\n\
                   \x20           clock(o)\n";
        assert!(parses(src), "measurement_qualification shape must parse");
    }

    /// Guard the boundary the fix depends on: absorption is credit-bounded, so
    /// a DEDENT that ends the enclosing block must still terminate the
    /// expression rather than swallowing the next statement into the chain.
    #[test]
    fn block_closing_dedent_still_ends_expression() {
        let src = "fn f(a: i64, b: i64) -> i64:\n\
                   \x20   if a > 0:\n\
                   \x20       val s = a +\n\
                   \x20           b\n\
                   \x20       return s\n\
                   \x20   b\n";
        assert!(parses(src), "block-closing dedent handling regressed");
    }
}
