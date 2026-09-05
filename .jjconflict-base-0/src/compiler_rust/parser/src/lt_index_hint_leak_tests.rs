//! Regression gate: a bracket index on the RHS of a comparison must not leak a
//! bogus "Deprecated syntax for type parameters" hint.
//!
//! Mechanism being pinned: on `a < arr[i]` the postfix layer speculatively tries
//! to read `<...>` as a generic-argument list (`try_skip_ident_generic_args` /
//! `try_parse_method_generic_args`). That speculation calls `parse_type`, which
//! PUSHES the `name[...]` deprecated-generics warning into `error_hints` as a
//! side effect. The speculation then correctly backtracks — token state is
//! restored and the comparison parses fine — but `error_hints` was never rolled
//! back, so the abandoned parse still emitted its diagnostic.
//!
//! The parse result was always correct; only the diagnostic leaked. These tests
//! therefore assert on `error_hints()`, which is the only observable that moves.
//!
//! See doc/08_tracking/bug/parser_bracket_index_after_less_than_still_misread_as_generics_2026-08-17.md

#[cfg(test)]
mod tests {
    use crate::parser_impl::core::Parser;

    /// Parse `source` and return the deprecated-generics hints it emitted.
    fn generic_hints(source: &str) -> Vec<String> {
        let mut parser = Parser::new(source);
        let parsed = parser.parse();
        assert!(parsed.is_ok(), "source failed to parse: {:?}", parsed.err());
        parser
            .error_hints()
            .iter()
            .filter(|h| h.message.contains("Deprecated syntax for type parameters"))
            .map(|h| h.suggestion.clone().unwrap_or_default())
            .collect()
    }

    /// Control: a bare index with no preceding `<` never tripped this. If this
    /// test ever fails, the harness is broken rather than the fix.
    #[test]
    fn bare_bracket_index_emits_no_generics_hint() {
        assert_eq!(generic_hints("fn main():\n    val x = arr[i]\n"), Vec::<String>::new());
    }

    /// The reported reproducer, reduced from
    /// src/compiler/70.backend/backend/native/regalloc.spl:158.
    #[test]
    fn bracket_index_after_less_than_emits_no_generics_hint() {
        assert_eq!(
            generic_hints("fn main():\n    if a < arr[i]:\n        print(1)\n"),
            Vec::<String>::new()
        );
    }

    /// Defect CLASS: every comparison operator that can precede an index, the
    /// `and`-chained shape from the style.spl reproducer, and a nested index.
    #[test]
    fn comparison_then_bracket_index_class_emits_no_generics_hint() {
        for src in [
            // `<` and `<=`
            "fn main():\n    if a < b[i]:\n        print(1)\n",
            "fn main():\n    if a <= b[i]:\n        print(1)\n",
            // the `and`-chained form: while j >= 0 and cur.spec < matched[j].spec
            "fn main():\n    if x >= 0 and y < arr[j].field:\n        print(1)\n",
            // nested index inside the index
            "fn main():\n    if a < b[c[d]]:\n        print(1)\n",
            // method call on the indexed element
            "fn main():\n    if a < b[i].len():\n        print(1)\n",
        ] {
            assert_eq!(generic_hints(src), Vec::<String>::new(), "leaked a hint for: {}", src);
        }
    }

    /// Guard against over-correction: a REAL `name[...]` generic type annotation
    /// must still produce the deprecation hint. Without this, the fix could be
    /// "passed" by deleting the warning outright.
    #[test]
    fn genuine_square_bracket_generic_still_warns() {
        let hints = generic_hints("fn main():\n    val x: List[i64] = f()\n");
        assert_eq!(hints.len(), 1, "expected exactly one deprecation hint, got {:?}", hints);
        assert!(hints[0].contains("List<...>"), "unexpected suggestion: {:?}", hints);
    }
}
