#[cfg(test)]
mod coalesce_diverging_fallback {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    fn err(src: &str) -> String {
        match crate::Parser::new(src).parse() {
            Ok(_) => String::new(),
            Err(e) => format!("{:?}", e),
        }
    }

    /// `expr ??\n    return X` failed with "expected expression, found Dedent".
    /// `return`/`break`/`continue` are usable as plain identifiers in primary
    /// position, so `parse_pipe` read `return` as a name and `X` as a no-paren
    /// call argument; on the multi-line form that scan ran past the statement's
    /// Newline and died at the enclosing block's DEDENT. A BARE `return` (no
    /// operand) parsed fine, which is what hid this.
    ///
    /// This was the whole of item 25 of doc/08_tracking/bug/
    /// unit_sweep_language_and_interpreter_gaps_2026-08-26.md for
    /// `src/os/port/initramfs_validate.spl` and
    /// `src/os/port/guest_toolchain_artifact_build_receipt.spl`.
    #[test]
    fn multiline_coalesce_return_fallback_parses() {
        let src = "fn f() -> R:\n    val p = g() ??\n        return Err(\"m\")\n    Ok(p)\n";
        assert!(parses(src), "`?? \\n return X` must parse: {}", err(src));
        assert!(
            parses("fn f() -> R:\n    val p = g() ??\n        return d\n    Ok(p)\n"),
            "`?? \\n return <ident>` must parse"
        );
        assert!(
            parses("fn f() -> R:\n    val p = g() ??\n        return Err(\"m\")\n"),
            "`?? \\n return X` as the last statement of a function must parse"
        );
        assert!(
            parses("fn f() -> R:\n    val p = g() ??\n        return Err(\"m\")\n    val q = 1\n    Ok(p + q)\n"),
            "statements after a `?? \\n return X` fallback must still be seen"
        );
    }

    /// `break`/`continue` fallbacks are OUT OF SCOPE of the fix: there is no
    /// loop-control counterpart to `UnwrapOrReturn`, and before this change they
    /// parsed only as bare identifiers, so there is no working runtime behaviour
    /// to preserve. Pinned here as "still parses, semantics unspecified" so a
    /// later fix has a starting point and this change is not credited with more
    /// than it does. See the sub-item under 25 in the bug record.
    #[test]
    fn break_and_continue_fallbacks_are_unchanged_by_this_fix() {
        assert!(
            parses("fn f(n: i64):\n    while n > 0:\n        val p = g() ??\n            break\n        h(p)\n"),
            "`?? \\n break` parse acceptance changed"
        );
    }

    /// Controls: the value fallback and the same-line form must keep working.
    /// The value form never broke and proves the fix did not touch general
    /// `??` continuation handling.
    #[test]
    fn coalesce_value_and_single_line_forms_still_parse() {
        assert!(
            parses("fn f() -> R:\n    val p = g() ??\n        d\n    Ok(p)\n"),
            "multi-line `??` with a plain value fallback regressed"
        );
        assert!(
            parses("fn f() -> R:\n    val p = g() ?? d\n    Ok(p)\n"),
            "single-line `??` with a value fallback regressed"
        );
        assert!(
            parses("fn f() -> R:\n    val p = g() ?? return Err(\"m\")\n    Ok(p)\n"),
            "single-line `?? return X` regressed"
        );
        assert!(
            parses("fn f() -> R:\n    val p = g() ??\n        h(1) + h(2)\n    Ok(p)\n"),
            "multi-line `??` with a compound value fallback regressed"
        );
    }

    /// The fix must not weaken the grammar: a `??` with no fallback at all is
    /// still an error.
    #[test]
    fn coalesce_with_no_fallback_still_rejected() {
        // NOTE: `val p = g() ??\n    Ok(p)` is NOT malformed — the next line is
        // a legitimate multi-line fallback value. Use a shape where no fallback
        // can possibly follow.
        assert!(
            !parses("fn f() -> R:\n    val p = (g() ??)\n    Ok(p)\n"),
            "`??` immediately followed by `)` must still be rejected"
        );
        assert!(
            !parses("fn f() -> R:\n    val p = [g() ??, 1]\n    Ok(p)\n"),
            "`??` immediately followed by `,` must still be rejected"
        );
    }
}
