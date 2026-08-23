//! Gate: a BODYLESS block header (`if`/`elif`/`else`/`while`/`for`) is a parse
//! error, while an empty `case nil:` match-arm body stays legal.
//!
//! Bug: doc/08_tracking/bug/
//! seed_accepts_bodyless_if_native_build_rejects_2026-08-22.md
//!
//! Mechanism. `parse_block_after_newline` returned an EMPTY `Block` on
//! Dedent/Eof with no error. Its own comment says that arm exists for
//! `case nil:` match arms, but the function is shared with
//! `parse_condition_block`, so match-arm leniency leaked into conditionals and
//! the seed silently accepted a bodyless `if` as a no-op — source the
//! pure-Simple front end (`native-build`) rejects. The arm is now gated by
//! `allow_empty_body`: `parse_block` passes `true` (match arms keep it),
//! `parse_condition_block` passes `false`.
//!
//! The match-arm case is asserted POSITIVELY in the same file so a future
//! tightening of the shared arm cannot pass this gate by breaking match arms.

use simple_parser::Parser;

fn parses(src: &str) -> bool {
    let mut p = Parser::new(src);
    p.parse().is_ok()
}

#[test]
fn bodyless_if_before_dedent_is_a_parse_error() {
    // Row A of the bug record: last statement of a method, next line dedents.
    let src = "\
class Probe:
    n: i64

impl Probe:
    me first():
        self.n = 1
        if self.n > 0:

    me second() -> i64:
        self.n
";
    assert!(!parses(src), "bodyless `if` before a Dedent must not parse");
}

#[test]
fn bodyless_if_at_eof_is_a_parse_error() {
    assert!(
        !parses("fn probe(flag: bool):\n    if flag:\n"),
        "bodyless `if` at Eof must not parse"
    );
}

#[test]
fn bodyless_while_and_for_are_parse_errors() {
    assert!(
        !parses("fn probe(flag: bool):\n    while flag:\n\n    pass\n"),
        "bodyless `while` must not parse"
    );
    assert!(
        !parses("fn probe(xs: [i64]):\n    for x in xs:\n\n    pass\n"),
        "bodyless `for` must not parse"
    );
}

#[test]
fn empty_match_arm_body_still_parses() {
    // The empty-block arm is load-bearing here and must survive the gate. It
    // fires when the empty arm is the LAST one, i.e. the body is followed by a
    // Dedent — an empty arm followed by another `case` has never parsed on
    // either front end (verified against the pre-fix seed), so that shape is
    // deliberately not asserted here.
    let src = "\
fn probe(v: i64?) -> i64:
    match v:
        case _:
            return 1
        case nil:
    0
";
    assert!(parses(src), "empty trailing `case nil:` arm must still parse");
}

#[test]
fn flat_body_and_real_body_still_parse() {
    // Row B and the control of the bug record: both must keep working.
    assert!(
        parses("fn probe(flag: bool) -> i64:\n    if flag:\n    return 7\n    3\n"),
        "flat body (same-column statement) must still parse"
    );
    assert!(
        parses("fn probe(flag: bool) -> i64:\n    if flag:\n        return 2\n    7\n"),
        "real indented body must still parse"
    );
}

#[test]
fn bodyless_if_before_same_column_integer_is_a_parse_error() {
    // Row C: the seed already rejected this; pin it so the gate cannot regress
    // into the pure-Simple side's old accept-and-miscompile behaviour.
    assert!(
        !parses("fn probe(flag: bool) -> i64:\n    if flag:\n\n    7\n"),
        "bodyless `if` before a same-column integer must not parse"
    );
}
