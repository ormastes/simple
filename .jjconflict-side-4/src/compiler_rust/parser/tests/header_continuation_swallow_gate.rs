//! Gate: a leading-operator continuation in a `while`/`for`/`match` HEADER must
//! not swallow the declarations that follow the enclosing function.
//!
//! Bug: doc/08_tracking/bug/
//! parser_while_continuation_swallows_following_declarations_2026-08-01.md
//!
//! Mechanism. When the continuation line's column EQUALS the block body's
//! column, the lexer emits no fresh `Indent` — the pseudo-INDENT consumed by the
//! operator continuation IS the block's own INDENT, and `parse_block_body`
//! consumes its matching DEDENT as the body terminator. The header parsers then
//! ALSO counted that same DEDENT in `deferred_before` and consumed a second one,
//! eating a DEDENT owned by an ENCLOSING block. Every following top-level
//! declaration was silently re-parented into the current function — `parse()`
//! still returned `Ok`, so nothing anywhere reported an error.
//!
//! These fixtures fail (1 top-level item instead of 3) before the fix in
//! `header_continuation_dedents_to_reconcile` and pass after it.

use simple_parser::Parser;

/// Number of TOP-LEVEL items the parser exposes, or `None` on a parse error.
fn top_level_count(src: &str) -> Option<usize> {
    let mut p = Parser::new(src);
    p.parse().ok().map(|ast| ast.items.len())
}

/// Assert that `repro` (with a header continuation) and `control` (same code,
/// header on one line) agree, and that both expose `expected` top-level items.
fn assert_parity(name: &str, repro: &str, control: &str, expected: usize) {
    let control_n = top_level_count(control);
    assert_eq!(
        control_n,
        Some(expected),
        "{name}: CONTROL (single-line header) must expose {expected} top-level items"
    );
    let repro_n = top_level_count(repro);
    assert_eq!(
        repro_n, control_n,
        "{name}: the multi-line header continuation swallowed the following \
         declarations (got {repro_n:?}, control {control_n:?})"
    );
}

const WHILE_REPRO: &str = "\
fn w(n: i64) -> i64:
    var i = 0
    while i
        < n:
        i = i + 1
    if n > 0:
        return 1
    else:
        return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const WHILE_CONTROL: &str = "\
fn w(n: i64) -> i64:
    var i = 0
    while i < n:
        i = i + 1
    if n > 0:
        return 1
    else:
        return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const WHILE_AND_REPRO: &str = "\
fn w(n: i64) -> i64:
    var i = 0
    while i < n
        and i < 100:
        i = i + 1
    if n > 0:
        return 1
    else:
        return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const WHILE_AND_CONTROL: &str = "\
fn w(n: i64) -> i64:
    var i = 0
    while i < n and i < 100:
        i = i + 1
    if n > 0:
        return 1
    else:
        return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const FOR_REPRO: &str = "\
fn f(xs: [i64], ys: [i64]) -> i64:
    var t = 0
    for x in xs
        + ys:
        t = t + x
    if t > 0:
        return 1
    else:
        return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const FOR_CONTROL: &str = "\
fn f(xs: [i64], ys: [i64]) -> i64:
    var t = 0
    for x in xs + ys:
        t = t + x
    if t > 0:
        return 1
    else:
        return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const MATCH_REPRO: &str = "\
fn m(a: i64, b: i64) -> i64:
    match a
        + b:
        case 0: return 10
        case _: return 20

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const MATCH_CONTROL: &str = "\
fn m(a: i64, b: i64) -> i64:
    match a + b:
        case 0: return 10
        case _: return 20

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

#[test]
fn while_leading_operator_header_does_not_swallow_following_declarations() {
    assert_parity("while `< n`", WHILE_REPRO, WHILE_CONTROL, 3);
}

#[test]
fn while_leading_and_header_does_not_swallow_following_declarations() {
    assert_parity("while `and ...`", WHILE_AND_REPRO, WHILE_AND_CONTROL, 3);
}

#[test]
fn for_leading_operator_header_does_not_swallow_following_declarations() {
    assert_parity("for `+ ys`", FOR_REPRO, FOR_CONTROL, 3);
}

#[test]
fn match_leading_operator_subject_does_not_swallow_following_declarations() {
    assert_parity("match `+ b`", MATCH_REPRO, MATCH_CONTROL, 3);
}

/// Non-vacuity guard: the fixtures really do exercise the continuation path.
/// If the repro and control texts were accidentally identical, every assertion
/// above would pass for the wrong reason.
#[test]
fn repro_and_control_fixtures_actually_differ() {
    for (repro, control) in [
        (WHILE_REPRO, WHILE_CONTROL),
        (WHILE_AND_REPRO, WHILE_AND_CONTROL),
        (FOR_REPRO, FOR_CONTROL),
        (MATCH_REPRO, MATCH_CONTROL),
    ] {
        assert_ne!(repro, control, "repro fixture must differ from its control");
    }
}
