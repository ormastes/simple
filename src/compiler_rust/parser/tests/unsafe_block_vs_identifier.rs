//! Regression pins for `doc/08_tracking/bug/
//! seed_redeploy_breaks_test_runner_accessor_rewrite_parse_2026-08-25.md`.
//!
//! `unsafe` / `danger` are ordinary identifiers, not reserved words. A seed
//! built from an unlanded tree accepted a bare `unsafe:` as an unsafe-block
//! PRIMARY, so an ordinary variable named `unsafe` used as the last token of a
//! block header swallowed the header's own colon plus the whole body, and
//! `src/lib/nogc_sync_mut/tooling/easy_fix/accessor_rewrite.spl:134`
//! (`for existing in unsafe:`) failed with "expected Colon, found If".
//!
//! Both directions are pinned: the identifier uses must parse, and the
//! capability-scoped block form (statement AND value position) must keep
//! parsing, since that form is what the redeploy was for.

use simple_parser::Parser;

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    if let Err(e) = parser.parse() {
        panic!("should parse, got {e:?}\n--- source ---\n{src}");
    }
}

#[test]
fn identifier_named_unsafe_as_for_iterable() {
    // The exact shape of accessor_rewrite.spl:134.
    parse_ok("fn f():\n    var unsafe: List<text> = []\n    for e in unsafe:\n        print(e)\n    if true:\n        print(\"d\")\n");
}

#[test]
fn identifier_named_unsafe_as_while_condition() {
    parse_ok(
        "fn f():\n    var unsafe: bool = false\n    while unsafe:\n        break\n    if true:\n        print(\"d\")\n",
    );
}

#[test]
fn identifier_named_unsafe_as_if_condition() {
    parse_ok("fn f():\n    var unsafe: bool = false\n    if unsafe:\n        print(\"a\")\n    if true:\n        print(\"d\")\n");
}

#[test]
fn identifier_named_danger_as_for_iterable() {
    // Same soft-keyword pair; `danger` is the other name the block form uses.
    parse_ok("fn f():\n    var danger: List<text> = []\n    for e in danger:\n        print(e)\n    if true:\n        print(\"d\")\n");
}

#[test]
fn statement_position_bare_unsafe_block_still_parses() {
    parse_ok("fn f():\n    unsafe:\n        print(\"raw\")\n    print(\"after\")\n");
}

#[test]
fn statement_position_capability_unsafe_block_still_parses() {
    parse_ok("fn f():\n    unsafe(capabilities: [ffi]):\n        print(\"raw\")\n    print(\"after\")\n");
}

#[test]
fn value_bound_capability_unsafe_block_still_parses() {
    // The form the 2026-08-25 seed was redeployed for; must not regress.
    parse_ok("fn f():\n    val v = unsafe(capabilities: [ffi]):\n        1\n    print(v)\n");
}

#[test]
fn value_bound_capability_unsafe_block_with_reason_still_parses() {
    parse_ok(
        "fn f():\n    val v = unsafe(reason: \"raw ffi\", capabilities: [ffi, raw_ptr]):\n        1\n    print(v)\n",
    );
}
