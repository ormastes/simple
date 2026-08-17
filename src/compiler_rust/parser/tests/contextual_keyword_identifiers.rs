//! Contextual soft-keyword identifiers in expression position.
//!
//! Bug: doc/08_tracking/bug/move_identifier_rejected_as_expression_2026-08-15.md
//!
//! `move` is a contextual keyword: it introduces a move-closure (`move \x: ...`)
//! and a unary move (`move value`), but it is also an ordinary variable name.
//! Until 2026-08-17 the parser accepted the *declaration* `var move = 3` and
//! then rejected the very next *use* — `while move + 1u32 < n` died with
//! `expected expression, found Plus`, because `move` unconditionally consumed
//! the following token as its operand.
//!
//! There is already a `.spl` regression spec
//! (`test/01_unit/compiler/parser_move_contextual_keyword_spec.spl`), but it can
//! only run on a rebuilt seed — the deployed `bin/simple` predates the fix and
//! still reports the Plus error, so that spec cannot settle the question today.
//! These tests exercise the parser crate directly and therefore give a verdict
//! now, on current source.

use simple_parser::Parser;

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    if let Err(err) = parser.parse() {
        panic!("should parse, got error: {err}\n--- source ---\n{src}");
    }
}

/// REPRODUCING TEST. Every one of these is `move` used as an ordinary
/// identifier in expression position; each fails with
/// "expected expression, found <operator>" if `parse_unary` goes back to
/// treating `move` as an unconditional prefix operator.
#[test]
fn move_reads_as_an_ordinary_identifier_in_expression_position() {
    // The exact shape from the bug report: declare, then read on the left of a
    // binary operator.
    parse_ok("var move = 3\nlet a = move + 1");
    // ... and on the right.
    parse_ok("var move = 3\nlet b = 2 + move");
    // The literal `while move + 1 < limit` loop condition that broke draw_ir.
    parse_ok("var move = 0\nwhile move + 1 < 4:\n    move = move + 1");
    // Reassignment, comparison, and passing it as an argument.
    parse_ok("var move = 1\nmove = move * 10");
    parse_ok("var move = 1\nlet c = move < 5 and move > 0");
    parse_ok("var move = 1\nlet d = str(move)");
    // Field access and indexing off a receiver named `move`.
    parse_ok("var move = [1, 2]\nlet e = move[0]");
}

/// COUNTERPART: the contextual rule must not disable the keyword meaning.
/// A fix that simply demoted `move` to a plain identifier would pass the test
/// above while silently breaking move-closures, so this pins the other side.
#[test]
fn move_still_introduces_a_move_closure_and_a_unary_move() {
    parse_ok("let f = move \\x: x + 1");
    parse_ok("var v = 1\nlet g = move v");
}

/// SIMILAR-PROBLEM DETECTION TEST for the defect CLASS: a soft keyword that is
/// accepted where it is *declared* but rejected where it is *used*.
///
/// `move` was the third instance of this shape in this parser, after `examples`
/// and `and_then` (see
/// doc/08_tracking/bug/examples_identifier_rejected_in_named_argument_position_2026-08-10.md).
/// The class is what matters, not the individual name: for every contextual
/// keyword the parser lets you bind, reading it back in the ordinary expression
/// positions — binary operand, comparison, assignment target, index base,
/// call argument — must parse. A newly-added soft keyword that forgets its
/// identifier arm fails here without anyone having to remember to file it.
#[test]
fn every_bindable_soft_keyword_reads_back_in_ordinary_expression_positions() {
    // Soft keywords this parser has an explicit identifier arm for
    // (parser/src/expressions/primary/identifiers.rs) plus the two that were
    // historically broken. `self`/`me` are excluded: they are not bindable.
    let soft_keywords = [
        "move", "spawn", "lazy", "skip", "into", "bind", "unwrap", "on", "with", "use", "export",
        "requires", "auto", "where", "mod", "onto", "by", "examples", "and_then",
    ];

    for kw in soft_keywords {
        // binary operand, both sides
        parse_ok(&format!("var {kw} = 3\nlet a = {kw} + 1"));
        parse_ok(&format!("var {kw} = 3\nlet b = 1 + {kw}"));
        // comparison in a loop condition — where `move` actually blew up
        parse_ok(&format!(
            "var {kw} = 0\nwhile {kw} + 1 < 4:\n    {kw} = {kw} + 1"
        ));
        // assignment target
        parse_ok(&format!("var {kw} = 1\n{kw} = {kw} * 10"));
        // call argument
        parse_ok(&format!("var {kw} = 1\nlet d = str({kw})"));
    }
}
