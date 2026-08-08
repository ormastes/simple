//! Gate: an `if`/`elif`/`else if` whose body sits at the same column as its
//! header continuation must parse the WHOLE body, not just its first statement.
//!
//! Bug: doc/08_tracking/bug/
//! parser_while_continuation_swallows_following_declarations_2026-08-01.md
//! (section "Follow-up: parse_condition_block's flat-body path").
//!
//! Mechanism. A leading-operator continuation in an `if`/`elif` condition makes
//! the lexer open a pseudo-INDENT for the continuation line. When the body then
//! sits at that same column, no fresh `Indent` is emitted — the continuation's
//! pseudo-INDENT IS the block's own INDENT. `parse_condition_block` therefore
//! fell into `parse_block_after_newline`'s "flat body" path, which is documented
//! to parse exactly ONE statement (the `if cond:` / next-line-same-column
//! one-liner shape). Every further statement of a genuinely indented body leaked
//! out of the `if`, and the surplus deferred DEDENT then desynchronised the rest
//! of the file.
//!
//! `while`/`for`/`match` already special-cased this shape in their own header
//! parsers; `if`/`elif` reach the block through `parse_condition_block`, which
//! did not, so the sibling fix did not cover them.
//!
//! Each fixture below is compared against a CONTROL that is the same code with
//! the header on one line. The comparison is a span-free structural digest, so
//! it catches re-parenting (a statement moving from the `if` body out to the
//! enclosing block) and not merely a top-level item count change.

use simple_parser::{Node, Parser};

/// Span-free structural digest: node variant names plus block sizes, nested.
/// Two programs with the same digest have the same statement tree shape.
fn shape(n: &Node, depth: usize, out: &mut String) {
    let pad = "  ".repeat(depth);
    match n {
        Node::Function(f) => {
            out.push_str(&format!("{pad}fn {}[{}]\n", f.name, f.body.statements.len()));
            for st in &f.body.statements {
                shape(st, depth + 1, out);
            }
        }
        Node::If(i) => {
            out.push_str(&format!("{pad}if then[{}]\n", i.then_block.statements.len()));
            for st in &i.then_block.statements {
                shape(st, depth + 1, out);
            }
            for (_, _, b) in &i.elif_branches {
                out.push_str(&format!("{pad}elif[{}]\n", b.statements.len()));
                for st in &b.statements {
                    shape(st, depth + 1, out);
                }
            }
            if let Some(b) = &i.else_block {
                out.push_str(&format!("{pad}else[{}]\n", b.statements.len()));
                for st in &b.statements {
                    shape(st, depth + 1, out);
                }
            }
        }
        Node::While(w) => {
            out.push_str(&format!("{pad}while[{}]\n", w.body.statements.len()));
            for st in &w.body.statements {
                shape(st, depth + 1, out);
            }
        }
        Node::For(f) => {
            out.push_str(&format!("{pad}for[{}]\n", f.body.statements.len()));
            for st in &f.body.statements {
                shape(st, depth + 1, out);
            }
        }
        other => {
            // Variant name only — the Debug payload carries spans, which differ
            // between a repro and its single-line control by construction.
            let d = format!("{other:?}");
            let name = d.split(['(', '{', ' ']).next().unwrap_or("?");
            out.push_str(&format!("{pad}{name}\n"));
        }
    }
}

/// `Some(structural digest)`, or `None` if the source does not parse.
fn digest(src: &str) -> Option<String> {
    let mut p = Parser::new(src);
    let ast = p.parse().ok()?;
    let mut s = format!("items[{}]\n", ast.items.len());
    for it in &ast.items {
        shape(it, 1, &mut s);
    }
    Some(s)
}

/// The repro (multi-line header) must parse to the SAME tree as the control
/// (single-line header), and the control must itself expose `items` top-level
/// items so the comparison cannot pass by both sides being degenerate.
fn assert_parity(name: &str, repro: &str, control: &str, items: usize) {
    let control_d = digest(control).unwrap_or_else(|| panic!("{name}: CONTROL must parse"));
    assert!(
        control_d.starts_with(&format!("items[{items}]\n")),
        "{name}: CONTROL must expose {items} top-level items, got:\n{control_d}"
    );
    let repro_d = digest(repro).unwrap_or_else(|| "<parse error>".to_string());
    assert_eq!(
        repro_d, control_d,
        "{name}: the equal-column condition continuation did not parse the whole \
         body.\n--- repro ---\n{repro_d}\n--- control ---\n{control_d}"
    );
}

const IF_REPRO: &str = "\
fn f(n: i64) -> i64:
    if n
        > 0:
        var a = 1
        var b = 2
        return a + b
    return 0

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const IF_CONTROL: &str = "\
fn f(n: i64) -> i64:
    if n > 0:
        var a = 1
        var b = 2
        return a + b
    return 0

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const IF_AND_ELSE_REPRO: &str = "\
fn f(n: i64) -> i64:
    if n > 0
        and n < 10:
        var a = 1
        return a
    else:
        var b = 2
        return b

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const IF_AND_ELSE_CONTROL: &str = "\
fn f(n: i64) -> i64:
    if n > 0 and n < 10:
        var a = 1
        return a
    else:
        var b = 2
        return b

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const ELIF_REPRO: &str = "\
fn f(n: i64) -> i64:
    if n < 0:
        return 0
    elif n
        > 0:
        var a = 1
        var b = 2
        return a + b
    return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const ELIF_CONTROL: &str = "\
fn f(n: i64) -> i64:
    if n < 0:
        return 0
    elif n > 0:
        var a = 1
        var b = 2
        return a + b
    return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const ELSE_IF_REPRO: &str = "\
fn f(n: i64) -> i64:
    if n < 0:
        return 0
    else if n
        > 0:
        var a = 1
        var b = 2
        return a + b
    return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const ELSE_IF_CONTROL: &str = "\
fn f(n: i64) -> i64:
    if n < 0:
        return 0
    else if n > 0:
        var a = 1
        var b = 2
        return a + b
    return 2

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const NESTED_IF_REPRO: &str = "\
fn f(n: i64) -> i64:
    if n > 5:
        if n
            > 7:
            var a = 1
            var b = 2
            return a + b
        return 3
    return 0

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const NESTED_IF_CONTROL: &str = "\
fn f(n: i64) -> i64:
    if n > 5:
        if n > 7:
            var a = 1
            var b = 2
            return a + b
        return 3
    return 0

fn later() -> i64:
    return 42

fn main():
    print(\"hi\")
";

const TOP_LEVEL_IF_REPRO: &str = "\
if 1
    > 0:
    var a = 1
    var b = 2

fn main():
    print(\"hi\")
";

const TOP_LEVEL_IF_CONTROL: &str = "\
if 1 > 0:
    var a = 1
    var b = 2

fn main():
    print(\"hi\")
";

#[test]
fn if_equal_column_continuation_parses_whole_body() {
    assert_parity("if `> 0`", IF_REPRO, IF_CONTROL, 3);
}

#[test]
fn if_equal_column_continuation_with_else_parses_whole_body() {
    assert_parity("if `and ...` + else", IF_AND_ELSE_REPRO, IF_AND_ELSE_CONTROL, 3);
}

#[test]
fn elif_equal_column_continuation_parses_whole_body() {
    assert_parity("elif `> 0`", ELIF_REPRO, ELIF_CONTROL, 3);
}

#[test]
fn else_if_equal_column_continuation_parses_whole_body() {
    assert_parity("else if `> 0`", ELSE_IF_REPRO, ELSE_IF_CONTROL, 3);
}

#[test]
fn nested_if_equal_column_continuation_parses_whole_body() {
    assert_parity("nested if `> 7`", NESTED_IF_REPRO, NESTED_IF_CONTROL, 3);
}

#[test]
fn top_level_if_equal_column_continuation_parses_whole_body() {
    assert_parity("top-level if `> 0`", TOP_LEVEL_IF_REPRO, TOP_LEVEL_IF_CONTROL, 2);
}

/// A single-statement equal-column body already worked; it must keep working.
/// (This case passes both before and after the fix — it is the boundary that
/// the one-statement flat-body path happened to get right.)
#[test]
fn single_statement_equal_column_body_still_parses() {
    const REPRO: &str = "\
fn f(n: i64) -> i64:
    if n
        > 0:
        return 1
    return 0
";
    const CONTROL: &str = "\
fn f(n: i64) -> i64:
    if n > 0:
        return 1
    return 0
";
    assert_parity("if `> 0` single stmt", REPRO, CONTROL, 1);
}

/// Guard on the OTHER flat-body shape, which this fix must NOT change: a body
/// at the `if`'s own column (no header continuation at all) is the documented
/// one-statement "flat body" form, and the statements after it belong to the
/// ENCLOSING block. Making that greedy would swallow the rest of the function.
#[test]
fn true_flat_body_stays_single_statement() {
    const SRC: &str = "\
fn f(n: i64) -> i64:
    if n > 0:
    var a = 1
    var b = 2
    return a + b
";
    let d = digest(SRC).expect("flat body must parse");
    assert_eq!(
        d, "items[1]\n  fn f[3]\n    if then[1]\n      Let\n    Let\n    Return\n",
        "the header-continuation fix must not change the true flat-body shape"
    );
}

/// The `while`/`for`/`match` equal-column shapes fixed by the sibling change
/// must stay fixed, and their multi-statement bodies must stay whole.
#[test]
fn loop_equal_column_bodies_unaffected() {
    const WHILE_REPRO: &str = "\
fn f(n: i64) -> i64:
    var i = 0
    while i
        < n:
        var a = 1
        i = i + a
    return i
";
    const WHILE_CONTROL: &str = "\
fn f(n: i64) -> i64:
    var i = 0
    while i < n:
        var a = 1
        i = i + a
    return i
";
    assert_parity("while `< n`", WHILE_REPRO, WHILE_CONTROL, 1);
}

/// Non-vacuity guard: every repro fixture must actually differ from its control,
/// otherwise all the parity assertions above would pass for the wrong reason.
#[test]
fn repro_and_control_fixtures_actually_differ() {
    for (repro, control) in [
        (IF_REPRO, IF_CONTROL),
        (IF_AND_ELSE_REPRO, IF_AND_ELSE_CONTROL),
        (ELIF_REPRO, ELIF_CONTROL),
        (ELSE_IF_REPRO, ELSE_IF_CONTROL),
        (NESTED_IF_REPRO, NESTED_IF_CONTROL),
        (TOP_LEVEL_IF_REPRO, TOP_LEVEL_IF_CONTROL),
    ] {
        assert_ne!(repro, control, "repro fixture must differ from its control");
    }
}
