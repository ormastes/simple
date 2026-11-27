// Regression gate: a leading-dot method-chain continuation that ENDS a
// multi-line block header (`if`/`while` condition).
//
//     if path_absolute(a).replace("\\", "/").lower() !=
//             path_absolute(b)
//                 .replace("\\", "/").lower():
//         return Err(...)
//
// (src/app/bootstrap_builder/native_group_phase2_admission.spl:93-95)
//
// The pure-Simple lexer (src/compiler/10.frontend/core/lexer_struct.spl,
// leading-`.` rule in handle_indentation and the newline arm of scan_token)
// suppresses both the Newline and the Indent of any line whose first
// non-blank character is `.`, with no indent guard, so the shape is valid
// Simple. The seed handles the same chain in the parser instead
// (`parse_postfix`, `consumed_indents`): it skips the Indent and later pairs
// it with a Dedent. When the chain ended at `:` that remainder was silently
// DROPPED, the lexer's `Dedent Dedent Indent` after the header Newline was
// drained one short, and `parse_condition_block` failed with
// "expected Indent, found Dedent". The fix hands the remainder to
// `deferred_dedent_count`, the same channel the binary-operator continuation
// uses.
//
// Structure is asserted, not just `is_ok()`: an unbalanced Dedent's failure
// mode is silent re-parenting of the following statements.
//
// Run: cargo test -p simple-parser --test leading_dot_continuation_block_header

use simple_parser::ast::{Block, Expr, FunctionDef, Node};

fn parse_module(src: &str) -> Vec<Node> {
    simple_parser::Parser::new(src)
        .parse()
        .unwrap_or_else(|e| panic!("parse failed for:\n{src}\nerror: {e:?}"))
        .items
}

fn as_fn(node: &Node) -> &FunctionDef {
    match node {
        Node::Function(f) => f,
        other => panic!("expected a function item, found {other:?}"),
    }
}

fn stmt_kinds(block: &Block) -> Vec<&'static str> {
    block
        .statements
        .iter()
        .map(|s| match s {
            Node::If(_) => "if",
            Node::While(_) => "while",
            Node::Return(_) => "return",
            Node::Let(_) => "let",
            Node::Expression(_) => "expr",
            _ => "other",
        })
        .collect()
}

fn if_then_kinds(block: &Block, index: usize) -> Vec<&'static str> {
    match &block.statements[index] {
        Node::If(stmt) => stmt_kinds(&stmt.then_block),
        other => panic!("expected `if` at statement {index}, found {other:?}"),
    }
}

/// Two functions, so re-parenting of the second into the first is visible.
fn two_fns(first_body: &str) -> String {
    format!("fn first(a: text, b: text) -> i64:\n{first_body}\nfn second() -> i64:\n    return 3\n")
}

#[test]
fn leading_dot_chain_ending_if_header_deep_shape() {
    // Continuation columns (12, 16) deeper than the body column (8): the
    // lexer emits `Dedent Dedent Indent` right after the header's Newline.
    let src = two_fns(
        "    if a !=\n\
         \x20           b\n\
         \x20               .lower():\n\
         \x20       return 1\n\
         \x20   return 2",
    );
    let items = parse_module(&src);
    assert_eq!(items.len(), 2, "both functions must stay top-level:\n{src}\n{items:#?}");
    let first = as_fn(&items[0]);
    assert_eq!(first.name, "first");
    assert_eq!(stmt_kinds(&first.body), vec!["if", "return"], "{src}");
    assert_eq!(if_then_kinds(&first.body, 0), vec!["return"], "{src}");
    assert_eq!(as_fn(&items[1]).name, "second");
}

#[test]
fn leading_dot_chain_ending_if_header_exact_product_shape() {
    // Verbatim shape of native_group_phase2_admission.spl:93-95 inside a
    // function, followed by a sibling statement at the `if`'s own indent.
    let src = two_fns(
        "    if path_absolute(a).replace(\"\\\\\", \"/\").lower() !=\n\
         \x20           path_absolute(b)\n\
         \x20               .replace(\"\\\\\", \"/\").lower():\n\
         \x20       return 1\n\
         \x20   val rest = a.len()\n\
         \x20   return rest",
    );
    let items = parse_module(&src);
    assert_eq!(items.len(), 2, "{src}\n{items:#?}");
    let first = as_fn(&items[0]);
    assert_eq!(stmt_kinds(&first.body), vec!["if", "let", "return"], "{src}");
    assert_eq!(if_then_kinds(&first.body, 0), vec!["return"], "{src}");
}

#[test]
fn leading_dot_chain_ending_if_header_shallow_shape() {
    // Continuation column (6) shallower than the body column (8): the
    // compensating Dedent only appears AFTER the body, with the block's own.
    let src = two_fns(
        "    if a\n\
         \x20     .lower() != b:\n\
         \x20       return 1\n\
         \x20   return 2",
    );
    let items = parse_module(&src);
    assert_eq!(items.len(), 2, "{src}\n{items:#?}");
    let first = as_fn(&items[0]);
    assert_eq!(stmt_kinds(&first.body), vec!["if", "return"], "{src}");
    assert_eq!(if_then_kinds(&first.body, 0), vec!["return"], "{src}");
}

#[test]
fn leading_dot_chain_ending_if_header_equal_column_shape() {
    // Continuation column == body column (8): the chain's Indent IS the body's.
    let src = two_fns(
        "    if a\n\
         \x20       .lower() != b:\n\
         \x20       return 1\n\
         \x20   return 2",
    );
    let items = parse_module(&src);
    assert_eq!(items.len(), 2, "{src}\n{items:#?}");
    let first = as_fn(&items[0]);
    assert_eq!(stmt_kinds(&first.body), vec!["if", "return"], "{src}");
    assert_eq!(if_then_kinds(&first.body, 0), vec!["return"], "{src}");
}

#[test]
fn leading_dot_chain_ending_while_header() {
    let src = two_fns(
        "    while a\n\
         \x20           .lower() != b:\n\
         \x20       return 1\n\
         \x20   return 2",
    );
    let items = parse_module(&src);
    assert_eq!(items.len(), 2, "{src}\n{items:#?}");
    let first = as_fn(&items[0]);
    assert_eq!(stmt_kinds(&first.body), vec!["while", "return"], "{src}");
}

#[test]
fn leading_dot_chain_followed_by_operator_settles_at_expression_end() {
    // The chain is followed by `+ 1` on the same line, so its Dedent only
    // appears after the whole expression. The remainder must be settled by
    // `parse_expression_inner`, not left for a later block header: the
    // following `if` must still own exactly its own body, and the sibling
    // statements and the second `fn` must stay where they are.
    let src = two_fns(
        "    val x = a\n\
         \x20       .len() + 1\n\
         \x20   if x > 1:\n\
         \x20       return 1\n\
         \x20   return x",
    );
    let items = parse_module(&src);
    assert_eq!(items.len(), 2, "{src}\n{items:#?}");
    let first = as_fn(&items[0]);
    assert_eq!(stmt_kinds(&first.body), vec!["let", "if", "return"], "{src}");
    assert_eq!(if_then_kinds(&first.body, 1), vec!["return"], "{src}");
    match &first.body.statements[0] {
        Node::Let(l) => assert!(
            matches!(l.value, Some(Expr::Binary { .. })),
            "binding value must be the chain plus `1`: {:?}",
            l.value
        ),
        other => panic!("expected let, found {other:?}"),
    }
    assert_eq!(as_fn(&items[1]).name, "second");
}

#[test]
fn leading_dot_chain_in_binding_still_pairs_its_dedent_locally() {
    // The pre-existing opportunistic path (Newline + Dedent right after the
    // chain) must be unchanged: nothing is deferred, and the next statement
    // stays a sibling.
    let src = two_fns(
        "    val x = a\n\
         \x20       .lower()\n\
         \x20   return x.len()",
    );
    let items = parse_module(&src);
    assert_eq!(items.len(), 2, "{src}\n{items:#?}");
    let first = as_fn(&items[0]);
    assert_eq!(stmt_kinds(&first.body), vec!["let", "return"], "{src}");
    match &first.body.statements[0] {
        Node::Let(l) => assert!(
            matches!(l.value, Some(Expr::MethodCall { .. })),
            "binding value must be the full method chain: {:?}",
            l.value
        ),
        other => panic!("expected let, found {other:?}"),
    }
}
