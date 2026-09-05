// Enumeration probe for trailing-token line continuation across the seed
// parser's statement/expression constructs. NOT a regression gate: every
// case just prints PASS/FAIL so the family table in the bug/fix report can
// cite `cargo test --test family_continuation_probe -- --nocapture` output
// as the determination method, per-construct, instead of inferring support
// by reading the parser source (the mistake that missed three prior gaps).
//
// Run: cargo test -p simple-parser --test family_continuation_probe -- --nocapture

fn parses(src: &str) -> bool {
    simple_parser::Parser::new(src).parse().is_ok()
}

fn probe(name: &str, src: &str) -> bool {
    let ok = parses(src);
    println!("[{}] {}", if ok { "PASS" } else { "FAIL" }, name);
    if !ok {
        if let Err(e) = simple_parser::Parser::new(src).parse() {
            println!("       error: {:?}", e);
        }
    }
    ok
}

#[test]
fn enumerate_continuation_family() {
    let mut results: Vec<(&str, bool)> = Vec::new();

    // 1. Arithmetic operators (+, -, *, /, %) — macro-generated binary parsers.
    results.push((
        "arithmetic +",
        probe(
            "arith_plus",
            "fn f(a: i64, b: i64) -> i64:\n    val x = a +\n       b\n    x\n",
        ),
    ));
    results.push((
        "arithmetic *",
        probe(
            "arith_star",
            "fn f(a: i64, b: i64) -> i64:\n    val x = a *\n       b\n    x\n",
        ),
    ));

    // 2. Logical and / or / not
    results.push((
        "logical and",
        probe(
            "logical_and",
            "fn f(a: bool, b: bool) -> bool:\n    if a and\n       b:\n        return true\n    false\n",
        ),
    ));
    results.push((
        "logical or",
        probe(
            "logical_or",
            "fn f(a: bool, b: bool) -> bool:\n    if a or\n       b:\n        return true\n    false\n",
        ),
    ));
    results.push((
        "logical not (unary, trailing on own line)",
        probe(
            "logical_not",
            "fn f(a: bool) -> bool:\n    val x =\n        not a\n    x\n",
        ),
    ));

    // 3. Comparison
    results.push((
        "comparison >",
        probe(
            "comparison_gt",
            "fn f(a: i64, b: i64) -> bool:\n    val x = a >\n       b\n    x\n",
        ),
    ));

    // 4. Equality
    results.push((
        "equality ==",
        probe(
            "equality_eq",
            "fn f(a: i64, b: i64) -> bool:\n    val x = a ==\n       b\n    x\n",
        ),
    ));

    // 5. Plain assignment `=`
    results.push((
        "plain assignment =",
        probe(
            "plain_assign",
            "fn f(a: i64) -> i64:\n    var x = 0\n    x =\n        a + 1\n    x\n",
        ),
    ));

    // 6. Compound assignment (+=, -=, etc.)
    results.push((
        "compound assignment +=",
        probe(
            "compound_assign",
            "fn f(a: i64) -> i64:\n    var x = a\n    x +=\n        a\n    x\n",
        ),
    ));

    // 7. return expressions
    results.push((
        "return <expr on next line>",
        probe(
            "return_bare_next_line",
            "fn f(a: i64) -> i64:\n    return\n        a + 1\n",
        ),
    ));
    results.push((
        "return a +\\n b",
        probe(
            "return_trailing_operator",
            "fn f(a: i64, b: i64) -> i64:\n    return a +\n        b\n",
        ),
    ));

    // 8. call-argument lists
    results.push((
        "call args trailing comma continuation",
        probe(
            "call_args_comma",
            "fn g(a: i64, b: i64) -> i64:\n    a + b\n\nfn f(a: i64, b: i64) -> i64:\n    g(a,\n      b)\n",
        ),
    ));

    // 9. collection literals
    results.push((
        "list literal trailing comma continuation",
        probe(
            "list_literal",
            "fn f() -> [i64]:\n    val xs = [1,\n              2,\n              3]\n    xs\n",
        ),
    ));

    // 10. member-access chains (`.`)
    results.push((
        "method chain trailing dot",
        probe(
            "method_chain_trailing_dot",
            "fn f(s: str) -> i64:\n    val n = s.\n        len()\n    n\n",
        ),
    ));
    results.push((
        "method chain leading dot on next line",
        probe(
            "method_chain_leading_dot",
            "fn f(s: str) -> i64:\n    val n = s\n        .len()\n    n\n",
        ),
    ));

    // 11. if/while/elif conditions
    results.push((
        "if condition trailing comparison (shallow continuation)",
        probe(
            "if_condition_shallow",
            "fn f(a: i64, b: i64) -> i64:\n    if a >\n       b:\n        return 1\n    2\n",
        ),
    ));
    results.push((
        "while condition trailing comparison",
        probe(
            "while_condition",
            "fn f(a: i64, b: i64) -> i64:\n    var i = 0\n    while a >\n          b:\n        i = i + 1\n        break\n    i\n",
        ),
    ));
    // Continuation line indented LESS than the branch body (7 spaces vs 8) —
    // the shape a7e5fbccf85's parse_elif_or_else_if_body drain fixed.
    results.push((
        "elif condition trailing comparison (continuation shallower than body)",
        probe(
            "elif_condition_shallower_than_body",
            "fn f(a: i64, b: i64) -> i64:\n    if a < 0:\n        return 1\n    elif a >\n       b:\n        return 2\n    3\n",
        ),
    ));
    // Continuation line indented MORE than the branch body (9 spaces vs 8) —
    // the still-open DEDENT-then-INDENT ambiguity filed in
    // seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
    results.push((
        "elif condition trailing comparison (continuation deeper than body)",
        probe(
            "elif_condition_deeper_than_body",
            "fn f(a: i64, b: i64) -> i64:\n    if a < 0:\n        return 1\n    elif a >\n         b:\n        return 2\n    3\n",
        ),
    ));

    println!("\n=== Continuation family summary ===");
    for (name, ok) in &results {
        println!("{:<55} {}", name, if *ok { "SUPPORTED" } else { "NOT SUPPORTED" });
    }
}
