use simple_parser::ast::Node;
use simple_parser::Parser;

fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    parser.parse().expect("should parse");
}

// If statements
#[test]
fn parse_if_statement() {
    let items = parse("if x > 0:\n    y = 1");
    assert!(matches!(&items[0], Node::If(_)));
}

#[test]
fn parse_if_else_statement() {
    parse_ok("if x > 0:\n    y = 1\nelse:\n    y = 0");
}

#[test]
fn parse_capability_scoped_unsafe_block() {
    let items = parse(
        "fn call_raw():\n    unsafe(capabilities: [ffi, raw_ptr]):\n        raw_call()",
    );
    let Node::Function(function) = &items[0] else {
        panic!("expected function");
    };
    assert!(matches!(
        &function.body.statements[0],
        Node::Expression(simple_parser::ast::Expr::UnsafeBlock(_))
    ));
}

#[test]
fn parse_method_statement_after_trailing_or_condition() {
    parse_ok(
        "class Session:\n    me reload():\n        if is_http() or\n            is_https():\n            return self.begin_reload()\n        self.begin_navigation()\n",
    );
}

// Uses 'elif' not 'else if'
#[test]
fn parse_complex_if_else() {
    parse_ok("if a:\n    x = 1\nelif b:\n    x = 2\nelse:\n    x = 3");
}

#[test]
fn parse_inline_assignment_else_if_chain() {
    parse_ok("if a: reason = \"a\"\nelse if b: reason = \"b\"\nelse if c: reason = \"c\"\nelse: reason = \"d\"");
}

#[test]
fn parse_inline_assignment_elif_then_else() {
    parse_ok("if a: reason = \"a\"\nelif b: reason = \"b\"\nelse: reason = \"c\"");
}

#[test]
fn parse_block_then_inline_elif_and_else_if_chain() {
    parse_ok("if a:\n    reason = \"a\"\nelif b: reason = \"b\"\nelse if c: reason = \"c\"\nelse: reason = \"d\"");
}

#[test]
fn parse_renderdoc_inspector_real_source() {
    parse_ok(include_str!("../../../app/test/renderdoc_replay_inspect.spl"));
}

// While loop
#[test]
fn parse_while_loop() {
    let items = parse("while x < 10:\n    x = x + 1");
    assert!(matches!(&items[0], Node::While(_)));
}

#[test]
fn parse_inline_while_loop() {
    let items = parse("while x < 10: x = x + 1");
    let Node::While(while_stmt) = &items[0] else {
        panic!("Expected While node");
    };

    assert_eq!(while_stmt.body.statements.len(), 1);
    assert!(matches!(&while_stmt.body.statements[0], Node::Assignment(_)));
}

// For loop
#[test]
fn parse_for_loop() {
    let items = parse("for i in range(0, 10):\n    sum = sum + i");
    assert!(matches!(&items[0], Node::For(_)));
}

// Match statement
#[test]
fn parse_match_statement() {
    let items = parse("match x:\n    1 =>\n        y = 1\n    _ =>\n        y = 0");
    assert!(matches!(&items[0], Node::Match(_)));
}

#[test]
fn parse_match_with_guard() {
    parse_ok("match x:\n    n if n > 0 =>\n        y = 1\n    _ =>\n        y = 0");
}

#[test]
fn parse_match_wildcard_rationale() {
    parse_ok("match x:\n    case _(\"remaining values are logged by caller\"):\n        y = 0");
}

// Match patterns use full enum paths or simple identifiers
#[test]
fn parse_match_with_patterns() {
    parse_ok("match opt:\n    Option::Some(x) =>\n        x\n    Option::None =>\n        0");
}

// Loop with break - needs newline after break
#[test]
fn parse_loop_statement() {
    parse_ok("loop:\n    x = x + 1\n    if x > 10:\n        break\n");
}

// Suspension control flow (async-by-default #45)
#[test]
fn parse_if_suspend_statement() {
    let items = parse("if~ x > 0:\n    y = 1");
    if let Node::If(if_stmt) = &items[0] {
        assert!(if_stmt.is_suspend);
    } else {
        panic!("Expected If node");
    }
}

#[test]
fn parse_while_suspend_loop() {
    let items = parse("while~ x < 10:\n    x = x + 1");
    if let Node::While(while_stmt) = &items[0] {
        assert!(while_stmt.is_suspend);
    } else {
        panic!("Expected While node");
    }
}

#[test]
fn parse_for_suspend_loop() {
    let items = parse("for~ i in range(0, 10):\n    sum = sum + i");
    if let Node::For(for_stmt) = &items[0] {
        assert!(for_stmt.is_suspend);
    } else {
        panic!("Expected For node");
    }
}

#[test]
fn parse_suspend_assignment() {
    let items = parse("x ~= async_function()");
    if let Node::Assignment(assign) = &items[0] {
        assert!(matches!(assign.op, simple_parser::ast::AssignOp::SuspendAssign));
    } else {
        panic!("Expected Assignment node");
    }
}

#[test]
fn parse_regular_vs_suspend_if() {
    // Regular if
    let items = parse("if x > 0:\n    y = 1");
    if let Node::If(if_stmt) = &items[0] {
        assert!(!if_stmt.is_suspend);
    } else {
        panic!("Expected If node");
    }

    // Suspension if
    let items = parse("if~ x > 0:\n    y = 1");
    if let Node::If(if_stmt) = &items[0] {
        assert!(if_stmt.is_suspend);
    } else {
        panic!("Expected If node");
    }
}

// ---------------------------------------------------------------------------
// Comma as a MATCH-ARM SEPARATOR (bug: match_arm_comma_separator_rejected,
// doc/08_tracking/bug/match_arm_comma_separator_rejected_2026-08-02.md).
//
// Before the fix every one of the `arm_separator` tests below failed with
// "expected pattern, found Comma" — the arms loop re-entered the arm parser on
// the comma itself. That made std `tooling/base64_utils.spl` and
// `tooling/url_utils.spl` unloadable in their entirety, so every spec and
// census importing them silently saw nothing.
//
// The `multi_pattern` tests pin the OTHER role of comma (before the arm's
// `:`/`=>`), which must keep working: the two roles are distinguished purely by
// position and must not be conflated.
// ---------------------------------------------------------------------------

#[test]
fn parse_match_arm_separator_comma_same_line() {
    let items = parse("match ch:\n    \"A\" => 65, \"B\" => 66, \"C\" => 67\n    _ => 0");
    match &items[0] {
        Node::Match(m) => assert_eq!(m.arms.len(), 4),
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn parse_match_arm_separator_trailing_comma_per_line() {
    let items = parse("match n:\n    0 => 10,\n    1 => 20,\n    _ => 0,");
    match &items[0] {
        Node::Match(m) => assert_eq!(m.arms.len(), 3),
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn parse_match_arm_separator_comma_wraps_across_lines() {
    let items = parse("match n:\n    0 => 10, 1 => 20\n    2 => 30, _ => 0");
    match &items[0] {
        Node::Match(m) => assert_eq!(m.arms.len(), 4),
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn parse_match_arm_separator_comma_colon_arms() {
    let items = parse("match n:\n    0: y = 10, 1: y = 20\n    _: y = 0");
    match &items[0] {
        Node::Match(m) => assert_eq!(m.arms.len(), 3),
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn parse_match_arm_separator_comma_case_arms() {
    let items = parse("match n:\n    case 0 => 10,\n    case 1 => 20,\n    case _ => 0");
    match &items[0] {
        Node::Match(m) => assert_eq!(m.arms.len(), 3),
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn parse_match_arm_separator_comma_in_expression_position() {
    // `match` as a VALUE goes through parse_match_expr, a second arms loop.
    parse_ok("fn f(n: i64) -> i64:\n    val r = match n:\n        0 => 10, 1 => 20, _ => 0\n    return r");
}

#[test]
fn parse_match_multi_pattern_comma_still_binds_to_one_arm() {
    // Comma BEFORE the arm separator stays a multi-pattern separator: three
    // patterns, one shared body — not three arms plus a stray body.
    let items = parse("match n:\n    case 1, 2, 3:\n        y = 100\n    case _:\n        y = 0");
    match &items[0] {
        Node::Match(m) => assert_eq!(m.arms.len(), 2),
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn parse_match_multi_pattern_comma_caseless_still_binds_to_one_arm() {
    let items = parse("match n:\n    1, 2, 3 => 100\n    _ => 0");
    match &items[0] {
        Node::Match(m) => assert_eq!(m.arms.len(), 2),
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn parse_match_multi_pattern_pipe_still_binds_to_one_arm() {
    let items = parse("match n:\n    case 1 | 2 | 3:\n        y = 100\n    case _:\n        y = 0");
    match &items[0] {
        Node::Match(m) => assert_eq!(m.arms.len(), 2),
        other => panic!("expected Match, got {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// `=>` with an INDENTED BLOCK body.
//
// `:` and `=>` are interchangeable arm separators (parse_match_arm accepts
// `->`, `=>` and `:` alike), so the body grammar reachable through one must be
// reachable through the other. A multi-statement indented block after `:` has
// always worked; after `=>` it did not, which made std
// `tooling/url_utils.spl` unloadable on the seed path even after the arm
// separator comma fix. bug doc:
// doc/08_tracking/bug/match_arm_comma_separator_rejected_2026-08-02.md
// ---------------------------------------------------------------------------

/// Count TsArrowFunction hints reported while parsing `src`.
///
/// Deliberately tolerant of a failed parse: hints are collected token-by-token
/// during `advance`, and a genuine TypeScript arrow function does NOT parse as
/// Simple at all (`val add = (a, b) => a + b` is an `UnexpectedToken` on the
/// `=>`). Requiring a successful parse here would make the "still reported"
/// control below untestable.
fn ts_arrow_hint_count(src: &str) -> usize {
    let mut parser = Parser::new(src);
    let _ = parser.parse();
    parser
        .error_hints()
        .iter()
        .filter(|h| h.help.as_deref().is_some_and(|m| m.contains("'=>' is for lambdas")))
        .count()
}

#[test]
fn match_arm_with_call_shaped_pattern_is_not_a_ts_arrow_function() {
    // `Some(code) =>` ends in `)`, which is exactly the lexical shape the
    // TsArrowFunction heuristic keys on — but it is a match-arm separator,
    // core Simple grammar. std tooling/url_utils.spl emitted 160 lines of
    // these hints for a file that parses perfectly.
    let src = "match from_hex(hex):\n    Some(code) =>\n        r = code\n    None =>\n        r = 0";
    parse_ok(src); // the source really is valid, so a 0 count is not vacuous
    assert_eq!(ts_arrow_hint_count(src), 0);
}

#[test]
fn match_arm_with_tuple_shaped_pattern_is_not_a_ts_arrow_function() {
    let src = "match p:\n    (a, b) => r = a\n    _ => r = 0";
    parse_ok(src);
    assert_eq!(ts_arrow_hint_count(src), 0);
}

#[test]
fn ts_arrow_detection_rule_itself_is_untouched() {
    // The two tests above suppress the hint CONTEXTUALLY (only inside a match
    // arm list); they must not have removed the underlying rule. The detector
    // is asserted directly — `) =>` still classifies as TsArrowFunction — so a
    // future change that guts the rule instead of scoping it fails here rather
    // than silently passing the suppression tests.
    // See also tests/error_recovery_test.rs::test_typescript_arrow_function_detection.
    use simple_parser::error_recovery::{detect_common_mistake, CommonMistake};
    use simple_parser::token::{Span, Token, TokenKind};

    let fat_arrow = Token::new(TokenKind::FatArrow, Span::new(8, 10, 1, 9), "=>".to_string());
    let rparen = Token::new(TokenKind::RParen, Span::new(7, 8, 1, 8), ")".to_string());
    assert_eq!(
        detect_common_mistake(&fat_arrow, &rparen, None),
        Some(CommonMistake::TsArrowFunction)
    );
}

#[test]
fn parse_match_arm_fat_arrow_indented_block_body_stmt_position() {
    let items = parse("match n:\n    1 =>\n        r = 10\n        r = r + 1\n    _ =>\n        r = 0");
    match &items[0] {
        Node::Match(m) => {
            assert_eq!(m.arms.len(), 2);
            assert_eq!(m.arms[0].body.statements.len(), 2);
        }
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn parse_match_arm_fat_arrow_indented_block_body_expr_position() {
    // `match` as a VALUE goes through parse_match_expr/parse_match_arm_expr,
    // a second arm parser that must agree with the statement one.
    parse_ok("fn g(n: i64) -> i64:\n    val r = match n:\n        1 =>\n            val a = 10\n            a\n        _ =>\n            0\n    return r");
}

#[test]
fn parse_match_arm_colon_indented_block_body_stmt_position() {
    // Control: the `:` spelling of the SAME shape. If this ever regresses the
    // two tests above are measuring the wrong thing.
    let items = parse("match n:\n    1:\n        r = 10\n        r = r + 1\n    _:\n        r = 0");
    match &items[0] {
        Node::Match(m) => {
            assert_eq!(m.arms.len(), 2);
            assert_eq!(m.arms[0].body.statements.len(), 2);
        }
        other => panic!("expected Match, got {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// An inline `match` used as a VALUE is terminated by the ENCLOSING list.
//
// Two-parser divergence: the self-hosted parser accepted these shapes (fix
// 8fdc21c67b5, `ends_enclosing_list` in parse_match_arms_common) while the
// seed rejected them, which made
// test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl
// unparseable on the seed path — i.e. invisible to every seed-run gate.
// The arm-boundary `,` belongs to the enclosing list when the match is lexed
// at bracket depth > 0; a `)`/`]`/`}` in pattern position always ends the arm
// list. bug doc:
// doc/08_tracking/bug/match_arm_comma_separator_rejected_2026-08-02.md
// ---------------------------------------------------------------------------

#[test]
fn parse_inline_match_struct_field_terminated_by_comma() {
    parse_ok(
        "fn f(x: i64) -> text:\n    val v = Box(\n        a: match x:\n            1: \"one\"\n            _: \"other\",\n        b: x\n    )\n    return v.a",
    );
}

#[test]
fn parse_inline_match_struct_field_terminated_by_rparen() {
    parse_ok(
        "fn f(x: i64) -> text:\n    val v = Box(\n        b: x,\n        a: match x:\n            1: \"one\"\n            _: \"other\"\n    )\n    return v.a",
    );
}

#[test]
fn parse_inline_match_call_arg_terminated_by_comma() {
    parse_ok(
        "fn f(x: i64) -> text:\n    return take_two(match x:\n        1: \"one\"\n        _: \"other\",\n        x)",
    );
}

#[test]
fn parse_inline_match_last_call_arg_terminated_by_rparen() {
    // The `)` shares the last arm's line, so no Dedent has been flushed.
    parse_ok(
        "fn f(x: i64) -> text:\n    return take_flipped(x, match x:\n        1: \"one\"\n        _: \"other\")",
    );
}

#[test]
fn parse_inline_match_array_element_terminated_by_comma() {
    parse_ok(
        "fn f(x: i64) -> text:\n    val items = [match x:\n        1: \"one\"\n        _: \"other\",\n        \"tail\"]\n    return items[0]",
    );
}

#[test]
fn parse_statement_match_trailing_comma_still_separates_arms() {
    // Guard for the depth gate: at statement level (bracket_depth == 0) the
    // arm-boundary comma must STILL be consumed as an arm separator. If the
    // gate ever over-fires, this drops back to one arm.
    let items = parse("match n:\n    0 => 10,\n    1 => 20,\n    _ => 0,");
    match &items[0] {
        Node::Match(m) => assert_eq!(m.arms.len(), 3),
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn parse_match_arm_fat_arrow_indented_block_body_url_utils_shape() {
    // The exact shape from std tooling/url_utils.spl url_decode/from_hex: a
    // caseless `Some(x) =>` arm whose body is an indented multi-statement
    // block, nested inside another block.
    parse_ok(
        "fn f(hex: text) -> i64:\n    match from_hex(hex):\n        Some(code) =>\n            r = r + code\n            i = i + 3\n        None =>\n            r = r + 1\n    return r",
    );
}
