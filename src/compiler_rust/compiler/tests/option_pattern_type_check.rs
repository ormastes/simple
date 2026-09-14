use simple_compiler::hir;
use simple_parser::Parser;

fn lower_error(source: &str) -> String {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("regression source must parse");
    hir::lower(&ast)
        .expect_err("Option/Result pattern on a definite non-optional primitive must be rejected")
        .to_string()
}

#[test]
fn statement_option_pattern_rejects_plain_i64_scrutinee() {
    let error = lower_error(
        r#"
fn invalid(n: i64) -> i64:
    match n:
        case Some(value): return value
        case None: return 0
"#,
    );

    assert!(error.contains("Some(...)` pattern"), "unexpected diagnostic: {error}");
    assert!(error.contains("statically typed `int`"), "unexpected diagnostic: {error}");
}

#[test]
fn expression_result_pattern_rejects_plain_text_scrutinee() {
    let error = lower_error(
        r#"
fn invalid(s: text) -> i64:
    val value = match s:
        case Ok(_): 1
        case Err(_): 0
    value
"#,
    );

    assert!(error.contains("Ok(...)` pattern"), "unexpected diagnostic: {error}");
    assert!(error.contains("statically typed `text`"), "unexpected diagnostic: {error}");
}
