use simple_compiler::{hir, interpreter::evaluate_module};
use simple_parser::Parser;

const ENUM_DECLARATION: &str = r#"
enum Arity:
    Four(first: i64, second: i64, third: i64, fourth: i64)
"#;

fn evaluate(source: &str) -> Result<i32, String> {
    let ast = Parser::new(source).parse().map_err(|error| error.to_string())?;
    evaluate_module(&ast.items).map_err(|error| error.to_string())
}

fn lower(source: &str) -> Result<hir::HirModule, String> {
    let ast = Parser::new(source).parse().map_err(|error| error.to_string())?;
    hir::lower(&ast).map_err(|error| error.to_string())
}

fn interpreter_construction(arguments: &str) -> String {
    format!(
        r#"{ENUM_DECLARATION}
fn main() -> i64:
    val value = Arity.Four({arguments})
    match value:
        case Arity.Four(a, b, c, d): return a + b + c + d
        case _: return 0
"#
    )
}

fn hir_construction(arguments: &str) -> String {
    format!(
        r#"{ENUM_DECLARATION}
fn construct() -> Arity:
    Arity.Four({arguments})
main = 0
"#
    )
}

fn assert_arity_error(error: String, expected: usize, actual: usize) {
    assert!(error.contains("payload arity mismatch"), "unexpected error: {error}");
    assert!(
        error.contains(&format!("expected {expected}, got {actual}")),
        "error must report declared and actual payload counts: {error}"
    );
}

#[test]
fn interpreter_constructs_declared_enum_variant_arity() {
    assert_eq!(evaluate(&interpreter_construction("1, 2, 3, 4")), Ok(10));
}

#[test]
fn interpreter_rejects_extra_enum_variant_payload() {
    let error = evaluate(&interpreter_construction("1, 2, 3, 4, 5")).expect_err("five payloads must be rejected");
    assert_arity_error(error, 4, 5);
}

#[test]
fn interpreter_rejects_missing_enum_variant_payload() {
    let error = evaluate(&interpreter_construction("1, 2, 3")).expect_err("three payloads must be rejected");
    assert_arity_error(error, 4, 3);
}

#[test]
fn interpreter_rejects_builtin_enum_variant_extra_payloads() {
    for (constructor, expected, actual) in [
        ("Option.Some(1, 2)", 1, 2),
        ("Option.None(1)", 0, 1),
        ("Result.Ok(1, 2)", 1, 2),
        ("Result.Err(1, 2)", 1, 2),
    ] {
        let source = format!("fn main() -> i64:\n    val value = {constructor}\n    return 0\n");
        let error = evaluate(&source).expect_err("extra built-in enum payloads must be rejected");
        assert_arity_error(error, expected, actual);
    }
}

#[test]
fn interpreter_constructs_builtin_enum_variants_with_declared_arity() {
    let source = r#"
fn main() -> i64:
    val some = Option.Some(7)
    val none = Option.None()
    val ok = Result.Ok(9)
    val err = Result.Err(11)
    if some.is_some() and none.is_none() and ok.is_ok() and err.is_err():
        if some.unwrap() == 7 and ok.unwrap() == 9 and err.unwrap_err() == 11:
            return 0
    return 1
"#;
    assert_eq!(evaluate(source), Ok(0));
}

#[test]
fn hir_constructs_declared_enum_variant_arity() {
    lower(&hir_construction("1, 2, 3, 4")).expect("four payloads must lower");
}

#[test]
fn hir_rejects_extra_enum_variant_payload() {
    let error = lower(&hir_construction("1, 2, 3, 4, 5")).expect_err("five payloads must be rejected");
    assert_arity_error(error, 4, 5);
}

#[test]
fn hir_rejects_missing_enum_variant_payload() {
    let error = lower(&hir_construction("1, 2, 3")).expect_err("three payloads must be rejected");
    assert_arity_error(error, 4, 3);
}

#[test]
fn hir_rejects_original_method_call_extra_payload() {
    let source = r#"
enum HirExprKind:
    MethodCall(receiver: Any, method: text, args: [Any], resolution: Any)
fn construct() -> HirExprKind:
    HirExprKind.MethodCall(1, "m", [], 0, 99)
main = 0
"#;
    let error = lower(source).expect_err("original five-payload MethodCall must be rejected");
    assert_arity_error(error, 4, 5);
}
