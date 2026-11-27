//! Pin: seed semantic errors carry file:line:col (bug row:
//! seed_semantic_error_missing_position_2026-11-09).
//!
//! Before the fix the seed reported `error: semantic: <message>` with no
//! source position, while the self-hosted compiler reports
//! `<file>:<line>:<col>: error: semantic: <message>`. The interpreter now
//! records the enclosing statement's span at each execution-loop head and
//! the `semantic_with_context` factory adopts it (plus the current file)
//! when the raise site recorded no position; `Display` renders
//! `semantic: <file>:<line>:<col>: <message>`.

use simple_compiler::interpreter::{evaluate_module, set_current_file};
use simple_parser::Parser;

#[test]
fn semantic_error_from_undefined_variable_carries_file_line_col() {
    let source = "fn main():\n    val x = nope_undefined\n    print(x)\n";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    set_current_file(Some(std::path::PathBuf::from("/tmp/sem_err_probe.spl")));
    let err = evaluate_module(&module.items).expect_err("undefined variable must be a semantic error");
    set_current_file(None);

    let rendered = format!("{}", err);
    assert!(
        rendered.contains("semantic:"),
        "error must keep its semantic kind: '{}'",
        rendered
    );
    assert!(
        rendered.contains("variable `nope_undefined` not found"),
        "error must keep its message: '{}'",
        rendered
    );
    assert!(
        rendered.contains("/tmp/sem_err_probe.spl:2:"),
        "semantic error must carry file:line:col of the offending statement: '{}'",
        rendered
    );
}

#[test]
fn semantic_error_inside_function_body_carries_file_line_col() {
    // Statement-position granularity: the raise happens deep inside
    // expression evaluation, but the position must still be the enclosing
    // (return) statement, not absent.
    let source = "fn helper() -> i64:\n    return missing_name + 1\n\nfn main():\n    print(helper())\n";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    set_current_file(Some(std::path::PathBuf::from("/tmp/sem_err_body.spl")));
    let err = evaluate_module(&module.items).expect_err("undefined variable must be a semantic error");
    set_current_file(None);

    let rendered = format!("{}", err);
    assert!(
        rendered.contains("/tmp/sem_err_body.spl:2:"),
        "semantic error inside a function body must carry file:line:col: '{}'",
        rendered
    );
}
