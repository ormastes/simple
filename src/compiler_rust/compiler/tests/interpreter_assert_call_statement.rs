//! Interpreter parity for the callable assertion spelling `assert(COND[, MSG])`.
//!
//! The lexer deliberately lexes `assert(` as an identifier call so a user
//! `fn assert` stays callable (test/fixtures/compiler/native_callable_assert_shadow.spl).
//! The pure-Simple front end desugars both `assert COND[, MSG]` and
//! `assert(COND[, MSG])` to the `__assert` builtin
//! (src/compiler/10.frontend/core/parser_stmts.spl); the seed's HIR lowering
//! already special-cased the 1-arg call, but the tree-walking interpreter had
//! no owner at all and died with `function \`assert\` not found` (E1002) --
//! which is what every bare `assert(...)` in a spec hit under `simple test`.
use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

fn run_program(main: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).unwrap();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    result.map_err(|e| format!("{e:?}"))
}

#[test]
fn passing_assert_call_is_a_no_op() {
    let src = "fn main() -> i64:\n    assert(1 == 1)\n    assert(2 == 2, \"with message\")\n    return 7\n";
    assert_eq!(run_program(src), Ok(7));
}

#[test]
fn failing_assert_call_raises_assertion_failed() {
    let src = "fn main() -> i64:\n    assert(1 == 2)\n    return 7\n";
    let err = run_program(src).expect_err("a false assert(...) must fail the program");
    assert!(err.contains("assertion failed: condition evaluated to false"), "{err}");
    assert!(err.contains("E3004"), "must carry the ASSERTION_FAILED code: {err}");
    assert!(!err.contains("not found"), "must not be reported as an unknown function: {err}");
}

#[test]
fn failing_assert_call_message_is_any_expression_evaluated_on_failure() {
    // The message is an arbitrary expression (string concatenation here), and
    // it is evaluated only when the condition is false.
    let src = "fn main() -> i64:\n    val who = \"disk\"\n    assert(1 == 2, \"no \" + who)\n    return 7\n";
    let err = run_program(src).expect_err("a false assert(...) must fail the program");
    assert!(err.contains("assertion failed: condition evaluated to false (no disk)"), "{err}");

    // Passing: the message expression must NOT be evaluated (it would panic
    // via division by zero if it were... use an undefined name instead, which
    // the interpreter reports as an error only when evaluated).
    let src = "fn main() -> i64:\n    assert(1 == 1, not_defined_anywhere)\n    return 7\n";
    assert_eq!(run_program(src), Ok(7));
}

#[test]
fn keyword_and_call_spellings_fail_identically() {
    let keyword = run_program("fn main() -> i64:\n    assert 1 == 2, \"same\"\n    return 7\n").unwrap_err();
    let call = run_program("fn main() -> i64:\n    assert(1 == 2, \"same\")\n    return 7\n").unwrap_err();
    assert_eq!(keyword, call, "both spellings must raise one identical error");
}

#[test]
fn user_defined_fn_assert_still_wins() {
    // Same contract as the native fixture: a declared `fn assert` accepts a
    // false value without the builtin check.
    let src = "var calls: i64 = 0\nfn assert(value: bool):\n    calls = calls + 1\nfn main() -> i64:\n    assert(false)\n    return calls\n";
    assert_eq!(run_program(src), Ok(1));
}

#[test]
fn assert_call_arity_is_checked() {
    let err = run_program("fn main() -> i64:\n    assert(1 == 1, \"a\", \"b\")\n    return 7\n").unwrap_err();
    assert!(err.contains("assert requires a condition and at most one message"), "{err}");
}
