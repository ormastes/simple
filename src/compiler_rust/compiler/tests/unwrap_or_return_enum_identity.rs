//! `?? return` must distinguish Result/Option by runtime enum identity.
//! Variant names alone are insufficient because user enums may also define
//! `Ok` and `Err`; the interpreter preserves those values as opaque enums.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

const SOURCE: &str = r#"
enum UserOutcome:
    Ok(i64)
    Err(i64)

fn keep_user(value: Any) -> i64:
    val kept = value ?? return -100
    match kept:
        case UserOutcome.Ok(payload): return payload + 10
        case UserOutcome.Err(payload): return payload + 20
        case _: return -200

fn maybe(present: bool) -> i64?:
    if present:
        return 7
    nil

fn keep_option(present: bool) -> i64:
    val kept = maybe(present) ?? return -3
    return kept

fn result_value(success: bool) -> Result<i64, i64>:
    if success:
        return Ok(9)
    Err(4)

fn keep_result(success: bool) -> i64:
    val kept = result_value(success) ?? return -4
    return kept

fn main() -> i64:
    if keep_user(UserOutcome.Ok(3)) != 13: return 1
    if keep_user(UserOutcome.Err(4)) != 24: return 2
    if keep_option(true) != 7: return 3
    if keep_option(false) != -3: return 4
    if keep_result(true) != 9: return 5
    if keep_result(false) != -4: return 6
    return 0
"#;

fn run_interpreter() -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{SOURCE}\nmain = main()\n");
    let module = Parser::new(&source)
        .parse()
        .expect("parity source must parse for interpreter");
    interpreter::evaluate_module(&module.items).expect("parity source must run in interpreter")
}

fn run_jit() -> i64 {
    let ast = Parser::new(SOURCE).parse().expect("parity source must parse for JIT");
    let hir_module = hir::lower(&ast).expect("parity source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("parity source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("parity MIR must compile");
    unsafe { jit.call_i64_void("main").expect("parity main must execute") }
}

#[test]
fn user_ok_err_and_typed_option_result_match_interpreter_and_native_jit() {
    let interpreted = run_interpreter();
    let native = run_jit();
    assert_eq!(interpreted, 0, "interpreter control failed at case {interpreted}");
    assert_eq!(
        native, interpreted as i64,
        "native/interpreter parity diverged at case {native}"
    );
}
