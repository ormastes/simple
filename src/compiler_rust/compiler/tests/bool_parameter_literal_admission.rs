//! A literal non-`bool` argument at a `bool`-typed parameter is rejected on
//! both lanes (interpreter and HIR->MIR->JIT), including a unary-wrapped
//! numeric literal such as `~0` or `-1`.
//! Bug: doc/08_tracking/bug/bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04

use simple_compiler::{hir, interpreter};
use simple_parser::Parser;

fn source(arg: &str) -> String {
    format!("fn takes_bool(value: bool) -> bool:\n    value\n\nfn main() -> i64:\n    if takes_bool({arg}): return 1\n    return 0\n")
}

fn interpreter_error(arg: &str) -> Option<String> {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let src = format!("{}\nmain = main()\n", source(arg));
    let module = Parser::new(&src).parse().expect("source must parse");
    interpreter::evaluate_module(&module.items).err().map(|e| format!("{e:?}"))
}

fn hir_error(arg: &str) -> Option<String> {
    let src = source(arg);
    let ast = Parser::new(&src).parse().expect("source must parse");
    hir::lower(&ast).err().map(|e| format!("{e:?}"))
}

fn assert_rejected(err: Option<String>, lane: &str, arg: &str) {
    let err = err.unwrap_or_else(|| panic!("{lane}: takes_bool({arg}) must be rejected"));
    assert!(err.contains("declared 'bool'"), "{lane}: wrong error for takes_bool({arg}): {err}");
}

#[test]
fn interpreter_rejects_integer_literal_at_bool_param() {
    assert_rejected(interpreter_error("0"), "interpreter", "0");
}

#[test]
fn interpreter_rejects_bitnot_literal_at_bool_param() {
    assert_rejected(interpreter_error("~0"), "interpreter", "~0");
}

#[test]
fn jit_lowering_rejects_integer_literal_at_bool_param() {
    assert_rejected(hir_error("0"), "jit", "0");
}

#[test]
fn jit_lowering_rejects_bitnot_literal_at_bool_param() {
    assert_rejected(hir_error("~0"), "jit", "~0");
}
