//! `fn f(x: mut i64)` called with a plain caller variable propagates the
//! callee's reassignment back to the caller (seed interpreter half).
//! Bug: doc/08_tracking/bug/mut_param_annotation_no_reference_propagation_2026-07-20

use simple_compiler::interpreter;
use simple_parser::Parser;

fn run(src: &str) -> i64 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module = Parser::new(src).parse().expect("source must parse");
    interpreter::evaluate_module(&module.items).expect("must run") as i64
}

#[test]
fn mut_i64_param_propagates_to_caller_variable() {
    let src = "fn modify(x: mut i64):\n    x = x + 1\n\nfn main() -> i64:\n    var n = 41\n    modify(n)\n    return n\n\nmain = main()\n";
    assert_eq!(run(src), 42);
}

#[test]
fn mut_bool_param_propagates_to_caller_variable() {
    let src = "fn flip(b: mut bool):\n    b = not b\n\nfn main() -> i64:\n    var f = false\n    flip(f)\n    if f: return 1\n    return 0\n\nmain = main()\n";
    assert_eq!(run(src), 1);
}

#[test]
fn plain_i64_param_stays_by_value() {
    let src = "fn modify(x: i64):\n    var y = x\n    y = y + 1\n\nfn main() -> i64:\n    var n = 41\n    modify(n)\n    return n\n\nmain = main()\n";
    assert_eq!(run(src), 41);
}
