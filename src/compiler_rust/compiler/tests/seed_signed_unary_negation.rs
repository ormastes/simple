//! Bootstrap seed interpreter: unary minus retains a signed operand's width.
use simple_parser::Parser;

fn evaluate(source: &str) -> i32 {
    let module = Parser::new(source).parse().expect("valid source");
    simple_compiler::interpreter::evaluate_module(&module.items).expect("successful evaluation")
}

#[test]
fn signed_minima_negate_at_their_declared_width() {
    for (ty, minimum) in [("i8", -128_i64), ("i16", -32768), ("i32", -2147483648)] {
        let source = format!(
            "fn probe() -> i64:\n    val x: {ty} = {minimum}\n    if -x != {minimum}: return 1\n    if -(-x) != {minimum}: return 2\n    val ordinary: {ty} = 7\n    if -ordinary != -7: return 3\n    0\nmain = probe()\n"
        );
        assert_eq!(evaluate(&source), 0, "{ty} unary negation");
    }
}

#[test]
fn parameters_casts_and_inferred_bindings_keep_narrow_width() {
    assert_eq!(
        evaluate(
            r#"
fn negate(x: i32) -> i64:
    -x
fn probe() -> i64:
    if negate(-2147483648) != -2147483648: return 1
    val source: i64 = -2147483648
    if -(source as i32) != -2147483648: return 2
    val inferred = source as i32
    if -inferred != -2147483648: return 3
    val derived = inferred + 0
    if -derived != -2147483648: return 4
    0
main = probe()
"#
        ),
        0
    );
}

#[test]
fn wide_integer_float_and_unsigned_negation_keep_existing_semantics() {
    assert_eq!(
        evaluate(
            r#"
fn probe() -> i64:
    val wide: i64 = -2147483648
    if -wide != 2147483648: return 1
    val untyped = -2147483648
    if -untyped != 2147483648: return 2
    val minimum: i64 = -9223372036854775808
    if -minimum != minimum: return 3
    val float_value: f64 = 1.5
    if -float_value != -1.5: return 4
    val unsigned_value: u8 = 1
    if -unsigned_value != 255u8: return 5
    0
main = probe()
"#
        ),
        0
    );
}

fn jit_evaluate(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("valid source");
    let hir = simple_compiler::hir::lower(&ast).expect("HIR lowering");
    let mir = simple_compiler::mir::lower_to_mir(&hir).expect("MIR lowering");
    let mut jit = simple_compiler::codegen::JitCompiler::new_static().expect("static JIT");
    jit.compile_module(&mir).expect("JIT compilation");
    unsafe { jit.call_i64_void("main").expect("JIT execution") }
}

#[test]
fn jit_signed_minima_negate_at_their_declared_width() {
    for (ty, minimum) in [("i8", -128_i64), ("i16", -32768), ("i32", -2147483648)] {
        let source = format!(
            "fn main() -> i64:\n    val x: {ty} = {minimum}\n    if -x != {minimum}: return 1\n    if -(-x) != {minimum}: return 2\n    val ordinary: {ty} = 7\n    if -ordinary != -7: return 3\n    0\n"
        );
        assert_eq!(jit_evaluate(&source), 0, "{ty} JIT unary negation");
    }
}

#[test]
fn jit_parameters_casts_and_wide_controls() {
    assert_eq!(
        jit_evaluate(
            r#"
fn negate(x: i32) -> i64:
    -x
fn main() -> i64:
    if negate(-2147483648) != -2147483648: return 1
    val source: i64 = -2147483648
    if -(source as i32) != -2147483648: return 2
    if -source != 2147483648: return 3
    val ordinary: i64 = 7
    if -ordinary != -7: return 4
    val float_value: f64 = 1.5
    if -float_value != -1.5: return 5
    0
"#
        ),
        0
    );
}

#[test]
fn jit_direct_parameter_return_preserves_signed_value() {
    for (ty, minimum) in [("i8", -128_i64), ("i16", -32768), ("i32", -2147483648)] {
        let source = format!("fn negate(x: {ty}) -> i64:\n    -x\n");
        let ast = Parser::new(&source).parse().expect("valid source");
        let hir = simple_compiler::hir::lower(&ast).expect("HIR lowering");
        let mir = simple_compiler::mir::lower_to_mir(&hir).expect("MIR lowering");
        let mut jit = simple_compiler::codegen::JitCompiler::new_static().expect("static JIT");
        jit.compile_module(&mir).expect("JIT compilation");
        for (input, expected) in [(minimum, minimum), (7, -7), (-7, 7), (0, 0)] {
            assert_eq!(
                unsafe { jit.call_i64_i64("negate", input).expect("JIT execution") },
                expected,
                "{ty}: -{input}"
            );
        }
    }
}
