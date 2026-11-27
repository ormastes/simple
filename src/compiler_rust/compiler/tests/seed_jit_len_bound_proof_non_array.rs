//! The loop bound proof (`val n = x.len(); var i: u64 = 0; while i < n`)
//! accepted any `.len()` receiver, so a tuple or text local got a loop
//! preheader calling `rt_array_data_ptr` on a non-array, and the tuple arm of
//! `lower_index_expr` read through that pointer. Separately, the JIT lowered a
//! tuple `.len()` to the undefined `Tuple.len`, which returned -1: the u64
//! loop above then never ended.
use simple_parser::Parser;

fn lower(source: &str) -> simple_compiler::mir::MirModule {
    let ast = Parser::new(source).parse().expect("valid source");
    let mut lowerer = simple_compiler::hir::Lowerer::new();
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let hir = lowerer.lower_module(&ast).expect("HIR lowering");
    simple_compiler::mir::lower_to_mir(&hir).expect("MIR lowering")
}

fn jit_evaluate(source: &str) -> i64 {
    let mir = lower(source);
    let mut jit = simple_compiler::codegen::JitCompiler::new_static().expect("static JIT");
    jit.compile_module(&mir).expect("JIT compilation");
    unsafe { jit.call_i64_void("main").expect("JIT execution") }
}

const TUPLE_LOOP: &str = "fn main() -> i64:\n    val t = (7, 40, 3)\n    var s = 0\n    val n = t.len()\n    var i: u64 = 0\n    while i < n:\n        s = s * 100 + t[i]\n        i = i + 1\n    s\n";

const TEXT_LOOP: &str = "fn main() -> i64:\n    val t = \"abc\"\n    var s = 0\n    val n = t.len()\n    var i: u64 = 0\n    while i < n:\n        s = s + 1\n        if t[i] == \"b\":\n            s = s + 10\n        i = i + 1\n    s\n";

#[test]
fn jit_tuple_len_is_the_arity() {
    assert_eq!(
        jit_evaluate("fn main() -> i64:\n    val t = (7, 40, 3)\n    t.len()\n"),
        3
    );
}

#[test]
fn jit_bound_loop_over_tuple_and_text_locals() {
    assert_eq!(jit_evaluate(TUPLE_LOOP), 74003, "tuple loop");
    assert_eq!(jit_evaluate(TEXT_LOOP), 13, "text loop");
}

#[test]
fn bound_proof_hoists_no_array_pointer_for_non_arrays() {
    for (name, source) in [("tuple", TUPLE_LOOP), ("text", TEXT_LOOP)] {
        let mir = format!("{:?}", lower(source));
        assert!(
            !mir.contains("rt_array_data_ptr"),
            "{name}: preheader hoisted an array pointer"
        );
    }
}

/// The untyped `Tuple.len` result sat in an `any` slot undecoded, so an i64
/// counter compared against it ran zero times.
#[test]
fn jit_tuple_len_bounds_an_i64_counter() {
    let source = "fn main() -> i64:\n    val t = (7, 40, 3)\n    val n = t.len()\n    var c = 0\n    var i = 0\n    while i < n:\n        c = c + t[i]\n        i = i + 1\n    c\n";
    assert_eq!(jit_evaluate(source), 50);
}
