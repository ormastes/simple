//! seed_jit_hoisted_loop_data_ptr_reaches_generic_array_get_2026-11-27: the
//! bound-proved loop (`val n = d.len(); var i: u64 = 0; while i < n`) hoists
//! the array's data pointer for every element type, and element types without
//! a typed reader fell back to `rt_array_get` / `rt_array_get_text` with that
//! raw pointer as the array handle: `[f64]` 7.5 read as 0.0, `[i32]` 7 as 3,
//! `[text]` "ab" as "".
use simple_parser::Parser;

fn jit_evaluate(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("valid source");
    let mut lowerer = simple_compiler::hir::Lowerer::new();
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let hir = lowerer.lower_module(&ast).expect("HIR lowering");
    let mir = simple_compiler::mir::lower_to_mir(&hir).expect("MIR lowering");
    let mut jit = simple_compiler::codegen::JitCompiler::new_static().expect("static JIT");
    jit.compile_module(&mir).expect("JIT compilation");
    unsafe { jit.call_i64_void("main").expect("JIT execution") }
}

/// (element type, init of `s`, loop body term, result expression, values, want)
const CASES: &[(&str, &str, &str, &str, &str, i64)] = &[
    ("f64", "0.0", "d[i]", "(s * 100.0) as i64", "7.5, 2.25", 975),
    ("i32", "0", "d[i] as i64", "s", "7i32, 40i32", 47),
    ("i16", "0", "d[i] as i64", "s", "7i16, 40i16", 47),
    ("text", "0", "d[i].len()", "s", "\"ab\", \"xyz\"", 5),
];

#[test]
fn jit_hoisted_loop_reads_non_word_elements_from_parameter() {
    for (ty, init, term, result, values, want) in CASES {
        let source = format!(
            "fn total(d: [{ty}]) -> i64:\n    var s = {init}\n    val n = d.len()\n    var i: u64 = 0\n    while i < n:\n        s = s + {term}\n        i = i + 1\n    {result}\nfn main() -> i64:\n    val a: [{ty}] = [{values}]\n    total(a)\n"
        );
        assert_eq!(jit_evaluate(&source), *want, "hoisted [{ty}] parameter loop");
    }
}

#[test]
fn jit_hoisted_loop_reads_non_word_elements_from_local() {
    for (ty, init, term, result, values, want) in CASES {
        let source = format!(
            "fn main() -> i64:\n    val d: [{ty}] = [{values}]\n    var s = {init}\n    val n = d.len()\n    var i: u64 = 0\n    while i < n:\n        s = s + {term}\n        i = i + 1\n    {result}\n"
        );
        assert_eq!(jit_evaluate(&source), *want, "hoisted [{ty}] local loop");
    }
}
