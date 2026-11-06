//! `d[k] ?? default` on a Dict with a scalar value type must coalesce a miss
//! to the default on the JIT, exactly like `d.get(k) ?? default`. The index
//! was typed as the bare value type, so `??` was lowered as the identity and
//! the nil sentinel leaked as the integer 3.
//! Bugs: seed_dict_int_index_nil_coalesce_2026-10-31,
//! seed_dict_miss_coalesce_increment_2026-10-10

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn int_key_int_value_miss_coalesces_to_default() {
    let src = r#"fn main() -> i64:
    var d: Dict<i64, i64> = {}
    d[5] = 5
    val a = d[9] ?? -1
    if a != -1: return 1
    val b = d.get(9) ?? -1
    if b != -1: return 2
    val c = d[5] ?? -1
    if c != 5: return 3
    return 0
"#;
    assert_eq!(run(src), 0);
}

#[test]
fn text_key_int_value_miss_coalesces_and_counts() {
    let src = r#"fn main() -> i64:
    var counts: Dict<text, i64> = {}
    val prev = counts["a"] ?? 0
    if prev != 0: return 1
    counts["a"] = (counts["a"] ?? 0) + 1
    counts["a"] = (counts["a"] ?? 0) + 1
    val got: i64 = counts["a"]
    if got != 2: return 2
    var f: Dict<text, i64> = {}
    f["k"] = 4
    if (f["z"] ?? -7) != -7: return 3
    if (f["k"] ?? -7) != 4: return 4
    return 0
"#;
    assert_eq!(run(src), 0);
}

/// A present value whose raw word collides with the nil sentinels (0, 3)
/// is still present: presence is the runtime tag, not a value compare.
#[test]
fn present_sentinel_values_are_not_nil() {
    let src = r#"fn main() -> i64:
    var d: Dict<text, i64> = {}
    d["three"] = 3
    d["zero"] = 0
    if (d["three"] ?? 9) != 3: return 1
    if (d["zero"] ?? 9) != 0: return 2
    return 0
"#;
    assert_eq!(run(src), 0);
}

#[test]
fn bool_and_float_values_miss_coalesce() {
    let src = r#"fn main() -> i64:
    var b: Dict<text, bool> = {}
    b["t"] = true
    b["f"] = false
    if (b["t"] ?? false) != true: return 1
    if (b["f"] ?? true) != false: return 2
    if (b["x"] ?? true) != true: return 3
    var f: Dict<text, f64> = {}
    f["h"] = 1.5
    if (f["h"] ?? 0.25) != 1.5: return 4
    if (f["x"] ?? 0.25) != 0.25: return 5
    return 0
"#;
    assert_eq!(run(src), 0);
}
