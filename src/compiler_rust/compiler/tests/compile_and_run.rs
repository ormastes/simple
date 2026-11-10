#![cfg(target_arch = "x86_64")]
use simple_compiler::CompilerPipeline;
use simple_runtime::loader::ModuleLoader;

/// Common compilation and execution helper
fn compile_with_method<F>(src: &str, compile_fn: F) -> i32
where
    F: FnOnce(&mut CompilerPipeline, &std::path::Path, &std::path::Path) -> Result<(), simple_compiler::CompileError>,
{
    let dir = tempfile::tempdir().unwrap();
    let src_path = dir.path().join("main.simple");
    let out_path = dir.path().join("main.smf");

    std::fs::write(&src_path, src).unwrap();

    let mut compiler = CompilerPipeline::new().unwrap();
    compile_fn(&mut compiler, &src_path, &out_path).unwrap();

    let loader = ModuleLoader::new();
    let module = loader.load(&out_path).unwrap();

    type MainFn = extern "C" fn() -> i32;
    let main: MainFn = module.entry_point().expect("main symbol");
    main()
}

/// Helper to compile and run a simple program
fn compile_and_run(src: &str) -> i32 {
    compile_with_method(src, |compiler, src_path, out_path| compiler.compile(src_path, out_path))
}

#[test]
fn compile_and_run_main() {
    assert_eq!(compile_and_run("main = 0"), 0);
}

#[test]
fn compile_preserves_root_import_types_for_annotated_local_fields() {
    let dir = tempfile::tempdir().unwrap();
    let package = dir.path().join("receipt_provider");
    std::fs::create_dir(&package).unwrap();
    let provider = package.join("__init__.spl");
    let entry = dir.path().join("main.spl");
    let output = dir.path().join("main.smf");
    std::fs::write(
        provider,
        "pub struct Receipt:\n    value: i64\n\npub fn make_receipt() -> Receipt:\n    Receipt(value: 7)\n",
    )
    .unwrap();
    std::fs::write(
        &entry,
        "use receipt_provider.Receipt\nuse receipt_provider.make_receipt\n\nfn main() -> i64:\n    val result: Receipt = make_receipt()\n    result.value\n",
    )
    .unwrap();

    let mut compiler = CompilerPipeline::new().unwrap();
    compiler.compile(&entry, &output).unwrap();

    let loader = ModuleLoader::new();
    let module = loader.load(&output).unwrap();
    let main: extern "C" fn() -> i32 = module.entry_point().expect("main symbol");
    assert_eq!(main(), 7);
}

#[test]
fn compile_integer_literal() {
    assert_eq!(compile_and_run("main = 42"), 42);
}

#[test]
fn compile_negative_integer() {
    assert_eq!(compile_and_run("main = -5"), -5);
}

#[test]
fn compile_addition() {
    assert_eq!(compile_and_run("main = 10 + 32"), 42);
}

#[test]
fn compile_subtraction() {
    assert_eq!(compile_and_run("main = 50 - 8"), 42);
}

#[test]
fn compile_multiplication() {
    assert_eq!(compile_and_run("main = 6 * 7"), 42);
}

#[test]
fn compile_division() {
    assert_eq!(compile_and_run("main = 84 / 2"), 42);
}

#[test]
fn compile_modulo() {
    assert_eq!(compile_and_run("main = 47 % 5"), 2);
}

#[test]
fn compile_comparison_lt() {
    assert_eq!(compile_and_run("main = if 1 < 2: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 2 < 1: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_gt() {
    assert_eq!(compile_and_run("main = if 2 > 1: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 1 > 2: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_lte() {
    assert_eq!(compile_and_run("main = if 1 <= 1: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 2 <= 1: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_gte() {
    assert_eq!(compile_and_run("main = if 2 >= 2: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 1 >= 2: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_eq() {
    assert_eq!(compile_and_run("main = if 42 == 42: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 42 == 43: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_ne() {
    assert_eq!(compile_and_run("main = if 42 != 43: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 42 != 42: 1 else: 0"), 0);
}

#[test]
fn compile_logical_and() {
    assert_eq!(compile_and_run("main = if true and true: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if true and false: 1 else: 0"), 0);
}

#[test]
fn compile_logical_or() {
    assert_eq!(compile_and_run("main = if false or true: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if false or false: 1 else: 0"), 0);
}

#[test]
fn compile_let_binding() {
    assert_eq!(compile_and_run("val x = 42\nmain = x"), 42);
}

#[test]
fn compile_multiple_lets() {
    assert_eq!(compile_and_run("val a = 10\nval b = 32\nmain = a + b"), 42);
}

#[test]
fn compile_function_definition() {
    assert_eq!(
        compile_and_run(
            r#"
fn add(a, b):
    return a + b
main = add(10, 32)
"#
        ),
        42
    );
}

#[test]
fn compile_nested_arithmetic() {
    assert_eq!(compile_and_run("main = (10 + 20) * 2 - 18"), 42);
}

#[test]
fn compile_boolean_true() {
    assert_eq!(compile_and_run("main = if true: 42 else: 0"), 42);
}

#[test]
fn compile_boolean_false() {
    assert_eq!(compile_and_run("main = if false: 0 else: 42"), 42);
}

/// Regression test for bug seed_compile_smf_stub_fail_open_2026-07-17:
/// `compile()` on a bare script entry (no `fn main`, no `main = <expr>`
/// result-binding idiom) must synthesize a real `main` and generate real
/// executable code for the script body, instead of interpreting it for side
/// effects at compile time and discarding them into a 219-byte
/// constant-return stub SMF that does nothing when run. This is the exact
/// `print("run-ok")` scenario from the bug report.
#[test]
fn compile_and_run_bare_script_print_executes_for_real() {
    use simple_runtime::value::{rt_capture_stdout_start, rt_capture_stdout_stop};

    rt_capture_stdout_start();
    let exit_code = compile_and_run("print(\"run-ok\")");
    let captured = rt_capture_stdout_stop();

    assert_eq!(exit_code, 0);
    assert!(
        captured.contains("run-ok"),
        "expected the compiled script to actually execute `print(\"run-ok\")` at run time \
(not interpret-and-discard into a stub), got captured stdout: {:?}",
        captured
    );
}

/// The legacy `main = <expr>` result-binding idiom must keep working
/// unchanged alongside a preceding script statement (bug
/// seed_compile_smf_stub_fail_open_2026-07-17 fix is scoped to bare scripts
/// with no `main =` binding; this case still uses the interpreter fallback).
#[test]
fn compile_and_run_main_assignment_with_preceding_statement_unaffected() {
    assert_eq!(compile_and_run("val x = 40\nmain = x + 2"), 42);
}

// =============================================================================
// Native compilation tests (HIR → MIR → Cranelift)
// =============================================================================

/// Helper to compile using native codegen and run
fn compile_native_and_run(src: &str) -> i32 {
    compile_with_method(src, |compiler, src_path, out_path| {
        compiler.compile_native(src_path, out_path)
    })
}

#[test]
fn native_compile_simple_return() {
    // fn main() -> i64: return 42
    let code = r#"
fn main() -> i64:
    return 42
"#;
    assert_eq!(compile_native_and_run(code), 42);
}

// Un-ignored 2026-08-17 (triage shard A6): verified passing on a freshly built
// seed. The `#[ignore]` predated the fix and made the reproducer invisible —
// exactly the silent-green shape this sweep is hunting. Bug doc:
// doc/08_tracking/bug/rust_seed_native_bool_arg_inlined_call_wrong_value_2026-07-17.md
#[test]
fn native_bool_argument_false_survives_inlined_calls() {
    let code = r#"
fn f(x: bool) -> i64:
    if x:
        return 1
    return 0

fn main() -> i64:
    return f(false) * 10 + f(true)
"#;

    // Decimal packing checks both calls: false must contribute 0, true must contribute 1.
    assert_eq!(compile_native_and_run(code), 1);
}

#[test]
fn native_compile_addition() {
    let code = r#"
fn main() -> i64:
    return 10 + 32
"#;
    assert_eq!(compile_native_and_run(code), 42);
}

#[test]
fn native_compile_subtraction() {
    let code = r#"
fn main() -> i64:
    return 50 - 8
"#;
    assert_eq!(compile_native_and_run(code), 42);
}

#[test]
fn native_compile_multiplication() {
    let code = r#"
fn main() -> i64:
    return 6 * 7
"#;
    assert_eq!(compile_native_and_run(code), 42);
}

#[test]
fn native_compile_comparison() {
    let code = r#"
fn main() -> i64:
    if 10 > 5:
        return 42
    else:
        return 0
"#;
    assert_eq!(compile_native_and_run(code), 42);
}

#[test]
fn native_compile_local_variable() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 42
    return x
"#;
    assert_eq!(compile_native_and_run(code), 42);
}

#[test]
fn native_inline_array_len_handles_tagged_nil() {
    let code = r#"
extern fn rt_array_len(array: i64) -> i64

fn main() -> i64:
    rt_array_len(3)
"#;
    assert_eq!(compile_native_and_run(code), 0);
}

#[test]
fn native_compile_binary_with_locals() {
    let code = r#"
fn main() -> i64:
    let a: i64 = 10
    let b: i64 = 32
    return a + b
"#;
    assert_eq!(compile_native_and_run(code), 42);
}

#[test]
fn native_compile_while_loop() {
    let code = r#"
fn main() -> i64:
    let mut x: i64 = 0
    while x < 42:
        x = x + 1
    return x
"#;
    assert_eq!(compile_native_and_run(code), 42);
}

#[test]
fn native_compile_nested_if() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 10
    if x > 5:
        if x > 8:
            return 42
        else:
            return 0
    else:
        return -1
"#;
    assert_eq!(compile_native_and_run(code), 42);
}

// ============================================================================
// Coverage Instrumentation Tests (#674)
// ============================================================================

/// Helper to compile with coverage enabled
fn compile_with_coverage(src: &str) -> i32 {
    compile_with_method(src, |compiler, src_path, out_path| {
        compiler.set_coverage_enabled(true);
        compiler.compile(src_path, out_path)
    })
}

#[test]
fn coverage_compile_simple_if() {
    // Test that code with coverage probes runs correctly
    let code = r#"
fn main() -> i64:
    let x: i64 = 5
    if x > 3:
        return 42
    return 0
"#;
    assert_eq!(compile_with_coverage(code), 42);
}

#[test]
fn coverage_compile_while_loop() {
    // Test while loop with coverage probes
    let code = r#"
fn main() -> i64:
    var count: i64 = 0
    while count < 5:
        count = count + 1
    return count
"#;
    assert_eq!(compile_with_coverage(code), 5);
}

#[test]
fn coverage_compile_compound_boolean() {
    // Test compound boolean expression with condition probes
    let code = r#"
fn test(a: bool, b: bool) -> i64:
    if a and b:
        return 1
    return 0

fn main() -> i64:
    return test(true, true)
"#;
    assert_eq!(compile_with_coverage(code), 1);
}

#[test]
fn coverage_compile_or_expression() {
    // Test or expression with condition probes
    let code = r#"
fn test(a: bool, b: bool) -> i64:
    if a or b:
        return 1
    return 0

fn main() -> i64:
    return test(false, true)
"#;
    assert_eq!(compile_with_coverage(code), 1);
}

#[test]
fn coverage_compile_nested_conditions() {
    // Test nested conditions with multiple decision probes
    let code = r#"
fn main() -> i64:
    let x: i64 = 10
    if x > 5:
        if x > 8:
            return 42
    return 0
"#;
    assert_eq!(compile_with_coverage(code), 42);
}

#[test]
fn bare_len_uses_rt_len_not_name_suffix_binding() {
    // Regression (2026-06-11, stage4 site 11): bare `.len()` on a receiver
    // whose static type is lost (for-loop binder) must lower to the rt_len
    // tag-dispatch builtin, NOT name-suffix bind to whatever unique
    // `Type_dot_len` method happens to be linked (Box.len -> 42 here;
    // std ListIter.len in the stage4 CLI closure, which segfaulted
    // `stage4 lint`). Arrays drive the untyped binder; the static runtime
    // symbol registry must be populated for the loader to resolve rt_array_*.
    simple_runtime::register_static_runtime_symbols();
    let code = r#"
class Box:
    n: i64
    fn len() -> i64:
        42

fn box_len(b: Box) -> i64:
    b.len()

fn main() -> i64:
    val rows = [[1, 2], [3]]
    var total = 0
    for row in rows:
        total = total + row.len()
    total
"#;
    // Pre-fix this returned 84 (Box.len()==42 per row); rt_len gives 2+1.
    // NOTE: box_len is a decoy keeping a linkable Box_dot_len in func_ids; it
    // is not called because this harness skips typecheck, so even its typed
    // receiver would reach codegen as a bare `len`. The full pipeline
    // qualifies typed receivers (verified via native-build e2e repro).
    assert_eq!(compile_and_run(code), 3);
}

/// seed_untyped_byte_len_binding_raw_i64_misdecoded_2026_11_09 (PR #7883):
/// the exact text-scan loop whose bound `value_len - needle_len` was built
/// from two UNTYPED `byte_len` bindings. Under the JIT the raw i64 results
/// were carried as if tagged, the difference misdecoded, and the loop never
/// terminated; with a bounded guard here it returned the wrong position.
#[test]
fn untyped_byte_len_difference_is_integer_under_jit() {
    let src = r#"fn index_of(value: text, needle: text) -> i64:
    val value_len = value.byte_len()
    val needle_len = needle.byte_len()
    if needle_len > value_len:
        return -1
    var start = 0
    var guard = 0
    while start <= value_len - needle_len:
        guard = guard + 1
        if guard > 64:
            return -99
        var offset = 0
        while offset < needle_len and value.byte_at(start + offset) == needle.byte_at(offset):
            offset = offset + 1
        if offset == needle_len:
            return start
        start = start + 1
    return -1

fn main() -> i64:
    val a = "semantic".byte_len()
    val b = "/".byte_len()
    if a - b != 7:
        return 100 + (a - b)
    val pos = index_of("abc/def", "/")
    if pos != 3:
        return 50 + pos
    if index_of("semantic_surface.spl", "/") != -1:
        return 40
    return 0
"#;
    assert_eq!(compile_and_run(src), 0);
}

// Bug: doc/08_tracking/bug/jit_unsafe_optional_as_cast_garbage_2026_11_09.md
// `T? as <numeric>` inside `unsafe:` must extract the Some payload, not
// reinterpret the boxed Option heap word.
#[test]
fn unsafe_optional_u64_as_cast_extracts_payload() {
    let src = r#"
fn mk(v: u64) -> u64?:
    if v != 0:
        v
    else:
        nil

fn main() -> i64:
    val r = mk(4275044352)
    var out: u64 = 0
    unsafe:
        out = r as u64
    if out == 4275044352:
        return 42
    return 7
"#;
    assert_eq!(compile_and_run(src), 42);
}

#[test]
fn unsafe_optional_i64_as_cast_extracts_payload() {
    let src = r#"
fn mk(v: i64) -> i64?:
    if v != 0:
        v
    else:
        nil

fn main() -> i64:
    val r = mk(-1234567)
    var out: i64 = 0
    unsafe:
        out = r as i64
    if out == -1234567:
        return 42
    return 7
"#;
    assert_eq!(compile_and_run(src), 42);
}

#[test]
fn unsafe_optional_text_as_cast_decodes_payload() {
    let src = r#"
fn mk(v: text) -> text?:
    if v != "":
        v
    else:
        nil

fn main() -> i64:
    val r = mk("77")
    var out: i64 = 0
    unsafe:
        out = r as i64
    if out == 77:
        return 42
    return 7
"#;
    assert_eq!(compile_and_run(src), 42);
}

#[test]
fn unsafe_option_enum_i64_as_cast_extracts_payload() {
    let src = r#"
fn main() -> i64:
    val r: Option<i64> = Some(99)
    var out: i64 = 0
    unsafe:
        out = r as i64
    if out == 99:
        return 42
    return 7
"#;
    assert_eq!(compile_and_run(src), 42);
}

#[test]
fn unsafe_optional_as_cast_to_wider_int_converts_payload() {
    let src = r#"
fn mk(v: i32) -> i32?:
    if v != 0:
        v
    else:
        nil

fn main() -> i64:
    val r = mk(-5)
    var out: i64 = 0
    unsafe:
        out = r as i64
    if out == -5:
        return 42
    return 7
"#;
    assert_eq!(compile_and_run(src), 42);
}

// Bug jit_struct_assignment_aliases_not_copies_2026-08-10: value-struct
// assignment must copy on the JIT/SMF lane; classes keep reference semantics.
#[test]
fn struct_reassign_copies_not_aliases() {
    simple_runtime::register_static_runtime_symbols();
    let code = r#"
struct P:
    x: i64
    y: i64

fn main() -> i64:
    val a = P(x: 1, y: 2)
    var b = P(x: 0, y: 0)
    b = a
    b.x = 99
    a.x
"#;
    assert_eq!(compile_and_run(code), 1);
}

#[test]
fn struct_let_copy_field_mutate_keeps_source() {
    simple_runtime::register_static_runtime_symbols();
    let code = r#"
struct P:
    x: i64
    y: i64

fn main() -> i64:
    val a = P(x: 1, y: 2)
    var b = a
    b.x = 99
    a.x + b.x
"#;
    assert_eq!(compile_and_run(code), 100);
}

#[test]
fn nested_struct_reassign_copies_inner() {
    simple_runtime::register_static_runtime_symbols();
    let code = r#"
struct In:
    a: i64

struct Out:
    inner: In
    k: i64

fn main() -> i64:
    val o = Out(inner: In(a: 5), k: 1)
    var o2 = Out(inner: In(a: 0), k: 0)
    o2 = o
    o2.inner.a = 77
    o.inner.a
"#;
    assert_eq!(compile_and_run(code), 5);
}

#[test]
fn struct_stored_in_array_element_is_copied() {
    simple_runtime::register_static_runtime_symbols();
    let code = r#"
struct P:
    x: i64

fn main() -> i64:
    var a = P(x: 3)
    var arr = [P(x: 0)]
    arr[0] = a
    a.x = 50
    arr[0].x
"#;
    assert_eq!(compile_and_run(code), 3);
}

#[test]
fn class_reassign_keeps_reference_semantics() {
    simple_runtime::register_static_runtime_symbols();
    let code = r#"
class C:
    x: i64

fn main() -> i64:
    val a = C(x: 1)
    var b = C(x: 0)
    b = a
    b.x = 42
    a.x
"#;
    assert_eq!(compile_and_run(code), 42);
}
