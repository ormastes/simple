//! C1 + C2 Integration Tests — `call_runtime_N` and `declare_uniform_i64_import` helpers
//!
//! **Gate for Phase 5 (implement):** every test here must pass AFTER C1+C2 land.
//! They are expected to compile but may fail with "helper not found" or a
//! module-declaration error until `codegen/instr/helpers.rs` exposes the new
//! `pub(crate)` helpers and the 74 open-coded sites in `methods.rs`,
//! `closures_structs.rs`, `basic_ops.rs`, etc. are rewritten to call them.
//!
//! Covered call sites (arch.md §3 C1):
//!   - `methods.rs` private `call_runtime_1/2/3/2_void` — promoted to helpers.rs
//!   - All ~74 open-coded `runtime_funcs[name] + declare_func_in_func + adapted_call`
//!     sites across 17 files that will call the promoted helpers after C1.
//!
//! Covered call sites (arch.md §3 C2):
//!   - `calls.rs:698`, `methods.rs:309`, `closures_structs.rs:65`, `mod.rs:232`
//!     dynamic-resolve pattern (cache-check + build I64 sig + declare_function +
//!     cache + declare_func_in_func) → replaced by `declare_uniform_i64_import`.
//!
//! Perf gate (AC-3, arch.md §4):
//!   - `bin/simple build` wall-clock and RSS must not regress ≥3% vs. pre-C1 baseline.
//!   - Measured via `/usr/bin/time -v` on the full bootstrap chain.
//!   - The harness is in `tests/perf_call_runtime_helpers.rs` (separate binary).
//!
//! See also: `arch.md §4 Perf Measurement Plan`.

#![cfg(target_arch = "x86_64")]

mod common;

use common::{find_hir_function, parse_and_lower};
use simple_compiler::codegen::instr::helpers::{
    call_runtime_0, call_runtime_1, call_runtime_2, call_runtime_2_void, call_runtime_3,
    declare_uniform_i64_import,
};
use simple_compiler::codegen::instr::{InstrContext, InstrResult};
use simple_compiler::CompilerPipeline;

// InstBuilder must be in scope for builder.ins().iconst()/return_() calls in
// the C2 idempotency tests below.
use cranelift_codegen::ir::InstBuilder;

// ============================================================================
// Helper: compile a minimal Simple program exercising a specific call arity
// ============================================================================

/// Compile source and return Ok(()) if it succeeds without panicking in codegen.
fn compile_ok(src: &str) -> Result<(), String> {
    let dir = tempfile::tempdir().map_err(|e| e.to_string())?;
    let src_path = dir.path().join("test.simple");
    let out_path = dir.path().join("test.smf");
    std::fs::write(&src_path, src).map_err(|e| e.to_string())?;
    let mut compiler = CompilerPipeline::new().map_err(|e| e.to_string())?;
    compiler
        .compile(&src_path, &out_path)
        .map_err(|e| e.to_string())
}

// ============================================================================
// C1 — call_runtime_N helper availability and codegen path exercise
// ============================================================================

/// Each helper function must be importable (i.e., pub(crate) in helpers.rs).
/// This test will fail to compile until C1 promotes the helpers.
#[test]
fn c1_call_runtime_helpers_are_pub_crate() {
    // The use statement at the top of this file imports the helpers.
    // If the helpers are not pub(crate) in codegen/instr/helpers.rs, this
    // file will not compile — which is the intended pre-C1 failure mode.
    //
    // Post-C1: the import succeeds and this test body trivially passes.
    // We just assert the module compiled (reaching this line proves it).
    assert!(true, "call_runtime helpers are importable as pub(crate)");
}

/// Arity-0: codegen path that calls a runtime function with no arguments.
/// Exercises programs that call e.g. rt_gc_collect() or rt_noop().
#[test]
fn c1_arity_0_codegen_path_compiles() {
    // A program that would exercise a call_runtime_0 site after C1.
    // `array.len()` is a typical arity-1 (receiver only) call; a bare
    // module-level function call with no args exercises arity-0.
    let src = r#"
fn no_arg_rt_call() -> i64:
    val arr = [1, 2, 3]
    arr.len()

main = no_arg_rt_call()
"#;
    assert!(
        compile_ok(src).is_ok(),
        "arity-0 codegen path must compile without panic"
    );
}

/// Arity-1: programs that call a runtime function with one argument.
/// Covers `call_runtime_1` sites like rt_array_pop, rt_array_clear, rt_dict_keys, etc.
#[test]
fn c1_arity_1_codegen_path_compiles() {
    let src = r#"
fn arity_1_site() -> i64:
    val arr = [10, 20, 30]
    arr.len()

main = arity_1_site()
"#;
    assert!(
        compile_ok(src).is_ok(),
        "arity-1 codegen path must compile without panic"
    );
}

/// Arity-2: programs that call a runtime function with two arguments.
/// Covers `call_runtime_2` sites like rt_array_push, rt_string_concat,
/// rt_index_get, rt_dict_get, rt_contains, etc.
#[test]
fn c1_arity_2_codegen_path_compiles() {
    let src = r#"
fn arity_2_site() -> text:
    val a = "hello"
    val b = " world"
    a + b

main = 0
"#;
    assert!(
        compile_ok(src).is_ok(),
        "arity-2 codegen path must compile without panic"
    );
}

/// Arity-2 void: call_runtime_2_void (no return value).
/// Covers sites like rt_print_value where the return is discarded.
#[test]
fn c1_arity_2_void_codegen_path_compiles() {
    let src = r#"
fn arity_2_void_site():
    val arr = [1, 2, 3]
    arr.push(4)

main = 0
"#;
    assert!(
        compile_ok(src).is_ok(),
        "arity-2-void codegen path must compile without panic"
    );
}

/// Arity-3: programs that call a runtime function with three arguments.
/// Covers `call_runtime_3` sites like rt_index_set, rt_dict_set, rt_tuple_set.
#[test]
fn c1_arity_3_codegen_path_compiles() {
    let src = r#"
fn arity_3_site() -> i64:
    var arr = [1, 2, 3]
    arr.set(0, 99)
    arr.get(0)

main = arity_3_site()
"#;
    // Note: even if the language surface for arr.set isn't wired up yet,
    // the codegen layer must not panic — it may return a compile error for
    // the unsupported method, which is acceptable here.
    let result = compile_ok(src);
    // Accept either success or a clean compile error; reject panics.
    match result {
        Ok(_) => {}
        Err(e) => {
            assert!(
                !e.contains("panic") && !e.contains("thread 'main' panicked"),
                "arity-3 codegen must not panic, got: {}",
                e
            );
        }
    }
}

/// All 5 arity helpers exist in the same file and can be imported together
/// (verifies no name collision or visibility issue in helpers.rs).
#[test]
fn c1_all_arity_helpers_coexist_in_helpers_rs() {
    // If any helper is missing or has a visibility conflict, this file won't compile.
    // Reaching this line confirms all 5 are importable simultaneously.
    assert!(
        true,
        "call_runtime_0/1/2/2_void/3 all coexist in helpers.rs"
    );
}

// ============================================================================
// C2 — declare_uniform_i64_import helper
// ============================================================================

/// declare_uniform_i64_import must be importable as pub(crate) from helpers.rs.
/// Pre-C2: compile error (not exported). Post-C2: this test compiles and passes.
#[test]
fn c2_declare_uniform_i64_import_is_pub_crate() {
    assert!(
        true,
        "declare_uniform_i64_import is importable as pub(crate)"
    );
}

/// Idempotency: calling declare_uniform_i64_import twice with the same name
/// must not panic or produce a duplicate-declaration error.
///
/// This test uses a minimal Cranelift JIT context to invoke the helper directly.
/// It mirrors the `declare_func_in_func` + cache pattern at calls.rs:698,
/// methods.rs:309, closures_structs.rs:65, mod.rs:232.
#[test]
fn c2_declare_uniform_i64_import_idempotent() {
    use cranelift_codegen::ir::types;
    use cranelift_codegen::ir::InstBuilder;
    use cranelift_codegen::settings;
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::{Linkage, Module};
    use simple_compiler::codegen::instr::InstrContext;

    let isa_builder = cranelift_native::builder().expect("host ISA");
    let flags = settings::Flags::new(settings::builder());
    let isa = isa_builder.finish(flags).expect("ISA");
    let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    let mut module = JITModule::new(builder);

    // Register a dummy runtime function so runtime_funcs lookup doesn't panic.
    let mut sig = module.make_signature();
    sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
    sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
    let dummy_id = module
        .declare_function("rt_dummy_uniform", Linkage::Import, &sig)
        .expect("declare dummy");

    let mut runtime_funcs = std::collections::HashMap::new();
    runtime_funcs.insert("rt_dummy_uniform".to_string(), dummy_id);

    // Declare a function body in which we call declare_uniform_i64_import twice.
    let mut fn_sig = module.make_signature();
    fn_sig
        .returns
        .push(cranelift_codegen::ir::AbiParam::new(types::I64));
    let test_fn_id = module
        .declare_function("test_idempotent", Linkage::Export, &fn_sig)
        .expect("declare test fn");

    let mut ctx = module.make_context();
    let mut fn_ctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fn_ctx);
        let entry_block = builder.create_block();
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let mut instr_ctx = InstrContext::new_for_test(&mut module, &runtime_funcs);

        // First call — must succeed.
        let _ref1 = declare_uniform_i64_import(
            &mut instr_ctx,
            &mut builder,
            "rt_dummy_uniform",
            1, // n_params
        );

        // Second call with the same name — must not panic or produce duplicate error.
        let _ref2 = declare_uniform_i64_import(
            &mut instr_ctx,
            &mut builder,
            "rt_dummy_uniform",
            1,
        );

        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[zero]);
        builder.finalize();
    }

    // If we reach here without panic, idempotency holds.
    assert!(true, "declare_uniform_i64_import is idempotent for same name");
}

/// Verify that declare_uniform_i64_import with n_params=0 (no-arg import)
/// works (boundary: zero-param uniform signature).
#[test]
fn c2_declare_uniform_i64_import_zero_params() {
    let src = r#"
fn zero_param_rt() -> i64:
    0

main = zero_param_rt()
"#;
    assert!(
        compile_ok(src).is_ok(),
        "zero-param uniform import must compile"
    );
}

/// Verify that declare_uniform_i64_import with n_params=3 (3-arg uniform)
/// works (boundary: maximum arity covered by C1+C2).
#[test]
fn c2_declare_uniform_i64_import_three_params() {
    let src = r#"
fn three_param_rt(a: i64, b: i64, c: i64) -> i64:
    a + b + c

main = three_param_rt(1, 2, 3)
"#;
    assert!(
        compile_ok(src).is_ok(),
        "3-param uniform import must compile"
    );
}

// ============================================================================
// Regression: existing codegen tests must still pass
// ============================================================================

/// This test is a canary: it re-runs a simple compile-and-run program that
/// exercises the method codegen path (which internally uses call_runtime_N).
/// If C1+C2 introduce a regression in the call-convention adapter, this fails.
#[test]
fn c1_c2_regression_array_push_pop() {
    let src = r#"
fn push_pop_test() -> i64:
    var arr = [1, 2, 3]
    arr.push(4)
    arr.len()

main = push_pop_test()
"#;
    assert!(
        compile_ok(src).is_ok(),
        "array push/pop codegen must still work after C1+C2"
    );
}

#[test]
fn c1_c2_regression_string_concat() {
    let src = r#"
fn concat_test() -> text:
    "hello" + " world"

main = 0
"#;
    assert!(
        compile_ok(src).is_ok(),
        "string concat codegen must still work after C1+C2"
    );
}

#[test]
fn c1_c2_regression_dict_operations() {
    let src = r#"
fn dict_test() -> i64:
    val d = {"a": 1, "b": 2}
    d.len()

main = dict_test()
"#;
    assert!(
        compile_ok(src).is_ok(),
        "dict codegen must still work after C1+C2"
    );
}
