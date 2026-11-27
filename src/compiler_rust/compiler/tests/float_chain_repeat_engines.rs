//! A float math method chained straight into an integer cast
//! (`x.ceil().to_i64()`) must convert the VALUE on every engine, and
//! `[v; n]` with a parameter fill and a computed count must store the fill
//! tagged. The fixture's `main` returns a failure bitmask (0 = pass) and prints
//! one verdict line; the interpreter, the static JIT and a native cranelift
//! build must all answer 0.
//!
//! Pre-fix the JIT/native answered mask 447: the chained receiver's vreg had
//! no MIR type, so the cast took `rt_to_int_dynamic` on the raw f64 register
//! and returned its IEEE bits (`0.4.ceil().to_i64()` == 4607182418800017408),
//! and the interpreter rejected `x.ceil().sqrt()` ("method 'sqrt' not found
//! on value of type f64 in nested call context").
//! doc/08_tracking/bug/float_method_chain_to_i64_returns_bits_2026-11-24.md
//! doc/08_tracking/bug/array_repeat_nonliteral_fill_computed_count_2026-11-24.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::interpreter::evaluate_module;
use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use simple_compiler::{hir, mir};
use simple_parser::Parser;
use std::path::PathBuf;

const SOURCE: &str = include_str!("../../../../test/fixtures/native/float_chain_repeat/main.spl");

#[test]
fn float_chain_repeat_interpreter() {
    let ast = Parser::new(SOURCE).parse().expect("fixture must parse");
    let mask = evaluate_module(&ast.items).expect("fixture must evaluate");
    assert_eq!(mask, 0, "interpreter failure mask");
}

#[test]
fn float_chain_repeat_jit() {
    let ast = Parser::new(SOURCE).parse().expect("fixture must parse");
    let hir_module = hir::lower(&ast).expect("fixture must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("fixture must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let mask = unsafe { jit.call_i64_void("main").expect("main must execute") };
    assert_eq!(mask, 0, "JIT failure mask");
}

#[test]
fn float_chain_repeat_native_cranelift() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let source = repo.join("test/fixtures/native/float_chain_repeat");
    let temporary = tempfile::tempdir().unwrap();
    let executable = temporary.path().join(if cfg!(windows) { "probe.exe" } else { "probe" });
    std::env::set_var("SIMPLE_BOOTSTRAP", "1");
    std::env::set_var("SIMPLE_NO_STUB_FALLBACK", "1");
    let result = NativeProjectBuilder::new(repo, executable.clone())
        .config(NativeBuildConfig {
            backend: "cranelift".to_string(),
            runtime_bundle: "core-c-bootstrap".to_string(),
            entry_closure: true,
            parallel: false,
            num_threads: Some(1),
            cache_dir: Some(temporary.path().join("native-cache")),
            ..NativeBuildConfig::default()
        })
        .source_dir(source.clone())
        .entry_file(source.join("main.spl"))
        .build()
        .unwrap_or_else(|e| panic!("native build must succeed: {e:?}"));
    assert_eq!(result.failed, 0, "failed units");
    let run = std::process::Command::new(executable).output().unwrap();
    assert_eq!(
        String::from_utf8_lossy(&run.stdout).trim(),
        "float-chain-repeat PASS",
        "native stdout (status {})",
        run.status
    );
}
