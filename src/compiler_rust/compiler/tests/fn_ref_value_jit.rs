//! A NAMED function used as a first-class value (`val g = add_one`,
//! `Port(tokenize_fn: my_tok)`) must be JIT-compiled — no whole-module bail to
//! the interpreter — and must call correctly through the closure ABI.
//!
//! Pre-fix: `JitCompiler::compile_module` refused the module with
//! "loads a named function as a callable value; the JIT closure ABI has no
//! tag-boxed representation for a bare function pointer". That single refusal
//! dropped the ENTIRE stage1 compiler (`compiler_services.spl:168`, fn-ref
//! ports) onto the tree-walking interpreter (~30x per statement). See
//! doc/08_tracking/bug/jit_fn_ref_port_bails_whole_stage1_2026-08-22.md.
//!
//! Fix: every such load gets a `name$boxed` thunk (codegen/closure_boxed_entry.rs)
//! wrapped in a zero-capture `rt_closure_new`, so the value IS a closure.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    // The load-bearing assertion: no bail. Pre-fix this is Err(...named function
    // as a callable value...).
    jit.compile_module(&mir_module)
        .expect("named fn used as a value must JIT-compile without bailing");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn named_fn_as_value_is_jit_compiled_and_calls_correctly() {
    let source = r#"
fn add_one(x: i64) -> i64:
    x + 1

fn add(a: i64, b: i64) -> i64:
    a + b

fn apply(f: (i64) -> i64, x: i64) -> i64:
    f(x)

fn main() -> i64:
    val g = add_one
    if g(41) != 42: return 1
    if apply(add_one, 4) != 5: return 2
    val h = add
    if h(40, 2) != 42: return 3
    0
"#;
    assert_eq!(run(source), 0);
}

#[test]
fn fn_ref_port_struct_fields_call_through_jit() {
    // The exact stage1 shape: a struct whose fields are fn refs, built by a
    // factory and invoked through the field (compiler_services.spl ports).
    let source = r#"
struct Port:
    name: text
    flag_fn: () -> bool
    add_fn: (i64, i64) -> i64
    scale_fn: (f64) -> f64

fn my_flag() -> bool:
    true

fn my_add(a: i64, b: i64) -> i64:
    a + b

fn my_scale(x: f64) -> f64:
    x * 1.5

fn make() -> Port:
    Port(name: "p", flag_fn: my_flag, add_fn: my_add, scale_fn: my_scale)

fn main() -> i64:
    val p = make()
    if not p.flag_fn(): return 1
    if p.add_fn(40, 2) != 42: return 2
    if p.scale_fn(2.0) != 3.0: return 3
    0
"#;
    assert_eq!(run(source), 0);
}
