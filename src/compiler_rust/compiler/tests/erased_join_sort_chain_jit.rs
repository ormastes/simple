//! Executable regression for erased-receiver `.join(sep)` after `.sort()`.
//!
//! When an array chain like `["b", "a"].sort().join(",")` passes through the
//! Cranelift JIT backend, `rt_sort` leaves the intermediate receiver typed as
//! `TypeId::ANY` (bare `.join`). Pre-fix, `closures_structs.rs` lacked `("join", 1)`
//! in `is_bare_builtin_collection_method`, so a lone linked `Type.join` method
//! (e.g. `CacheSingleFlightV1.join(self, key, request_id)` in Stage 2) hijacked
//! the call via single-candidate suffix matching instead of routing to `rt_string_join`.

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
fn erased_sort_join_routes_to_builtin_not_unrelated_two_arg_method() {
    let source = r#"
struct DummyFlight:
    tag: i64

    fn join(key: text, request_id: text) -> text:
        return "HIJACKED:" + key + ":" + request_id

fn make_parts() -> [text]:
    return ["beta", "alpha"]

fn main() -> i64:
    val unused = DummyFlight(tag: 7)
    val joined = make_parts().sort().join(",")
    if joined != "alpha,beta":
        return 1
    var erased: Any = ["x", "y"]
    if erased.join("-") != "x-y":
        return 2
    val check_unused = unused.join("k", "r")
    if check_unused != "HIJACKED:k:r":
        return 3
    return 42
"#;
    assert_eq!(
        run(source),
        42,
        "erased `.sort().join(sep)` must execute `rt_string_join`, not hijack onto DummyFlight.join"
    );
}
