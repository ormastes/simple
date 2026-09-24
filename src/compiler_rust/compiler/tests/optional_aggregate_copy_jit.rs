//! Regression coverage for optional aggregate copies in the Cranelift backend.
//!
//! `AggregateCopy` uses a freshly allocated, zero-filled block as the safe load
//! target for a malformed/non-heap source.  That temporary must not become the
//! result: copying the nil sentinel (raw `3`) must return raw `3`, while a live
//! tagged aggregate must produce a tagged copy whose fields are readable.
//!
//! The HIR constructor checks at the end pin the source-level contract that
//! untyped `Call`, `NamedVar`, and `StringLit` nodes carry no type metadata.
//! A zeroed aggregate crossing the seed/JIT boundary used to turn those fields
//! into arbitrary tagged values (notably `has_type_ == 3`) during Stage 3.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::hir::TypeId;
use simple_compiler::mir::{BlockId, MirFunction, MirInst, MirModule, Terminator};
use simple_parser::ast::Visibility;

fn nil_copy_function() -> MirFunction {
    let mut function = MirFunction::new("nil_copy".to_string(), TypeId::I64, Visibility::Public);
    let nil = function.new_vreg();
    let nil_copy = function.new_vreg();
    let block = function.block_mut(BlockId(0)).expect("new function has entry block");
    block.instructions.push(MirInst::ConstInt { dest: nil, value: 3 });
    block.instructions.push(MirInst::AggregateCopy {
        dest: nil_copy,
        src: nil,
        byte_size: 8,
        type_name: Some("OptionalProbe".to_string()),
        owner_has_vtable: Some(false),
        deep_fields: Vec::new(),
    });
    block.terminator = Terminator::Return(Some(nil_copy));
    function
}

fn valid_copy_function(source_tagged: i64) -> MirFunction {
    let mut function = MirFunction::new("valid_copy".to_string(), TypeId::I64, Visibility::Public);
    let source = function.new_vreg();
    let copy = function.new_vreg();
    let block = function.block_mut(BlockId(0)).expect("new function has entry block");
    // Feed a pointer allocated by the host runtime.  This avoids coupling the
    // probe to StructInit's separate allocation/registration path while still
    // exercising the exact tagged source ABI consumed by AggregateCopy.
    block.instructions.push(MirInst::ConstInt {
        dest: source,
        value: source_tagged,
    });
    block.instructions.push(MirInst::AggregateCopy {
        dest: copy,
        src: source,
        byte_size: 8,
        type_name: Some("OptionalProbe".to_string()),
        owner_has_vtable: Some(false),
        deep_fields: Vec::new(),
    });
    block.terminator = Terminator::Return(Some(copy));
    function
}

fn run_probe() -> (i64, i64) {
    let source_ptr = simple_runtime::rt_alloc(8);
    assert!(!source_ptr.is_null(), "probe source allocation must succeed");
    unsafe { *(source_ptr as *mut i64) = 42 };

    let mut module = MirModule::new();
    module.functions.push(nil_copy_function());
    module.functions.push(valid_copy_function(source_ptr as i64 | 1));
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&module).expect("aggregate-copy probe must compile");
    let nil = unsafe { jit.call_i64_void("nil_copy").expect("nil-copy probe must execute") };
    let valid = unsafe { jit.call_i64_void("valid_copy").expect("valid-copy probe must execute") };
    (nil, valid)
}

#[test]
fn nil_optional_aggregate_stays_nil_and_live_aggregate_is_copied() {
    let (nil, valid) = run_probe();
    assert_eq!(nil, 3, "nil Optional<aggregate> must remain the raw nil sentinel");
    assert_ne!(valid, 3, "a live aggregate copy must not become nil");
    assert_eq!(valid & 7, 1, "a live aggregate copy must carry the heap tag");
    let copied_word = unsafe { *((valid & !7) as *const i64) };
    assert_eq!(copied_word, 42, "a live aggregate copy must preserve its first field");
}

#[test]
fn untyped_hir_expression_constructors_do_not_invent_type_metadata() {
    let source = std::fs::read_to_string("src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl")
        .expect("HIR expression lowering source must exist");

    for (variant, constructor) in [
        (
            "Call",
            "HirExprKind.Call(self.lower_hir_expr(call_callee_t), hir_args, [])",
        ),
        ("NamedVar", "HirExprKind.NamedVar(resolved_callable, callable_name)"),
        ("StringLit", "case ExprKind.StringLit(value, interps):"),
    ] {
        let start = source
            .find(constructor)
            .unwrap_or_else(|| panic!("HIR {variant} constructor disappeared"));
        let window = &source[start..source.len().min(start + 320)];
        let (has_type, type_value) = if variant == "StringLit" {
            // String literals use the shared final HIR wrapper after the
            // variant-specific lowering match, rather than an inline return.
            (
                source.contains("HirExpr(kind: kind, has_type_: false"),
                source.contains("type_: nil, span: e.span"),
            )
        } else {
            (window.contains("has_type_: false"), window.contains("type_: nil"))
        };
        assert!(
            has_type && type_value,
            "untyped HIR {variant} must explicitly carry has_type_: false and type_: nil; window={window:?}"
        );
    }
}
