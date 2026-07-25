use super::{aot_compiles, aot_compiles_module, aot_object};
use crate::hir::{BinOp, TypeId};
use crate::mir::{
    BindingStep, BlockId, LocalKind, MirFunction, MirInst, MirLiteral, MirLocal, MirModule, MirPattern, PatternBinding,
    Terminator, UnitOverflowBehavior,
};

// =============================================================================
// Closure / IndirectCall (closures_structs.rs)
// =============================================================================

#[test]
fn codegen_closure_create_and_indirect_call() {
    // Need a callable function in the module for the closure
    let mut func = MirFunction::new(
        "identity".to_string(),
        TypeId::I64,
        simple_parser::ast::Visibility::Public,
    );
    let param_vreg = func.new_vreg();
    func.params.push(MirLocal {
        name: "x".to_string(),
        ty: TypeId::I64,
        kind: LocalKind::Parameter,
        is_ghost: false,
    });
    func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(param_vreg));

    let mut main = MirFunction::new(
        "clos_test".to_string(),
        TypeId::I64,
        simple_parser::ast::Visibility::Public,
    );
    let closure = main.new_vreg();
    let arg = main.new_vreg();
    let dest = main.new_vreg();
    let block = main.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ClosureCreate {
        dest: closure,
        func_name: "identity".to_string(),
        closure_size: 8,
        capture_offsets: vec![],
        capture_types: vec![],
        captures: vec![],
        lambda_params: vec![],
        body_block: None,
    });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
    block.instructions.push(MirInst::IndirectCall {
        dest: Some(dest),
        callee: closure,
        param_types: vec![TypeId::I64],
        return_type: TypeId::I64,
        args: vec![arg],
        effect: crate::mir::Effect::Compute,
    });
    block.terminator = Terminator::Return(Some(dest));

    let mut module = MirModule::new();
    module.functions.push(func);
    module.functions.push(main);

    assert!(aot_compiles_module(module));
}

// =============================================================================
// Method calls (closures_structs.rs, methods.rs, extern_classes.rs)
// =============================================================================

#[test]
fn codegen_method_call_static() {
    // MethodCallStatic compiles as Call with receiver prepended
    // Need a target function
    let mut target = MirFunction::new(
        "Point::get_x".to_string(),
        TypeId::I64,
        simple_parser::ast::Visibility::Public,
    );
    let self_vreg = target.new_vreg();
    target.params.push(MirLocal {
        name: "self".to_string(),
        ty: TypeId::I64,
        kind: LocalKind::Parameter,
        is_ghost: false,
    });
    target.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(self_vreg));

    let mut main = MirFunction::new(
        "method_static".to_string(),
        TypeId::I64,
        simple_parser::ast::Visibility::Public,
    );
    let recv = main.new_vreg();
    let dest = main.new_vreg();
    let block = main.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "Point::get_x".to_string(),
        args: vec![],
    });
    block.terminator = Terminator::Return(Some(dest));

    let mut module = MirModule::new();
    module.functions.push(target);
    module.functions.push(main);

    assert!(aot_compiles_module(module));
}

#[test]
fn codegen_method_call_virtual() {
    assert!(aot_compiles("method_virt", |f| {
        let recv = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
        block.instructions.push(MirInst::MethodCallVirtual {
            dest: Some(dest),
            receiver: recv,
            vtable_slot: 0,
            param_types: vec![],
            return_type: TypeId::I64,
            args: vec![],
        });
        dest
    }));
}

#[test]
fn codegen_builtin_method() {
    assert!(aot_compiles("builtin_m", |f| {
        let recv = f.new_vreg();
        let arr = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 1 });
        block.instructions.push(MirInst::ArrayLit {
            dest: arr,
            elements: vec![recv],
        });
        block.instructions.push(MirInst::BuiltinMethod {
            dest: Some(dest),
            receiver: arr,
            receiver_type: "Array".to_string(),
            method: "len".to_string(),
            args: vec![],
        });
        dest
    }));
}

#[test]
fn codegen_direct_dotted_unwrap_redirects_to_runtime() {
    assert!(aot_compiles("direct_dotted_unwrap", |f| {
        let recv = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("lib__nogc_sync_mut__failsafe__core__FailSafeResult.unwrap"),
            args: vec![recv],
        });
        dest
    }));
}

#[test]
fn codegen_direct_bare_unwrap_redirects_to_runtime() {
    assert!(aot_compiles("direct_bare_unwrap", |f| {
        let recv = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("unwrap"),
            args: vec![recv],
        });
        dest
    }));
}

// Bug fix 14922f8e3cb (flat-nullable unwrap): a bare/dynamic-dispatch
// `.unwrap()`/`.unwrap_or()` used to compile to a call to `rt_enum_payload`,
// which returns tagged-nil for any receiver that is not a genuine
// heap-tagged `Enum` object -- always true for a flat-nullable (`i64?`)
// local holding a present value, since flat-nullables store their payload
// directly rather than as a boxed `Option::Some`. That produced the wrong
// value end-to-end (`i64? = 100` printed `3`, the nil tag pattern, instead
// of `100`). The fix in `codegen/instr/closures_structs.rs`
// (`try_compile_builtin_method_call`) re-routes both method names to
// `rt_unwrap_or_self`, which returns the receiver unchanged when it is not a
// genuine boxed enum -- the correct fallback for a flat-nullable's raw
// payload. See
// doc/08_tracking/bug/seed_interp_flat_nullable_unwrap_wrong_value_2026-07-16.md.
//
// These tests assert on the SYMBOL the compiled object relocates to for the
// runtime call, not just that compilation succeeds (the pre-existing
// `codegen_direct_bare_unwrap_redirects_to_runtime` above only checks the
// latter and would keep passing on a revert). Reverting the fix restores
// the `rt_enum_payload` mapping, which flips both assertions here.
// The bare-name dispatch that ultimately reaches `try_compile_builtin_method_call`
// (the function this fix touches) is `MirInst::MethodCallStatic` with a
// dot-less `func_name` (`compile_method_call_static` in
// `codegen/instr/closures_structs.rs`, its final `else` branch once
// `use_map`/`import_map` cross-module resolution comes up empty) -- NOT
// `MirInst::Call`. A `MirInst::Call { target: CallTarget::from_name("unwrap") }`
// (as used by the pre-existing `codegen_direct_bare_unwrap_redirects_to_runtime`
// above) takes an entirely different path in `compile_call` and simply
// declares an external symbol literally named "unwrap" -- it never reaches
// the method-name-to-runtime-function mapping this bug fixed, so it cannot
// distinguish the fix from its revert (confirmed empirically: relocates to
// symbol "unwrap", not `rt_enum_payload` or `rt_unwrap_or_self`).
#[test]
fn codegen_bare_unwrap_calls_rt_unwrap_or_self_not_rt_enum_payload() {
    let object = aot_object("bare_unwrap_symbol", |f| {
        let recv = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 100 });
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(dest),
            receiver: recv,
            func_name: "unwrap".to_string(),
            args: vec![],
        });
        dest
    });

    assert!(
        object_relocates_to_symbol(&object, "rt_unwrap_or_self"),
        "bare .unwrap() must compile to a call to rt_unwrap_or_self (correct fallback: \
         returns the receiver unchanged for a non-enum/flat-nullable value)"
    );
    assert!(
        !object_relocates_to_symbol(&object, "rt_enum_payload"),
        "bare .unwrap() must NOT compile to rt_enum_payload -- that returns tagged-nil for a \
         flat-nullable's raw payload, which is the reverted (wrong) behavior"
    );
}

// Edge case: `unwrap_or` shares the exact same fallback mapping in
// `try_compile_builtin_method_call` (`"unwrap" | "unwrap_or" => "rt_unwrap_or_self"`).
// A fix that only patched the `unwrap` arm (e.g. a hand-edited partial
// revert) would leave this one still calling `rt_enum_payload`.
#[test]
fn codegen_bare_unwrap_or_calls_rt_unwrap_or_self_not_rt_enum_payload() {
    let object = aot_object("bare_unwrap_or_symbol", |f| {
        let recv = f.new_vreg();
        let fallback = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 100 });
        block.instructions.push(MirInst::ConstInt { dest: fallback, value: 0 });
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(dest),
            receiver: recv,
            func_name: "unwrap_or".to_string(),
            args: vec![fallback],
        });
        dest
    });

    assert!(
        object_relocates_to_symbol(&object, "rt_unwrap_or_self"),
        "bare .unwrap_or() must compile to a call to rt_unwrap_or_self, same as .unwrap()"
    );
    assert!(
        !object_relocates_to_symbol(&object, "rt_enum_payload"),
        "bare .unwrap_or() must NOT compile to rt_enum_payload"
    );
}

// Edge case: chained/nested unwrap (`opt.unwrap().unwrap()`, as would arise
// from a doubly-nested flat-nullable). Both call sites in the chain must
// route through the same fixed symbol -- a partial fix that only patched
// the first dispatch point (e.g. an inlined fast path bypassing the shared
// match arm) would leave the second `unwrap` still on the old mapping.
#[test]
fn codegen_chained_unwrap_calls_use_rt_unwrap_or_self_at_every_step() {
    let object = aot_object("chained_unwrap_symbol", |f| {
        let recv = f.new_vreg();
        let mid = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 100 });
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(mid),
            receiver: recv,
            func_name: "unwrap".to_string(),
            args: vec![],
        });
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(dest),
            receiver: mid,
            func_name: "unwrap".to_string(),
            args: vec![],
        });
        dest
    });

    assert!(
        object_relocates_to_symbol(&object, "rt_unwrap_or_self"),
        "every .unwrap() call in a chain must compile to rt_unwrap_or_self"
    );
    assert!(
        !object_relocates_to_symbol(&object, "rt_enum_payload"),
        "no step of a chained .unwrap() should fall back to rt_enum_payload"
    );
}

#[test]
fn codegen_direct_result_helpers_redirect_to_runtime() {
    assert!(aot_compiles("direct_result_helpers", |f| {
        let recv = f.new_vreg();
        let tmp = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
        block.instructions.push(MirInst::Call {
            dest: Some(tmp),
            target: crate::mir::CallTarget::from_name("lib__nogc_sync_mut__failsafe__core__FailSafeResult.is_err"),
            args: vec![recv],
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("Result.unwrap_err"),
            args: vec![recv],
        });
        dest
    }));
}

#[test]
fn codegen_extern_method_call() {
    assert!(aot_compiles("extern_m", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ExternMethodCall {
            dest: Some(dest),
            receiver: None,
            class_name: "Math".to_string(),
            method_name: "pi".to_string(),
            is_static: true,
            args: vec![],
        });
        dest
    }));
}

// =============================================================================
// Pattern (pattern.rs)
// =============================================================================

#[test]
fn codegen_pattern_test() {
    assert!(aot_compiles("pat_test", |f| {
        let subject = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: subject,
            value: 42,
        });
        block.instructions.push(MirInst::PatternTest {
            dest,
            subject,
            pattern: MirPattern::Literal(MirLiteral::Int(42)),
        });
        dest
    }));
}

#[test]
fn codegen_pattern_bind() {
    assert!(aot_compiles("pat_bind", |f| {
        let subject = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: subject,
            value: 42,
        });
        block.instructions.push(MirInst::PatternBind {
            dest,
            subject,
            binding: PatternBinding {
                name: "x".to_string(),
                path: vec![],
            },
        });
        dest
    }));
}

#[test]
fn codegen_pattern_bind_enum_tuple_field() {
    assert!(aot_compiles("pat_bind_enum_tuple", |f| {
        let subject = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: subject,
            value: 42,
        });
        block.instructions.push(MirInst::PatternBind {
            dest,
            subject,
            binding: PatternBinding {
                name: "field".to_string(),
                path: vec![BindingStep::EnumPayload, BindingStep::TupleIndex(1)],
            },
        });
        dest
    }));
}

// =============================================================================
// Interpreter fallback (interpreter.rs, core.rs)
// =============================================================================

#[test]
fn codegen_interp_call() {
    assert!(aot_compiles("interp_call", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InterpCall {
            dest: Some(dest),
            func_name: "test_func".to_string(),
            args: vec![],
            boxed_result: false,
        });
        dest
    }));
}

#[test]
fn codegen_interp_eval() {
    assert!(aot_compiles("interp_eval", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::InterpEval { dest, expr_index: 0 });
        dest
    }));
}

// =============================================================================
// Async / Generator / Actor (async_ops.rs, actors.rs)
// =============================================================================

#[test]
fn codegen_future_create() {
    assert!(aot_compiles("future_c", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let ret = f.new_vreg();
        f.block_mut(body_block)
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: ret, value: 42 });
        f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::FutureCreate { dest, body_block });
        dest
    }));
}

#[test]
fn codegen_await() {
    assert!(aot_compiles("await_test", |f| {
        let future = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: future, value: 0 });
        block.instructions.push(MirInst::Await { dest, future });
        dest
    }));
}

#[test]
fn codegen_actor_spawn() {
    assert!(aot_compiles("actor_sp", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let ret = f.new_vreg();
        f.block_mut(body_block)
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: ret, value: 0 });
        f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ActorSpawn { dest, body_block });
        dest
    }));
}

#[test]
fn codegen_actor_send() {
    assert!(aot_compiles("actor_send", |f| {
        let actor = f.new_vreg();
        let msg = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: actor, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: msg, value: 42 });
        block.instructions.push(MirInst::ActorSend { actor, message: msg });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_actor_recv() {
    assert!(aot_compiles("actor_recv", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ActorRecv { dest });
        dest
    }));
}

#[test]
fn codegen_generator_create() {
    assert!(aot_compiles("gen_create", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let ret = f.new_vreg();
        f.block_mut(body_block)
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: ret, value: 0 });
        f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GeneratorCreate { dest, body_block });
        dest
    }));
}

#[test]
fn codegen_yield() {
    assert!(aot_compiles("yield_test", |f| {
        let val = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Yield { value: val });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_generator_next() {
    assert!(aot_compiles("gen_next", |f| {
        let gen = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: gen, value: 0 });
        block.instructions.push(MirInst::GeneratorNext { dest, generator: gen });
        dest
    }));
}

// =============================================================================
// Parallel iterators (parallel.rs)
// =============================================================================

#[test]
fn codegen_par_map() {
    assert!(aot_compiles("par_map", |f| {
        let input = f.new_vreg();
        let closure = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: closure,
            value: 0,
        });
        block.instructions.push(MirInst::ParMap {
            dest,
            input,
            closure,
            backend: None,
        });
        dest
    }));
}

#[test]
fn codegen_par_reduce() {
    assert!(aot_compiles("par_reduce", |f| {
        let input = f.new_vreg();
        let initial = f.new_vreg();
        let closure = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: initial,
            value: 0,
        });
        block.instructions.push(MirInst::ConstInt {
            dest: closure,
            value: 0,
        });
        block.instructions.push(MirInst::ParReduce {
            dest,
            input,
            initial,
            closure,
            backend: None,
        });
        dest
    }));
}

#[test]
fn codegen_par_filter() {
    assert!(aot_compiles("par_filter", |f| {
        let input = f.new_vreg();
        let pred = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: pred, value: 0 });
        block.instructions.push(MirInst::ParFilter {
            dest,
            input,
            predicate: pred,
            backend: None,
        });
        dest
    }));
}

#[test]
fn codegen_par_for_each() {
    assert!(aot_compiles("par_each", |f| {
        let input = f.new_vreg();
        let closure = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: closure,
            value: 0,
        });
        block.instructions.push(MirInst::ParForEach {
            input,
            closure,
            backend: None,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

// =============================================================================
// Call instruction (calls.rs) — direct function call
// =============================================================================

#[test]
fn codegen_call() {
    // Call a function defined in the same module
    let mut target = MirFunction::new(
        "add_one".to_string(),
        TypeId::I64,
        simple_parser::ast::Visibility::Public,
    );
    let param = target.new_vreg();
    target.params.push(MirLocal {
        name: "x".to_string(),
        ty: TypeId::I64,
        kind: LocalKind::Parameter,
        is_ghost: false,
    });
    let one = target.new_vreg();
    let result = target.new_vreg();
    let block = target.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: one, value: 1 });
    block.instructions.push(MirInst::BinOp {
        dest: result,
        op: crate::hir::BinOp::Add,
        left: param,
        right: one,
    });
    block.terminator = Terminator::Return(Some(result));

    let mut main = MirFunction::new(
        "call_test".to_string(),
        TypeId::I64,
        simple_parser::ast::Visibility::Public,
    );
    let arg = main.new_vreg();
    let dest = main.new_vreg();
    let block = main.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 41 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("add_one".to_string()),
        args: vec![arg],
    });
    block.terminator = Terminator::Return(Some(dest));

    let mut module = MirModule::new();
    module.functions.push(target);
    module.functions.push(main);
    assert!(aot_compiles_module(module));
}

#[test]
fn codegen_inline_bytes_u8_at_call_accepts_narrow_index() {
    assert!(aot_compiles("inline_bytes_u8_at", |f| {
        let array = f.new_vreg();
        let wide_index = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: wide_index,
            value: -1,
        });
        block.instructions.push(MirInst::UnitNarrow {
            dest: index,
            value: wide_index,
            from_bits: 64,
            to_bits: 8,
            signed: true,
            overflow: UnitOverflowBehavior::Wrap,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_bytes_u8_at"),
            args: vec![array, index],
        });
        dest
    }));
}

#[test]
fn codegen_inline_typed_bytes_u8_unchecked_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_bytes_u8_unchecked", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_bytes_u8_unchecked"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_bytes_u8_unchecked"));
}

#[test]
fn codegen_inline_adler_reduce_does_not_emit_function_symbol() {
    let object = aot_object("inline_adler_reduce", |f| {
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: value,
            value: 131_071,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::Pure("_adler_reduce".to_string()),
            args: vec![value],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "_adler_reduce"));
}

#[test]
fn codegen_inline_bytes_u8_set_call_accepts_narrow_value() {
    assert!(aot_compiles("inline_bytes_u8_set", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let wide_value = f.new_vreg();
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: wide_value,
            value: 255,
        });
        block.instructions.push(MirInst::UnitNarrow {
            dest: value,
            value: wide_value,
            from_bits: 64,
            to_bits: 8,
            signed: false,
            overflow: UnitOverflowBehavior::Wrap,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_bytes_u8_set"),
            args: vec![array, index, value],
        });
        dest
    }));
}

fn object_relocates_to_symbol(object: &[u8], symbol: &str) -> bool {
    use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};

    let file = object::File::parse(object).expect("object parse failed");
    file.sections().any(|section| {
        section.relocations().any(|(_, relocation)| {
            let RelocationTarget::Symbol(index) = relocation.target() else {
                return false;
            };
            file.symbol_by_index(index).and_then(|sym| sym.name()) == Ok(symbol)
        })
    })
}

#[test]
fn codegen_qualified_dict_values_uses_runtime_dispatch() {
    let object = aot_object("qualified_dict_values", |f| {
        let dict = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: dict, value: 0 });
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(dest),
            receiver: dict,
            func_name: "Dict.values".to_string(),
            args: vec![],
        });
        dest
    });

    assert!(object_relocates_to_symbol(&object, "rt_dict_values"));
}

#[test]
fn codegen_inline_spl_f64_to_bits_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_spl_f64_to_bits", |f| {
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstFloat {
            dest: value,
            value: 3.5,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("spl_f64_to_bits"),
            args: vec![value],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "spl_f64_to_bits"));
}

#[test]
fn codegen_inline_rt_len_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_rt_len", |f| {
        let array = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_len"),
            args: vec![array],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_len"));
}

#[test]
fn codegen_inline_rt_array_len_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_rt_array_len", |f| {
        let array = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_array_len"),
            args: vec![array],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_array_len"));
}

#[test]
fn codegen_inline_len_method_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_len_method", |f| {
        let array = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(dest),
            receiver: array,
            func_name: "len".to_string(),
            args: vec![],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_len"));
    assert!(!object_relocates_to_symbol(&object, "rt_array_len"));
}

#[test]
fn codegen_inline_typed_bytes_u32_le_set_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_bytes_u32_le_set", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: value,
            value: 0x0403_0201,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_bytes_u32_le_set"),
            args: vec![array, index, value],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_bytes_u32_le_set"));
}

#[test]
fn codegen_inline_typed_bytes_u8_set_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_bytes_u8_set", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: value, value: 1 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_bytes_u8_set"),
            args: vec![array, index, value],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_bytes_u8_set"));
}

#[test]
fn codegen_inline_typed_words_u32_set_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_words_u32_set", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: value,
            value: 0x8000_0001,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u32_set"),
            args: vec![array, index, value],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_words_u32_set"));
}

#[test]
fn codegen_inline_typed_bytes_u8_push_compiles_with_grow_fallback() {
    assert!(aot_compiles("inline_typed_bytes_u8_push", |f| {
        let array = f.new_vreg();
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: value,
            value: 0x101,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_bytes_u8_push"),
            args: vec![array, value],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_inline_typed_words_u32_push_compiles_with_grow_fallback() {
    assert!(aot_compiles("inline_typed_words_u32_push", |f| {
        let array = f.new_vreg();
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: value,
            value: 0x1_0000_0001,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u32_push"),
            args: vec![array, value],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_inline_typed_words_u64_push_compiles_with_grow_fallback() {
    assert!(aot_compiles("inline_typed_words_u64_push", |f| {
        let array = f.new_vreg();
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: value,
            value: 0x1001,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u64_push"),
            args: vec![array, value],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_inline_typed_words_u64_push_known_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_words_u64_push_known_at", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: value,
            value: 0x1001,
        });
        block.instructions.push(MirInst::Call {
            dest: None,
            target: crate::mir::CallTarget::from_name("rt_typed_words_u64_push_known_at"),
            args: vec![array, index, value],
        });
        value
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_words_u64_push_known_at"));
}

#[test]
fn codegen_inline_typed_words_u64_push_known_data_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_words_u64_push_known_data_at", |f| {
        let header = f.new_vreg();
        let data = f.new_vreg();
        let index = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: header, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: data, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: value,
            value: 0x1001,
        });
        block.instructions.push(MirInst::Call {
            dest: None,
            target: crate::mir::CallTarget::from_name("rt_typed_words_u64_push_known_data_at"),
            args: vec![header, data, index, value],
        });
        value
    });

    assert!(!object_relocates_to_symbol(
        &object,
        "rt_typed_words_u64_push_known_data_at"
    ));
}

#[test]
fn codegen_inline_bytes_u64_le_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_bytes_u64_le_at", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_bytes_u64_le_at"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_bytes_u64_le_at"));
}

#[test]
fn codegen_inline_bytes_u32_le_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_bytes_u32_le_at", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_bytes_u32_le_at"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_bytes_u32_le_at"));
}

#[test]
fn codegen_inline_typed_bytes_u64_le_unchecked_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_bytes_u64_le_unchecked", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_bytes_u64_le_unchecked"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_bytes_u64_le_unchecked"));
}

#[test]
fn codegen_inline_typed_bytes_u32_le_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_bytes_u32_le_at", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_bytes_u32_le_at"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_bytes_u32_le_at"));
}

#[test]
fn codegen_inline_typed_words_u32_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_words_u32_at", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u32_at"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_words_u32_at"));
}

#[test]
fn codegen_inline_typed_words_u64_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_words_u64_at", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u64_at"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_words_u64_at"));
}

#[test]
fn codegen_inline_typed_words_u64_unchecked_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_words_u64_unchecked", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u64_unchecked"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_words_u64_unchecked"));
}

#[test]
fn codegen_inline_typed_words_u64_data_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_words_u64_data_at", |f| {
        let data_ptr = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: data_ptr,
            value: 0,
        });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u64_data_at"),
            args: vec![data_ptr, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_words_u64_data_at"));
}

#[test]
fn codegen_inline_typed_words_u64_data_at_checked_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_words_u64_data_at_checked", |f| {
        let header_ptr = f.new_vreg();
        let data_ptr = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: header_ptr,
            value: 0,
        });
        block.instructions.push(MirInst::ConstInt {
            dest: data_ptr,
            value: 0,
        });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u64_data_at_checked"),
            args: vec![header_ptr, data_ptr, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(
        &object,
        "rt_typed_words_u64_data_at_checked"
    ));
}

#[test]
fn codegen_inline_typed_words_u64_raw_data_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_words_u64_raw_data_at", |f| {
        let data_ptr = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: data_ptr,
            value: 0,
        });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u64_raw_data_at"),
            args: vec![data_ptr, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_words_u64_raw_data_at"));
}

#[test]
fn codegen_inline_numeric_xor_sum_u64_data_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_numeric_xor_sum_u64_data", |f| {
        let data_ptr = f.new_vreg();
        let length = f.new_vreg();
        let xor_value = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: data_ptr,
            value: 4096,
        });
        block.instructions.push(MirInst::ConstInt { dest: length, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: xor_value,
            value: 0,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_numeric_xor_sum_u64_data"),
            args: vec![data_ptr, length, xor_value],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_numeric_xor_sum_u64_data"));
}

#[test]
fn codegen_inline_array_data_ptr_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_array_data_ptr", |f| {
        let array = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_array_data_ptr"),
            args: vec![array],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_array_data_ptr"));
}

#[test]
fn codegen_inline_array_get_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_array_get", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_array_get"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_array_get"));
}

#[test]
fn codegen_inline_array_get_text_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_array_get_text", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_array_get_text"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_array_get_text"));
}

#[test]
fn codegen_inline_array_set_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_array_set", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: value, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_array_set"),
            args: vec![array, index, value],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_array_set"));
}

#[test]
fn codegen_inline_array_set_text_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_array_set_text", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let value = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::ConstString {
            dest: value,
            value: "stored".to_string(),
        });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_array_set_text"),
            args: vec![array, index, value],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_array_set_text"));
}

#[test]
fn codegen_inline_array_set_len_known_text_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_array_set_len_known_text", |f| {
        let array = f.new_vreg();
        let len = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: len, value: 4 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_array_set_len_known_text"),
            args: vec![array, len],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_array_set_len_known_text"));
}

#[test]
fn codegen_typed_words_u64_eq_uses_native_compare() {
    let object = aot_object("typed_words_u64_eq", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let loaded = f.new_vreg();
        let key = f.new_vreg();
        let eq = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(loaded),
            target: crate::mir::CallTarget::from_name("rt_typed_words_u64_at"),
            args: vec![array, index],
        });
        block.instructions.push(MirInst::Cast {
            dest: key,
            source: index,
            from_ty: TypeId::I64,
            to_ty: TypeId::U64,
        });
        block.instructions.push(MirInst::BinOp {
            dest: eq,
            op: BinOp::Eq,
            left: loaded,
            right: key,
        });
        eq
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_words_u64_at"));
    assert!(!object_relocates_to_symbol(&object, "rt_native_eq"));
}

#[test]
fn codegen_text_eq_uses_string_eq_not_native_eq() {
    let object = aot_object("text_eq", |f| {
        let object = f.new_vreg();
        let left_value = f.new_vreg();
        let right_value = f.new_vreg();
        let left = f.new_vreg();
        let right = f.new_vreg();
        let eq = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstString {
            dest: left_value,
            value: "left".to_string(),
        });
        block.instructions.push(MirInst::ConstString {
            dest: right_value,
            value: "right".to_string(),
        });
        block.instructions.push(MirInst::StructInit {
            dest: object,
            type_id: TypeId::I64,
            struct_name: None,
            vtable_symbol: None,
            struct_size: 16,
            field_offsets: vec![0, 8],
            field_types: vec![TypeId::STRING, TypeId::STRING],
            field_values: vec![left_value, right_value],
        });
        block.instructions.push(MirInst::FieldGet {
            dest: left,
            object,
            owner_name: None,
            owner_has_vtable: None,
            byte_offset: 0,
            field_type: TypeId::STRING,
        });
        block.instructions.push(MirInst::FieldGet {
            dest: right,
            object,
            owner_name: None,
            owner_has_vtable: None,
            byte_offset: 8,
            field_type: TypeId::STRING,
        });
        block.instructions.push(MirInst::BinOp {
            dest: eq,
            op: BinOp::Eq,
            left,
            right,
        });
        eq
    });

    assert!(object_relocates_to_symbol(&object, "rt_string_eq"));
    assert!(!object_relocates_to_symbol(&object, "rt_native_eq"));
}

#[test]
fn codegen_inline_typed_bytes_u64_le_at_does_not_emit_runtime_symbol() {
    let object = aot_object("inline_typed_bytes_u64_le_at", |f| {
        let array = f.new_vreg();
        let index = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: array, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: index, value: 0 });
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::from_name("rt_typed_bytes_u64_le_at"),
            args: vec![array, index],
        });
        dest
    });

    assert!(!object_relocates_to_symbol(&object, "rt_typed_bytes_u64_le_at"));
}

// Regression test for S63 fix: LLVM backend method-call→rt_* lowering (stage2 unblock)
// These tests assert that previously-missing string methods now properly relocate to
// rt_* symbols instead of emitting unresolved literal method names (e.g., "str.bytes").
// Verifies the fix in src/codegen/llvm/functions.rs that added missing method mappings.
// Note: "length" alias is verified in the mapping but not tested here because rt_len
// is inlined for simple cases, so there would be no runtime relocation in the object file.
#[test]
fn codegen_string_bytes_method_calls_rt_string_bytes() {
    let object = aot_object("string_bytes_method", |f| {
        let receiver = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: receiver, value: 1 });
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(dest),
            receiver,
            func_name: "bytes".to_string(),
            args: vec![],
        });
        dest
    });
    assert!(
        object_relocates_to_symbol(&object, "rt_string_bytes"),
        "string.bytes() must compile to rt_string_bytes, not unresolved 'bytes' symbol"
    );
}

#[test]
fn codegen_string_chars_method_calls_rt_string_chars() {
    let object = aot_object("string_chars_method", |f| {
        let receiver = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: receiver, value: 1 });
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(dest),
            receiver,
            func_name: "chars".to_string(),
            args: vec![],
        });
        dest
    });
    assert!(
        object_relocates_to_symbol(&object, "rt_string_chars"),
        "string.chars() must compile to rt_string_chars, not unresolved 'chars' symbol"
    );
}
