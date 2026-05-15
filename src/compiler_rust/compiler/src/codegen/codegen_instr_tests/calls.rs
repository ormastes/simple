use super::{aot_compiles, aot_compiles_module, aot_object};
use crate::hir::{BinOp, TypeId};
use crate::mir::{
    BlockId, LocalKind, MirFunction, MirInst, MirLiteral, MirLocal, MirModule, MirPattern, PatternBinding, Terminator,
    UnitOverflowBehavior,
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
