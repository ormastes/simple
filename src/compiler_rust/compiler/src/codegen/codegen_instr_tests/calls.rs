use super::{aot_compiles, aot_compiles_module};
use crate::hir::TypeId;
use crate::mir::{
    BlockId, LocalKind, MirFunction, MirInst, MirLiteral, MirLocal, MirModule, MirPattern, PatternBinding, Terminator,
};

// =============================================================================
// Closure / IndirectCall (closures_structs.rs)
// =============================================================================

#[test]
fn codegen_closure_create_and_indirect_call() {
    // Need a callable function in the module for the closure
    let mut func = MirFunction::new("identity".to_string(), TypeId::I64, simple_parser::ast::Visibility::Public);
    let param_vreg = func.new_vreg();
    func.params.push(MirLocal {
        name: "x".to_string(),
        ty: TypeId::I64,
        kind: LocalKind::Parameter,
        is_ghost: false,
    });
    func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(param_vreg));

    let mut main = MirFunction::new("clos_test".to_string(), TypeId::I64, simple_parser::ast::Visibility::Public);
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
    let mut target = MirFunction::new("Point::get_x".to_string(), TypeId::I64, simple_parser::ast::Visibility::Public);
    let self_vreg = target.new_vreg();
    target.params.push(MirLocal {
        name: "self".to_string(),
        ty: TypeId::I64,
        kind: LocalKind::Parameter,
        is_ghost: false,
    });
    target.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(self_vreg));

    let mut main = MirFunction::new("method_static".to_string(), TypeId::I64, simple_parser::ast::Visibility::Public);
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
    let mut target = MirFunction::new("add_one".to_string(), TypeId::I64, simple_parser::ast::Visibility::Public);
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

    let mut main = MirFunction::new("call_test".to_string(), TypeId::I64, simple_parser::ast::Visibility::Public);
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
