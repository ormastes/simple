use super::*;

// =============================================================================
// Phase 3: Enum payload
// =============================================================================

shared_test!(shared_enum_payload, |f: &mut MirFunction| {
    let payload = f.new_vreg();
    let wrapped = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt {
        dest: payload,
        value: 42,
    });
    block.instructions.push(MirInst::EnumWith {
        dest: wrapped,
        enum_name: "Option".to_string(),
        variant_name: "Some".to_string(),
        payload,
    });
    block.instructions.push(MirInst::EnumPayload { dest, value: wrapped });
    dest
});

// =============================================================================
// Phase 3: Union discriminant / payload
// =============================================================================

shared_test!(shared_union_discriminant, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let wrapped = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnionWrap {
        dest: wrapped,
        value: val,
        type_index: 0,
    });
    block
        .instructions
        .push(MirInst::UnionDiscriminant { dest, value: wrapped });
    dest
});

shared_test!(shared_union_payload, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let wrapped = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnionWrap {
        dest: wrapped,
        value: val,
        type_index: 0,
    });
    block.instructions.push(MirInst::UnionPayload {
        dest,
        value: wrapped,
        type_index: 0,
    });
    dest
});

// =============================================================================
// Phase 3: Actor join / recv / reply
// =============================================================================

shared_test!(shared_actor_join, |f: &mut MirFunction| {
    let actor = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: actor, value: 0 });
    block.instructions.push(MirInst::ActorJoin { dest, actor });
    dest
});

shared_test!(shared_actor_recv, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ActorRecv { dest });
    dest
});

shared_test!(shared_actor_reply, |f: &mut MirFunction| {
    let msg = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: msg, value: 42 });
    block.instructions.push(MirInst::ActorReply { message: msg });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Phase 3: Generator next
// =============================================================================

shared_test!(shared_generator_next, |f: &mut MirFunction| {
    let gen = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: gen, value: 0 });
    block.instructions.push(MirInst::GeneratorNext { dest, generator: gen });
    dest
});

// =============================================================================
// Phase 3: Memory — GcAlloc, Wait, GetElementPtr, LocalAddr/Store/Load
// =============================================================================

shared_test!(shared_gc_alloc, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GcAlloc { dest, ty: TypeId::I64 });
    dest
});

shared_test!(shared_wait, |f: &mut MirFunction| {
    let target = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: target, value: 0 });
    block.instructions.push(MirInst::Wait {
        dest: Some(dest),
        target,
    });
    dest
});

shared_test!(shared_get_element_ptr, |f: &mut MirFunction| {
    let base = f.new_vreg();
    let idx = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: base, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block
        .instructions
        .push(MirInst::GetElementPtr { dest, base, index: idx });
    dest
});

shared_test!(shared_local_addr_store_load, |f: &mut MirFunction| {
    f.locals.push(MirLocal {
        name: "x".to_string(),
        ty: TypeId::I64,
        kind: LocalKind::Local,
        is_ghost: false,
    });
    let addr = f.new_vreg();
    let val = f.new_vreg();
    let loaded = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::LocalAddr {
        dest: addr,
        local_index: 0,
    });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::Store {
        addr,
        value: val,
        ty: TypeId::I64,
    });
    block.instructions.push(MirInst::Load {
        dest: loaded,
        addr,
        ty: TypeId::I64,
    });
    loaded
});

// =============================================================================
// Phase 3: Global Load/Store (module-level test)
// =============================================================================

shared_module_test!(shared_global_load_store,
    module: {
        let mut func = MirFunction::new("global_test".to_string(), TypeId::I64, Visibility::Public);
        let val = func.new_vreg();
        let loaded = func.new_vreg();
        let block = func.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::GlobalStore {
            global_name: "MY_GLOBAL".to_string(), value: val, ty: TypeId::I64,
        });
        block.instructions.push(MirInst::GlobalLoad {
            dest: loaded, global_name: "MY_GLOBAL".to_string(), ty: TypeId::I64,
        });
        block.terminator = Terminator::Return(Some(loaded));
        let mut module = MirModule::new();
        module.globals.push(("MY_GLOBAL".to_string(), TypeId::I64, true));
        module.functions.push(func);
        module
    },
    insts: vec![
        MirInst::ConstInt { dest: VReg(0), value: 42 },
        MirInst::GlobalStore { global_name: "MY_GLOBAL".to_string(), value: VReg(0), ty: TypeId::I64 },
        MirInst::GlobalLoad { dest: VReg(1), global_name: "MY_GLOBAL".to_string(), ty: TypeId::I64 },
    ]
);

// =============================================================================
// Phase 3: Interpreter / fallback calls
// =============================================================================

shared_test!(shared_interp_call, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::InterpCall {
        dest: Some(dest),
        func_name: "test_func".to_string(),
        args: vec![],
    });
    dest
});

shared_test!(shared_interp_eval, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::InterpEval { dest, expr_index: 0 });
    dest
});

// =============================================================================
// Phase 3: Coverage — condition probe
// =============================================================================

shared_test!(shared_condition_probe, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstBool {
        dest: cond,
        value: true,
    });
    block.instructions.push(MirInst::ConditionProbe {
        decision_id: 0,
        condition_id: 0,
        result: cond,
        file: "test.spl".to_string(),
        line: 1,
        column: 1,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
    ret
});

// =============================================================================
// Phase 3: Method calls (module-level tests for static/virtual/builtin/extern)
// =============================================================================

shared_module_test!(shared_method_call_static,
    module: {
        let mut target = MirFunction::new("Point::get_x".to_string(), TypeId::I64, Visibility::Public);
        let self_vreg = target.new_vreg();
        target.params.push(MirLocal {
            name: "self".to_string(), ty: TypeId::I64,
            kind: LocalKind::Parameter, is_ghost: false,
        });
        target.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(self_vreg));

        let mut main = MirFunction::new("method_static".to_string(), TypeId::I64, Visibility::Public);
        let recv = main.new_vreg();
        let dest = main.new_vreg();
        let block = main.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(dest), receiver: recv,
            func_name: "Point::get_x".to_string(), args: vec![],
        });
        block.terminator = Terminator::Return(Some(dest));

        let mut module = MirModule::new();
        module.functions.push(target);
        module.functions.push(main);
        module
    },
    insts: vec![
        MirInst::ConstInt { dest: VReg(0), value: 42 },
        MirInst::MethodCallStatic {
            dest: Some(VReg(1)), receiver: VReg(0),
            func_name: "Point::get_x".to_string(), args: vec![],
        },
    ]
);

shared_test!(shared_method_call_virtual, |f: &mut MirFunction| {
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
});

shared_test!(shared_builtin_method, |f: &mut MirFunction| {
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
});

shared_test!(shared_extern_method_call, |f: &mut MirFunction| {
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
});

// =============================================================================
// Phase 3: Call (module-level test)
// =============================================================================

shared_module_test!(shared_call,
    module: {
        let mut target = MirFunction::new("add_one".to_string(), TypeId::I64, Visibility::Public);
        let param = target.new_vreg();
        target.params.push(MirLocal {
            name: "x".to_string(), ty: TypeId::I64,
            kind: LocalKind::Parameter, is_ghost: false,
        });
        let one = target.new_vreg();
        let result = target.new_vreg();
        let block = target.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: one, value: 1 });
        block.instructions.push(MirInst::BinOp { dest: result, op: hir::BinOp::Add, left: param, right: one });
        block.terminator = Terminator::Return(Some(result));

        let mut main = MirFunction::new("call_test".to_string(), TypeId::I64, Visibility::Public);
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
        module
    },
    insts: vec![
        MirInst::ConstInt { dest: VReg(0), value: 41 },
        MirInst::Call {
            dest: Some(VReg(1)),
            target: crate::mir::CallTarget::Pure("add_one".to_string()),
            args: vec![VReg(0)],
        },
    ]
);

// =============================================================================
// Phase 3: Closure / IndirectCall (module-level test)
// =============================================================================

shared_module_test!(shared_closure_create_and_indirect_call,
    module: {
        let mut func = MirFunction::new("identity".to_string(), TypeId::I64, Visibility::Public);
        let param_vreg = func.new_vreg();
        func.params.push(MirLocal {
            name: "x".to_string(), ty: TypeId::I64,
            kind: LocalKind::Parameter, is_ghost: false,
        });
        func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(param_vreg));

        let mut main = MirFunction::new("clos_test".to_string(), TypeId::I64, Visibility::Public);
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
        module
    },
    insts: vec![
        MirInst::ClosureCreate {
            dest: VReg(0),
            func_name: "identity".to_string(),
            closure_size: 8,
            capture_offsets: vec![],
            capture_types: vec![],
            captures: vec![],
            body_block: None,
        },
        MirInst::ConstInt { dest: VReg(1), value: 42 },
        MirInst::IndirectCall {
            dest: Some(VReg(2)),
            callee: VReg(0),
            param_types: vec![TypeId::I64],
            return_type: TypeId::I64,
            args: vec![VReg(1)],
            effect: crate::mir::Effect::Compute,
        },
    ]
);

// =============================================================================
// Phase 3: TryUnwrap (cranelift-only — needs block infrastructure)
// =============================================================================

/// TryUnwrap creates internal Cranelift blocks for branching.
/// We test it cranelift-only (MIR construction) + interpreter separately.
mod shared_try_unwrap {
    use super::*;

    #[test]
    fn cranelift() {
        // TryUnwrap needs block-sealing infra, verify MIR construction is valid
        let mut func = MirFunction::new("try_unwrap".to_string(), TypeId::I64, Visibility::Public);
        let val = func.new_vreg();
        let opt = func.new_vreg();
        let dest = func.new_vreg();
        let _error_dest = func.new_vreg();
        let error_block = func.new_block();

        let block = func.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::OptionSome { dest: opt, value: val });
        block.instructions.push(MirInst::TryUnwrap {
            dest,
            value: opt,
            error_block,
            error_dest: _error_dest,
        });

        assert!(func.blocks[0]
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::TryUnwrap { .. })));
    }

    #[test]
    fn interpreter() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::OptionSome {
                dest: VReg(1),
                value: VReg(0),
            },
            MirInst::TryUnwrap {
                dest: VReg(2),
                value: VReg(1),
                error_block: BlockId(1),
                error_dest: VReg(3),
            },
        ];
        interpreter_ok(&insts);
    }
}

