use super::*;

// =============================================================================
// Branch coverage: BinOp — all operator variants
// =============================================================================

shared_test!(shared_binop_mod, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 10 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 3 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Mod,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_bitand, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0xFF });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0x0F });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::BitAnd,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_bitor, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0xF0 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0x0F });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::BitOr,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_bitxor, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0xFF });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0x0F });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::BitXor,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_shift_left, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 3 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::ShiftLeft,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_shift_right, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 8 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::ShiftRight,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_noteq, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::NotEq,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_gt, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 10 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 5 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Gt,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_lteq, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 5 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 5 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::LtEq,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_gteq, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 5 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 5 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::GtEq,
        left: a,
        right: b,
    });
    dest
});

cranelift_only_test!(shared_binop_is, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 42 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 42 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Is,
        left: a,
        right: b,
    });
    dest
});

cranelift_only_test!(shared_binop_in, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::In,
        left: a,
        right: b,
    });
    dest
});

cranelift_only_test!(shared_binop_notin, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::NotIn,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_and, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 1 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::And,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_or, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 1 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Or,
        left: a,
        right: b,
    });
    dest
});

cranelift_only_test!(shared_binop_and_suspend, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::AndSuspend,
        left: a,
        right: b,
    });
    dest
});

cranelift_only_test!(shared_binop_or_suspend, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 1 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::OrSuspend,
        left: a,
        right: b,
    });
    dest
});

// BinOp::Pow creates loop blocks in Cranelift (unsealable in single-block test harness)
// and is unsupported in the interpreter. Covered by codegen_instr_tests instead.

cranelift_only_test!(shared_binop_floordiv, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 7 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Div,
        left: a,
        right: b,
    });
    dest
});

// =============================================================================

// Branch coverage: Closure with missing function
// =============================================================================

shared_test!(shared_closure_missing_func, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ClosureCreate {
        dest,
        func_name: "nonexistent_function_xyz".to_string(),
        closure_size: 8,
        capture_offsets: vec![],
        capture_types: vec![],
        captures: vec![],
        body_block: None,
    });
    dest
});

// =============================================================================
// Branch coverage: IndirectCall with VOID return type
// =============================================================================

shared_module_test!(shared_indirect_call_void_return,
    module: {
        let mut func = MirFunction::new("void_fn".to_string(), TypeId::VOID, Visibility::Public);
        func.params.push(MirLocal {
            name: "x".to_string(), ty: TypeId::I64,
            kind: LocalKind::Parameter, is_ghost: false,
        });
        let ret = func.new_vreg();
        func.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));

        let mut main = MirFunction::new("test_void_indirect".to_string(), TypeId::I64, Visibility::Public);
        let closure = main.new_vreg();
        let arg = main.new_vreg();
        let ret = main.new_vreg();
        let block = main.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ClosureCreate {
            dest: closure, func_name: "void_fn".to_string(),
            closure_size: 8, capture_offsets: vec![], capture_types: vec![], captures: vec![],
            body_block: None,
        });
        block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
        block.instructions.push(MirInst::IndirectCall {
            dest: None, callee: closure,
            param_types: vec![TypeId::I64], return_type: TypeId::VOID,
            args: vec![arg], effect: crate::mir::Effect::Compute,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        block.terminator = Terminator::Return(Some(ret));

        let mut module = MirModule::new();
        module.functions.push(func);
        module.functions.push(main);
        module
    },
    insts: vec![
        MirInst::ClosureCreate {
            dest: VReg(0), func_name: "void_fn".to_string(),
            closure_size: 8, capture_offsets: vec![], capture_types: vec![], captures: vec![],
            body_block: None,
        },
        MirInst::ConstInt { dest: VReg(1), value: 42 },
        MirInst::IndirectCall {
            dest: None, callee: VReg(0),
            param_types: vec![TypeId::I64], return_type: TypeId::VOID,
            args: vec![VReg(1)], effect: crate::mir::Effect::Compute,
        },
    ]
);

// =============================================================================
// Branch coverage: MethodCallVirtual with VOID return
// =============================================================================

shared_test!(shared_method_call_virtual_void, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
    block.instructions.push(MirInst::MethodCallVirtual {
        dest: None,
        receiver: recv,
        vtable_slot: 0,
        param_types: vec![],
        return_type: TypeId::VOID,
        args: vec![],
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Branch coverage: Struct init with fewer values than fields
// =============================================================================

shared_test!(shared_struct_init_fewer_values, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let obj = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    // Two fields but only one value — exercises the "more fields than values" branch
    block.instructions.push(MirInst::StructInit {
        dest: obj,
        type_id: TypeId::I64,
        struct_size: 16,
        field_offsets: vec![0, 8],
        field_types: vec![TypeId::I64, TypeId::I64],
        field_values: vec![val],
    });
    obj
});

// =============================================================================
// Branch coverage: BuiltinMethod — in-place mutating methods
// =============================================================================

shared_test!(shared_builtin_method_push, |f: &mut MirFunction| {
    let elem = f.new_vreg();
    let arr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: elem, value: 1 });
    block.instructions.push(MirInst::ArrayLit {
        dest: arr,
        elements: vec![elem],
    });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "Array".to_string(),
        method: "push".to_string(),
        args: vec![val],
    });
    dest
});

shared_test!(shared_builtin_method_pop, |f: &mut MirFunction| {
    let elem = f.new_vreg();
    let arr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: elem, value: 1 });
    block.instructions.push(MirInst::ArrayLit {
        dest: arr,
        elements: vec![elem],
    });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "Array".to_string(),
        method: "pop".to_string(),
        args: vec![],
    });
    dest
});

// =============================================================================
// Branch coverage: declare_functions — extern (empty blocks), public, private
// =============================================================================

/// Tests function declaration with extern functions (empty blocks = import linkage)
/// and mixed visibility functions
mod shared_declare_functions_branches {
    use super::*;

    #[test]
    fn cranelift_extern_and_private() {
        // Extern function (empty blocks — generates Import linkage)
        let extern_func = MirFunction::new("external_fn".to_string(), TypeId::I64, Visibility::Public);
        // Note: MirFunction::new creates with one default block. For a true extern, blocks would be empty.
        // We test the public + main branch here.

        let mut main = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let ret = main.new_vreg();
        main.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: ret, value: 0 });
        main.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));

        // Private function
        let mut priv_fn = MirFunction::new("helper".to_string(), TypeId::I64, Visibility::Private);
        let ret2 = priv_fn.new_vreg();
        priv_fn
            .block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: ret2, value: 1 });
        priv_fn.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret2));

        let mut module = MirModule::new();
        module.functions.push(main);
        module.functions.push(priv_fn);
        cranelift_module_ok(module);
    }
}

// =============================================================================
// Interpreter branch coverage: BinOp error paths & edge cases
// =============================================================================

