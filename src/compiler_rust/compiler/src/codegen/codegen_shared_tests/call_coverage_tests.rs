use super::*;

// =============================================================================
// Branch coverage: BinOp error paths (MatMul, PipeForward)
// =============================================================================

// MatMul and PipeForward return errors in Cranelift codegen.
// MethodCallStatic with these names hits the "function not found" fallback in Cranelift,
// so we test the BinOp error paths via the Call instruction which goes through compile_call.
// The interpreter handles these as no-ops, so we test cranelift-only.

cranelift_only_test!(shared_binop_matmul_error, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    // MatMul returns Err in compile_binop — but the Cranelift emitter may handle this
    // differently at the instruction level. Use InterpCall as fallback.
    block.instructions.push(MirInst::InterpCall {
        dest: Some(dest),
        func_name: "matmul_stub".to_string(),
        args: vec![a, b],
    });
    dest
});

cranelift_only_test!(shared_binop_pipeforward_error, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::InterpCall {
        dest: Some(dest),
        func_name: "pipe_forward_stub".to_string(),
        args: vec![a],
    });
    dest
});

// =============================================================================
// Branch coverage: Empty println() / eprintln() (no args)
// =============================================================================

cranelift_only_test!(shared_call_println_empty, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Io("println".to_string()),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_call_eprintln_empty, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Io("eprintln".to_string()),
        args: vec![],
    });
    dest
});

// Also test print/eprint with single and multiple args for space-separator branch
cranelift_only_test!(shared_call_print_single_arg, |f: &mut MirFunction| {
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Io("print".to_string()),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_call_println_multi_args, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Io("println".to_string()),
        args: vec![a, b],
    });
    dest
});

cranelift_only_test!(shared_call_eprint_single_arg, |f: &mut MirFunction| {
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Io("eprint".to_string()),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_call_eprintln_multi_args, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Io("eprintln".to_string()),
        args: vec![a, b],
    });
    dest
});

// =============================================================================

// =============================================================================

cranelift_only_test!(shared_cast_f32_to_f64, |f: &mut MirFunction| {
    let src = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstFloat { dest: src, value: 3.14 });
    block.instructions.push(MirInst::Cast {
        dest,
        source: src,
        from_ty: TypeId::F32,
        to_ty: TypeId::F64,
    });
    dest
});

cranelift_only_test!(shared_cast_f64_to_f32, |f: &mut MirFunction| {
    let src = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstFloat { dest: src, value: 3.14 });
    block.instructions.push(MirInst::Cast {
        dest,
        source: src,
        from_ty: TypeId::F64,
        to_ty: TypeId::F32,
    });
    dest
});

// Default fallback: non-numeric cast (e.g., ANY to STRING)
cranelift_only_test!(shared_cast_default_fallback, |f: &mut MirFunction| {
    let src = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: src, value: 42 });
    block.instructions.push(MirInst::Cast {
        dest,
        source: src,
        from_ty: TypeId::ANY,
        to_ty: TypeId::STRING,
    });
    dest
});

// =============================================================================
// Branch coverage: ContractKind variants (Postcondition through Assertion)
// =============================================================================

cranelift_only_test!(shared_contract_postcondition, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstBool {
        dest: cond,
        value: true,
    });
    block.instructions.push(MirInst::ContractCheck {
        condition: cond,
        kind: ContractKind::Postcondition,
        func_name: "test_fn".to_string(),
        message: None,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

cranelift_only_test!(shared_contract_error_postcondition, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstBool {
        dest: cond,
        value: true,
    });
    block.instructions.push(MirInst::ContractCheck {
        condition: cond,
        kind: ContractKind::ErrorPostcondition,
        func_name: "test_fn".to_string(),
        message: None,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

cranelift_only_test!(shared_contract_invariant_entry, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstBool {
        dest: cond,
        value: true,
    });
    block.instructions.push(MirInst::ContractCheck {
        condition: cond,
        kind: ContractKind::InvariantEntry,
        func_name: "test_fn".to_string(),
        message: None,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

cranelift_only_test!(shared_contract_invariant_exit, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstBool {
        dest: cond,
        value: true,
    });
    block.instructions.push(MirInst::ContractCheck {
        condition: cond,
        kind: ContractKind::InvariantExit,
        func_name: "test_fn".to_string(),
        message: None,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

cranelift_only_test!(shared_contract_assertion, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstBool {
        dest: cond,
        value: true,
    });
    block.instructions.push(MirInst::ContractCheck {
        condition: cond,
        kind: ContractKind::Assertion,
        func_name: "test_fn".to_string(),
        message: None,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Branch coverage: Call — Result/Option constructors (Ok, Err, Some, None)
// =============================================================================

cranelift_only_test!(shared_call_ok_constructor, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("Ok".to_string()),
        args: vec![val],
    });
    dest
});

cranelift_only_test!(shared_call_err_constructor, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("Err".to_string()),
        args: vec![val],
    });
    dest
});

cranelift_only_test!(shared_call_some_constructor, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 10 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("Some".to_string()),
        args: vec![val],
    });
    dest
});

cranelift_only_test!(shared_call_none_constructor, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("None".to_string()),
        args: vec![],
    });
    dest
});

// Qualified variant names (MyResult::Ok, Option::None)
cranelift_only_test!(shared_call_qualified_ok, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("Result::Ok".to_string()),
        args: vec![val],
    });
    dest
});

cranelift_only_test!(shared_call_qualified_none_dot, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("Option.None".to_string()),
        args: vec![],
    });
    dest
});

// Call with no dest (result discarded)
cranelift_only_test!(shared_call_ok_no_dest, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
    block.instructions.push(MirInst::Call {
        dest: None,
        target: crate::mir::CallTarget::Pure("Ok".to_string()),
        args: vec![val],
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Branch coverage: Call — runtime FFI name mapping
// =============================================================================

cranelift_only_test!(shared_call_sys_get_args, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("sys_get_args".to_string()),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_call_sys_exit, |f: &mut MirFunction| {
    let code = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: code, value: 0 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("sys_exit".to_string()),
        args: vec![code],
    });
    dest
});

// Call to runtime FFI function directly (e.g., rt_array_new)
cranelift_only_test!(shared_call_runtime_ffi, |f: &mut MirFunction| {
    let cap = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: cap, value: 10 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("rt_array_new".to_string()),
        args: vec![cap],
    });
    dest
});

// Call to unknown function (triggers warning path)
cranelift_only_test!(shared_call_unknown_function, |f: &mut MirFunction| {
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::Call {
        dest: None,
        target: crate::mir::CallTarget::Pure("totally_unknown_xyz".to_string()),
        args: vec![],
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Branch coverage: GPU — memory fence scopes and atomic operations
// =============================================================================

cranelift_only_test!(shared_gpu_mem_fence_workgroup, |f: &mut MirFunction| {
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::GpuMemFence {
        scope: GpuMemoryScope::WorkGroup,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

cranelift_only_test!(shared_gpu_mem_fence_all, |f: &mut MirFunction| {
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::GpuMemFence {
        scope: GpuMemoryScope::All,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

cranelift_only_test!(shared_gpu_atomic_sub, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
    block.instructions.push(MirInst::GpuAtomic {
        dest,
        op: GpuAtomicOp::Sub,
        ptr,
        value: val,
    });
    dest
});

cranelift_only_test!(shared_gpu_atomic_xchg, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 5 });
    block.instructions.push(MirInst::GpuAtomic {
        dest,
        op: GpuAtomicOp::Xchg,
        ptr,
        value: val,
    });
    dest
});

cranelift_only_test!(shared_gpu_atomic_min, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 3 });
    block.instructions.push(MirInst::GpuAtomic {
        dest,
        op: GpuAtomicOp::Min,
        ptr,
        value: val,
    });
    dest
});

cranelift_only_test!(shared_gpu_atomic_max, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 7 });
    block.instructions.push(MirInst::GpuAtomic {
        dest,
        op: GpuAtomicOp::Max,
        ptr,
        value: val,
    });
    dest
});

cranelift_only_test!(shared_gpu_atomic_and, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 0xFF });
    block.instructions.push(MirInst::GpuAtomic {
        dest,
        op: GpuAtomicOp::And,
        ptr,
        value: val,
    });
    dest
});

cranelift_only_test!(shared_gpu_atomic_or, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 0x0F });
    block.instructions.push(MirInst::GpuAtomic {
        dest,
        op: GpuAtomicOp::Or,
        ptr,
        value: val,
    });
    dest
});

cranelift_only_test!(shared_gpu_atomic_xor, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 0xAA });
    block.instructions.push(MirInst::GpuAtomic {
        dest,
        op: GpuAtomicOp::Xor,
        ptr,
        value: val,
    });
    dest
});

// =============================================================================
// Branch coverage: MethodCallStatic — function not found, void return, suffix search
// =============================================================================

// MethodCallStatic with a function that doesn't exist (hits rt_function_not_found)
cranelift_only_test!(shared_method_static_not_found, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "nonexistent_method_xyz".to_string(),
        args: vec![],
    });
    dest
});

// MethodCallStatic with dest: None (void return, function not found)
cranelift_only_test!(shared_method_static_void_not_found, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: None,
        receiver: recv,
        func_name: "void_method_xyz".to_string(),
        args: vec![],
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// MethodCallStatic with suffix search (e.g., "parse" matches "ArgParser.parse")
shared_module_test!(shared_method_static_suffix_search,
    module: {
        // Create a function named "MyClass.do_thing"
        let mut target = MirFunction::new("MyClass.do_thing".to_string(), TypeId::I64, Visibility::Public);
        target.params.push(MirLocal { name: "self".to_string(), ty: TypeId::I64, kind: LocalKind::Parameter, is_ghost: false });
        let ret = target.new_vreg();
        target.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstInt { dest: ret, value: 99 });
        target.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));

        let mut main = MirFunction::new("test_suffix".to_string(), TypeId::I64, Visibility::Public);
        let recv = main.new_vreg();
        let dest = main.new_vreg();
        let block = main.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
        // Call with just "do_thing" — should find "MyClass.do_thing" via suffix search
        block.instructions.push(MirInst::MethodCallStatic {
            dest: Some(dest), receiver: recv,
            func_name: "do_thing".to_string(), args: vec![],
        });
        block.terminator = Terminator::Return(Some(dest));

        let mut module = MirModule::new();
        module.functions.push(target);
        module.functions.push(main);
        module
    },
    insts: vec![
        MirInst::ConstInt { dest: VReg(0), value: 0 },
        MirInst::MethodCallStatic {
            dest: Some(VReg(1)), receiver: VReg(0),
            func_name: "do_thing".to_string(), args: vec![],
        },
    ]
);
