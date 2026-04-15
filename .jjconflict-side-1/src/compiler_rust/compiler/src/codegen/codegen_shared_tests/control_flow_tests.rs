use super::*;

// =============================================================================
// Branch coverage: Global variables (GlobalLoad / GlobalStore via module test)
// =============================================================================

mod shared_global_variables {
    use super::*;

    #[test]
    fn cranelift() {
        let mut main = MirFunction::new("test_globals".to_string(), TypeId::I64, Visibility::Public);
        let val = main.new_vreg();
        let loaded = main.new_vreg();
        let block = main.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::GlobalStore {
            global_name: "my_global".to_string(),
            value: val,
            ty: TypeId::I64,
        });
        block.instructions.push(MirInst::GlobalLoad {
            dest: loaded,
            global_name: "my_global".to_string(),
            ty: TypeId::I64,
        });
        block.terminator = Terminator::Return(Some(loaded));

        let mut module = MirModule::new();
        module.globals.push(("my_global".to_string(), TypeId::I64, true));
        module.functions.push(main);
        cranelift_module_ok(module);
    }

    #[test]
    fn interpreter() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::GlobalStore {
                global_name: "my_global".to_string(),
                value: VReg(0),
                ty: TypeId::I64,
            },
            MirInst::GlobalLoad {
                dest: VReg(1),
                global_name: "my_global".to_string(),
                ty: TypeId::I64,
            },
        ];
        let val = interpreter_value(&insts, VReg(1));
        assert_eq!(val, 42);
    }
}

// =============================================================================
// Branch coverage: Call — user-defined function with void return (empty results)
// =============================================================================

shared_module_test!(shared_call_user_void_return,
    module: {
        let mut void_fn = MirFunction::new("void_user_fn".to_string(), TypeId::VOID, Visibility::Public);
        let ret = void_fn.new_vreg();
        void_fn.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        void_fn.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(None);

        let mut main = MirFunction::new("test_call_void".to_string(), TypeId::I64, Visibility::Public);
        let dest = main.new_vreg();
        let ret = main.new_vreg();
        let block = main.block_mut(BlockId(0)).unwrap();
        // Call void function with dest — should not insert result (results.is_empty())
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: crate::mir::CallTarget::Pure("void_user_fn".to_string()),
            args: vec![],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        block.terminator = Terminator::Return(Some(ret));

        let mut module = MirModule::new();
        module.functions.push(void_fn);
        module.functions.push(main);
        module
    },
    insts: vec![
        MirInst::Call {
            dest: Some(VReg(0)),
            target: crate::mir::CallTarget::Pure("void_user_fn".to_string()),
            args: vec![],
        },
    ]
);

// =============================================================================
// Branch coverage: Interpreter — additional branches
// =============================================================================

mod interpreter_coverage_extras {
    use super::*;

    // Cast: float-to-int
    #[test]
    fn cast_float_to_int() {
        let insts = vec![
            MirInst::ConstFloat {
                dest: VReg(0),
                value: 3.14,
            },
            MirInst::Cast {
                dest: VReg(1),
                source: VReg(0),
                from_ty: TypeId::F64,
                to_ty: TypeId::I64,
            },
        ];
        interpreter_ok(&insts);
    }

    // Cast: int-to-float
    #[test]
    fn cast_int_to_float() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::Cast {
                dest: VReg(1),
                source: VReg(0),
                from_ty: TypeId::I64,
                to_ty: TypeId::F64,
            },
        ];
        interpreter_ok(&insts);
    }

    // Cast: f32-to-f64 (fpromote equivalent)
    #[test]
    fn cast_f32_to_f64() {
        let insts = vec![
            MirInst::ConstFloat {
                dest: VReg(0),
                value: 1.5,
            },
            MirInst::Cast {
                dest: VReg(1),
                source: VReg(0),
                from_ty: TypeId::F32,
                to_ty: TypeId::F64,
            },
        ];
        interpreter_ok(&insts);
    }

    // Cast: f64-to-f32 (fdemote equivalent)
    #[test]
    fn cast_f64_to_f32() {
        let insts = vec![
            MirInst::ConstFloat {
                dest: VReg(0),
                value: 2.5,
            },
            MirInst::Cast {
                dest: VReg(1),
                source: VReg(0),
                from_ty: TypeId::F64,
                to_ty: TypeId::F32,
            },
        ];
        interpreter_ok(&insts);
    }

    // Cast: default fallback (non-numeric types)
    #[test]
    fn cast_default_fallback() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 100,
            },
            MirInst::Cast {
                dest: VReg(1),
                source: VReg(0),
                from_ty: TypeId::ANY,
                to_ty: TypeId::STRING,
            },
        ];
        interpreter_ok(&insts);
    }

    // ContractCheck — all kinds via interpreter
    #[test]
    fn contract_postcondition() {
        let insts = vec![
            MirInst::ConstBool {
                dest: VReg(0),
                value: true,
            },
            MirInst::ContractCheck {
                condition: VReg(0),
                kind: ContractKind::Postcondition,
                func_name: "f".to_string(),
                message: None,
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn contract_error_postcondition() {
        let insts = vec![
            MirInst::ConstBool {
                dest: VReg(0),
                value: true,
            },
            MirInst::ContractCheck {
                condition: VReg(0),
                kind: ContractKind::ErrorPostcondition,
                func_name: "f".to_string(),
                message: None,
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn contract_invariant_entry() {
        let insts = vec![
            MirInst::ConstBool {
                dest: VReg(0),
                value: true,
            },
            MirInst::ContractCheck {
                condition: VReg(0),
                kind: ContractKind::InvariantEntry,
                func_name: "f".to_string(),
                message: None,
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn contract_invariant_exit() {
        let insts = vec![
            MirInst::ConstBool {
                dest: VReg(0),
                value: true,
            },
            MirInst::ContractCheck {
                condition: VReg(0),
                kind: ContractKind::InvariantExit,
                func_name: "f".to_string(),
                message: None,
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn contract_assertion() {
        let insts = vec![
            MirInst::ConstBool {
                dest: VReg(0),
                value: true,
            },
            MirInst::ContractCheck {
                condition: VReg(0),
                kind: ContractKind::Assertion,
                func_name: "f".to_string(),
                message: None,
            },
        ];
        interpreter_ok(&insts);
    }

    // GPU instruction branches via interpreter
    #[test]
    fn gpu_mem_fence_workgroup() {
        let insts = vec![MirInst::GpuMemFence {
            scope: GpuMemoryScope::WorkGroup,
        }];
        interpreter_ok(&insts);
    }

    #[test]
    fn gpu_mem_fence_all() {
        let insts = vec![MirInst::GpuMemFence {
            scope: GpuMemoryScope::All,
        }];
        interpreter_ok(&insts);
    }

    #[test]
    fn gpu_atomic_sub() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 1,
            },
            MirInst::GpuAtomic {
                dest: VReg(2),
                op: GpuAtomicOp::Sub,
                ptr: VReg(0),
                value: VReg(1),
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn gpu_atomic_xchg() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 5,
            },
            MirInst::GpuAtomic {
                dest: VReg(2),
                op: GpuAtomicOp::Xchg,
                ptr: VReg(0),
                value: VReg(1),
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn gpu_atomic_min() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 3,
            },
            MirInst::GpuAtomic {
                dest: VReg(2),
                op: GpuAtomicOp::Min,
                ptr: VReg(0),
                value: VReg(1),
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn gpu_atomic_max() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 7,
            },
            MirInst::GpuAtomic {
                dest: VReg(2),
                op: GpuAtomicOp::Max,
                ptr: VReg(0),
                value: VReg(1),
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn gpu_atomic_and() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 0xFF,
            },
            MirInst::GpuAtomic {
                dest: VReg(2),
                op: GpuAtomicOp::And,
                ptr: VReg(0),
                value: VReg(1),
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn gpu_atomic_or() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 0x0F,
            },
            MirInst::GpuAtomic {
                dest: VReg(2),
                op: GpuAtomicOp::Or,
                ptr: VReg(0),
                value: VReg(1),
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn gpu_atomic_xor() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 0xAA,
            },
            MirInst::GpuAtomic {
                dest: VReg(2),
                op: GpuAtomicOp::Xor,
                ptr: VReg(0),
                value: VReg(1),
            },
        ];
        interpreter_ok(&insts);
    }

    // Call Result/Option constructors via interpreter
    #[test]
    fn call_ok_constructor() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::Call {
                dest: Some(VReg(1)),
                target: crate::mir::CallTarget::Pure("Ok".to_string()),
                args: vec![VReg(0)],
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn call_err_constructor() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 1,
            },
            MirInst::Call {
                dest: Some(VReg(1)),
                target: crate::mir::CallTarget::Pure("Err".to_string()),
                args: vec![VReg(0)],
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn call_some_constructor() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 10,
            },
            MirInst::Call {
                dest: Some(VReg(1)),
                target: crate::mir::CallTarget::Pure("Some".to_string()),
                args: vec![VReg(0)],
            },
        ];
        interpreter_ok(&insts);
    }

    #[test]
    fn call_none_constructor() {
        let insts = vec![MirInst::Call {
            dest: Some(VReg(0)),
            target: crate::mir::CallTarget::Pure("None".to_string()),
            args: vec![],
        }];
        interpreter_ok(&insts);
    }

    #[test]
    fn call_qualified_variant() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 1,
            },
            MirInst::Call {
                dest: Some(VReg(1)),
                target: crate::mir::CallTarget::Pure("Result::Ok".to_string()),
                args: vec![VReg(0)],
            },
        ];
        interpreter_ok(&insts);
    }

    // Global variable via interpreter
    #[test]
    fn global_store_load() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 99,
            },
            MirInst::GlobalStore {
                global_name: "g".to_string(),
                value: VReg(0),
                ty: TypeId::I64,
            },
            MirInst::GlobalLoad {
                dest: VReg(1),
                global_name: "g".to_string(),
                ty: TypeId::I64,
            },
        ];
        let val = interpreter_value(&insts, VReg(1));
        assert_eq!(val, 99);
    }
}
