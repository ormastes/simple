use super::*;

#[cfg(test)]
mod interpreter_value_checks {
    use super::*;

    #[test]
    fn const_int_value() {
        let insts = vec![MirInst::ConstInt {
            dest: VReg(0),
            value: 42,
        }];
        assert_eq!(interpreter_value(&insts, VReg(0)), 42);
    }

    #[test]
    fn binop_add_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 10,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 32,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::Add,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 42);
    }

    #[test]
    fn binop_mul_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 6,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 7,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::Mul,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 42);
    }

    #[test]
    fn unary_neg_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::UnaryOp {
                dest: VReg(1),
                op: hir::UnaryOp::Neg,
                operand: VReg(0),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), -42);
    }

    #[test]
    fn copy_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 99,
            },
            MirInst::Copy {
                dest: VReg(1),
                src: VReg(0),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), 99);
    }

    #[test]
    fn unit_saturate_clamps() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 300,
            },
            MirInst::UnitSaturate {
                dest: VReg(1),
                value: VReg(0),
                min: 0,
                max: 255,
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), 255);
    }

    #[test]
    fn box_unbox_int_roundtrip() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::BoxInt {
                dest: VReg(1),
                value: VReg(0),
            },
            MirInst::UnboxInt {
                dest: VReg(2),
                value: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 42);
    }

    #[test]
    fn global_store_load_roundtrip() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
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
        assert_eq!(interpreter_value(&insts, VReg(1)), 42);
    }

    #[test]
    fn option_some_tagged() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::OptionSome {
                dest: VReg(1),
                value: VReg(0),
            },
        ];
        // Tagged: (42 << 1) | 1 = 85
        assert_eq!(interpreter_value(&insts, VReg(1)), 85);
    }

    #[test]
    fn option_none_is_zero() {
        let insts = vec![MirInst::OptionNone { dest: VReg(0) }];
        assert_eq!(interpreter_value(&insts, VReg(0)), 0);
    }
}

#[cfg(test)]
mod interpreter_branch_coverage {
    use super::*;

    #[test]
    fn binop_mod_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 10,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 3,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::Mod,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn binop_mod_by_zero() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(1),
                value: 0,
            },
        )
        .unwrap();
        let result = dispatch_instruction(
            &mut emitter,
            &MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::Mod,
                left: VReg(0),
                right: VReg(1),
            },
        );
        assert!(result.is_err());
    }

    #[test]
    fn binop_bitand_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0xFF,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 0x0F,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::BitAnd,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 0x0F);
    }

    #[test]
    fn binop_bitor_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0xF0,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 0x0F,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::BitOr,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 0xFF);
    }

    #[test]
    fn binop_bitxor_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0xFF,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 0x0F,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::BitXor,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 0xF0);
    }

    #[test]
    fn binop_shift_left_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 1,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 3,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::ShiftLeft,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 8);
    }

    #[test]
    fn binop_shift_right_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 8,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 2,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::ShiftRight,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 2);
    }

    #[test]
    fn binop_noteq_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 1,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 2,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::NotEq,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn binop_noteq_same() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 42,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::NotEq,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 0);
    }

    #[test]
    fn binop_gt_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 10,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 5,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::Gt,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn binop_lteq_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 5,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 5,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::LtEq,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn binop_gteq_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 5,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 5,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::GtEq,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn unary_bitnot_value() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
            MirInst::UnaryOp {
                dest: VReg(1),
                op: hir::UnaryOp::BitNot,
                operand: VReg(0),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), !0i64);
    }

    #[test]
    fn unit_bound_check_out_of_range() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(0),
                value: 200,
            },
        )
        .unwrap();
        let result = dispatch_instruction(
            &mut emitter,
            &MirInst::UnitBoundCheck {
                value: VReg(0),
                unit_name: "Score".to_string(),
                min: 0,
                max: 100,
                overflow: UnitOverflowBehavior::Default,
            },
        );
        assert!(result.is_err());
    }

    #[test]
    fn cast_identity() {
        // Test the identity/unsupported cast fallback branch
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::Cast {
                dest: VReg(1),
                source: VReg(0),
                from_ty: TypeId::I64,
                to_ty: TypeId::I64,
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), 42);
    }

    #[test]
    fn local_addr_store_load_roundtrip() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::LocalAddr {
                dest: VReg(0),
                local_index: 0,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(1),
                value: 42,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::Store {
                addr: VReg(0),
                value: VReg(1),
                ty: TypeId::I64,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::Load {
                dest: VReg(2),
                addr: VReg(0),
                ty: TypeId::I64,
            },
        )
        .unwrap();
        assert_eq!(emitter.get(VReg(2)), 42);
    }

    #[test]
    fn get_element_ptr_offset() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 100,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 3,
            },
            MirInst::GetElementPtr {
                dest: VReg(2),
                base: VReg(0),
                index: VReg(1),
            },
        ];
        // 100 + 3*8 = 124
        assert_eq!(interpreter_value(&insts, VReg(2)), 124);
    }

    #[test]
    fn result_err_tagged() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 5,
            },
            MirInst::ResultErr {
                dest: VReg(1),
                value: VReg(0),
            },
        ];
        // (5 << 1) = 10 (no | 1 for Err)
        assert_eq!(interpreter_value(&insts, VReg(1)), 10);
    }

    #[test]
    fn result_ok_tagged() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 5,
            },
            MirInst::ResultOk {
                dest: VReg(1),
                value: VReg(0),
            },
        ];
        // (5 << 1) | 1 = 11
        assert_eq!(interpreter_value(&insts, VReg(1)), 11);
    }

    #[test]
    fn pattern_bind_copies_subject() {
        let insts = vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
            MirInst::PatternBind {
                dest: VReg(1),
                subject: VReg(0),
                binding: PatternBinding {
                    name: "x".to_string(),
                    path: vec![],
                },
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), 42);
    }

    #[test]
    fn wait_with_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::Wait {
                dest: Some(VReg(1)),
                target: VReg(0),
            },
        )
        .unwrap();
        assert_eq!(emitter.get(VReg(1)), 0);
    }

    #[test]
    fn wait_without_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
        )
        .unwrap();
        // Should not panic
        dispatch_instruction(
            &mut emitter,
            &MirInst::Wait {
                dest: None,
                target: VReg(0),
            },
        )
        .unwrap();
    }

    #[test]
    fn call_with_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::Call {
                dest: None,
                target: crate::mir::CallTarget::Pure("noop".to_string()),
                args: vec![VReg(0)],
            },
        )
        .unwrap();
    }

    #[test]
    fn interp_call_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::InterpCall {
                dest: None,
                func_name: "noop".to_string(),
                args: vec![],
            },
        )
        .unwrap();
    }

    #[test]
    fn indirect_call_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::IndirectCall {
                dest: None,
                callee: VReg(0),
                param_types: vec![],
                return_type: TypeId::VOID,
                args: vec![],
                effect: crate::mir::Effect::Compute,
            },
        )
        .unwrap();
    }

    #[test]
    fn method_call_static_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::MethodCallStatic {
                dest: None,
                receiver: VReg(0),
                func_name: "Foo::bar".to_string(),
                args: vec![],
            },
        )
        .unwrap();
    }

    #[test]
    fn method_call_virtual_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(0),
                value: 42,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::MethodCallVirtual {
                dest: None,
                receiver: VReg(0),
                vtable_slot: 0,
                param_types: vec![],
                return_type: TypeId::VOID,
                args: vec![],
            },
        )
        .unwrap();
    }

    #[test]
    fn builtin_method_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ConstInt {
                dest: VReg(0),
                value: 0,
            },
        )
        .unwrap();
        dispatch_instruction(
            &mut emitter,
            &MirInst::BuiltinMethod {
                dest: None,
                receiver: VReg(0),
                receiver_type: "Array".to_string(),
                method: "clear".to_string(),
                args: vec![],
            },
        )
        .unwrap();
    }

    #[test]
    fn extern_method_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(
            &mut emitter,
            &MirInst::ExternMethodCall {
                dest: None,
                receiver: None,
                class_name: "IO".to_string(),
                method_name: "flush".to_string(),
                is_static: true,
                args: vec![],
            },
        )
        .unwrap();
    }
}
