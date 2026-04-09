use super::*;

// =============================================================================
// Phase 1: Constants
// =============================================================================

shared_test!(shared_const_int, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstInt { dest, value: 42 });
    dest
});

shared_test!(shared_const_float, |f: &mut MirFunction| {
    let fv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstFloat { dest: fv, value: 3.14 });
    block.instructions.push(MirInst::Cast {
        dest,
        source: fv,
        from_ty: TypeId::F64,
        to_ty: TypeId::I64,
    });
    dest
});

shared_test!(shared_const_bool_true, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstBool { dest, value: true });
    dest
});

shared_test!(shared_const_bool_false, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstBool { dest, value: false });
    dest
});

shared_test!(shared_const_string, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstString {
            dest,
            value: "hello".to_string(),
        });
    dest
});

shared_test!(shared_const_symbol, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstSymbol {
            dest,
            value: "my_sym".to_string(),
        });
    dest
});

// =============================================================================
// Phase 1: Basic operations
// =============================================================================

shared_test!(shared_copy, |f: &mut MirFunction| {
    let src = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: src, value: 99 });
    block.instructions.push(MirInst::Copy { dest, src });
    dest
});

shared_test!(shared_spread, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::Spread { dest, source: val });
    dest
});

shared_test!(shared_unary_neg, |f: &mut MirFunction| {
    let src = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: src, value: 42 });
    block.instructions.push(MirInst::UnaryOp {
        dest,
        op: hir::UnaryOp::Neg,
        operand: src,
    });
    dest
});

shared_test!(shared_unary_not, |f: &mut MirFunction| {
    let src = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstBool { dest: src, value: true });
    block.instructions.push(MirInst::UnaryOp {
        dest,
        op: hir::UnaryOp::Not,
        operand: src,
    });
    dest
});

shared_test!(shared_cast_int_float, |f: &mut MirFunction| {
    let i = f.new_vreg();
    let fv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: i, value: 7 });
    block.instructions.push(MirInst::Cast {
        dest: fv,
        source: i,
        from_ty: TypeId::I64,
        to_ty: TypeId::F64,
    });
    block.instructions.push(MirInst::Cast {
        dest,
        source: fv,
        from_ty: TypeId::F64,
        to_ty: TypeId::I64,
    });
    dest
});

// BinOp tests — individual operations
shared_test!(shared_binop_add, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 10 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 32 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Add,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_sub, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 50 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 8 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Sub,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_mul, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 6 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 7 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Mul,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_div, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 84 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Div,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_eq, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 42 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 42 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Eq,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_lt, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 5 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 10 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Lt,
        left: a,
        right: b,
    });
    dest
});

// =============================================================================
// Phase 1: Memory safety / no-ops
// =============================================================================

shared_test!(shared_drop_noop, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::Drop {
        value: val,
        ty: TypeId::I64,
    });
    val
});

shared_test!(shared_end_scope_noop, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::EndScope { local_index: 0 });
    val
});

// =============================================================================
// Phase 1: Boxing
// =============================================================================

shared_test!(shared_box_unbox_int, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let boxed = f.new_vreg();
    let unboxed = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BoxInt {
        dest: boxed,
        value: val,
    });
    block.instructions.push(MirInst::UnboxInt {
        dest: unboxed,
        value: boxed,
    });
    unboxed
});

shared_test!(shared_box_unbox_float, |f: &mut MirFunction| {
    let fval = f.new_vreg();
    let boxed = f.new_vreg();
    let unboxed = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstFloat { dest: fval, value: 7.0 });
    block.instructions.push(MirInst::BoxFloat {
        dest: boxed,
        value: fval,
    });
    block.instructions.push(MirInst::UnboxFloat {
        dest: unboxed,
        value: boxed,
    });
    block.instructions.push(MirInst::Cast {
        dest,
        source: unboxed,
        from_ty: TypeId::F64,
        to_ty: TypeId::I64,
    });
    dest
});

// =============================================================================
// Phase 1: Units
// =============================================================================

shared_test!(shared_unit_widen, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnitWiden {
        dest,
        value: val,
        from_bits: 8,
        to_bits: 16,
        signed: true,
    });
    dest
});

shared_test!(shared_unit_narrow, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnitNarrow {
        dest,
        value: val,
        from_bits: 16,
        to_bits: 8,
        signed: true,
        overflow: UnitOverflowBehavior::Saturate,
    });
    dest
});

shared_test!(shared_unit_saturate, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 300 });
    block.instructions.push(MirInst::UnitSaturate {
        dest,
        value: val,
        min: 0,
        max: 255,
    });
    dest
});

shared_test!(shared_unit_bound_check, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 50 });
    block.instructions.push(MirInst::UnitBoundCheck {
        value: val,
        unit_name: "Score".to_string(),
        min: 0,
        max: 100,
        overflow: UnitOverflowBehavior::Default,
    });
    val
});

// =============================================================================
// Phase 1: Contracts
// =============================================================================

shared_test!(shared_contract_old_capture, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block
        .instructions
        .push(MirInst::ContractOldCapture { dest, value: val });
    dest
});

shared_test!(shared_contract_check, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstBool {
        dest: cond,
        value: true,
    });
    block.instructions.push(MirInst::ContractCheck {
        condition: cond,
        kind: ContractKind::Precondition,
        func_name: "shared_contract_check".to_string(),
        message: None,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
    ret
});

// =============================================================================
// Phase 1: Pointers
// =============================================================================

shared_test!(shared_pointer_new, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest,
        kind: PointerKind::Unique,
        value: val,
    });
    dest
});

shared_test!(shared_pointer_ref_deref, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerRef {
        dest: ptr,
        kind: PointerKind::Borrow,
        source: val,
    });
    block.instructions.push(MirInst::PointerDeref {
        dest,
        pointer: ptr,
        kind: PointerKind::Borrow,
    });
    dest
});

// =============================================================================
// Phase 1: Coverage probes (no-ops)
// =============================================================================

shared_test!(shared_decision_probe, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstBool {
        dest: cond,
        value: true,
    });
    block.instructions.push(MirInst::DecisionProbe {
        decision_id: 0,
        result: cond,
        file: "test.spl".to_string(),
        line: 1,
        column: 1,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
    ret
});

shared_test!(shared_path_probe, |f: &mut MirFunction| {
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::PathProbe {
        path_id: 0,
        block_id: 0,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
    ret
});

