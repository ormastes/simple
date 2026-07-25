use super::*;

// Branch coverage: Pointer kinds
// =============================================================================

shared_test!(shared_pointer_new_shared, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest,
        kind: PointerKind::Shared,
        value: val,
    });
    dest
});

shared_test!(shared_pointer_new_handle, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest,
        kind: PointerKind::Handle,
        value: val,
    });
    dest
});

shared_test!(shared_pointer_new_weak, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest,
        kind: PointerKind::Weak,
        value: val,
    });
    dest
});

shared_test!(shared_pointer_new_borrow_mut, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest,
        kind: PointerKind::BorrowMut,
        value: val,
    });
    dest
});

shared_test!(shared_pointer_new_raw_const, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest,
        kind: PointerKind::RawConst,
        value: val,
    });
    dest
});

shared_test!(shared_pointer_new_raw_mut, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest,
        kind: PointerKind::RawMut,
        value: val,
    });
    dest
});

shared_test!(shared_pointer_deref_shared, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest: ptr,
        kind: PointerKind::Shared,
        value: val,
    });
    block.instructions.push(MirInst::PointerDeref {
        dest,
        pointer: ptr,
        kind: PointerKind::Shared,
    });
    dest
});

shared_test!(shared_pointer_deref_weak, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest: ptr,
        kind: PointerKind::Weak,
        value: val,
    });
    block.instructions.push(MirInst::PointerDeref {
        dest,
        pointer: ptr,
        kind: PointerKind::Weak,
    });
    dest
});

shared_test!(shared_pointer_deref_borrow_mut, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerRef {
        dest: ptr,
        kind: PointerKind::BorrowMut,
        source: val,
    });
    block.instructions.push(MirInst::PointerDeref {
        dest,
        pointer: ptr,
        kind: PointerKind::BorrowMut,
    });
    dest
});

shared_test!(shared_pointer_deref_raw_const, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest: ptr,
        kind: PointerKind::RawConst,
        value: val,
    });
    block.instructions.push(MirInst::PointerDeref {
        dest,
        pointer: ptr,
        kind: PointerKind::RawConst,
    });
    dest
});

shared_test!(shared_pointer_deref_raw_mut, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest: ptr,
        kind: PointerKind::RawMut,
        value: val,
    });
    block.instructions.push(MirInst::PointerDeref {
        dest,
        pointer: ptr,
        kind: PointerKind::RawMut,
    });
    dest
});

// =============================================================================
// Branch coverage: Unit overflow behaviors
// =============================================================================

cranelift_only_test!(shared_unit_bound_check_saturate, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 200 });
    block.instructions.push(MirInst::UnitBoundCheck {
        value: val,
        unit_name: "Byte".to_string(),
        min: 0,
        max: 100,
        overflow: UnitOverflowBehavior::Saturate,
    });
    val
});

cranelift_only_test!(shared_unit_bound_check_wrap, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 200 });
    block.instructions.push(MirInst::UnitBoundCheck {
        value: val,
        unit_name: "Byte".to_string(),
        min: 0,
        max: 100,
        overflow: UnitOverflowBehavior::Wrap,
    });
    val
});

shared_test!(shared_unit_bound_check_checked, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 50 });
    block.instructions.push(MirInst::UnitBoundCheck {
        value: val,
        unit_name: "Byte".to_string(),
        min: 0,
        max: 100,
        overflow: UnitOverflowBehavior::Checked,
    });
    val
});

shared_test!(shared_unit_narrow_checked, |f: &mut MirFunction| {
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
        overflow: UnitOverflowBehavior::Checked,
    });
    dest
});

shared_test!(shared_unit_narrow_wrap, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 300 });
    block.instructions.push(MirInst::UnitNarrow {
        dest,
        value: val,
        from_bits: 16,
        to_bits: 8,
        signed: false,
        overflow: UnitOverflowBehavior::Wrap,
    });
    dest
});

shared_test!(shared_unit_widen_unsigned, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnitWiden {
        dest,
        value: val,
        from_bits: 8,
        to_bits: 16,
        signed: false,
    });
    dest
});

shared_test!(shared_unit_narrow_unsigned, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnitNarrow {
        dest,
        value: val,
        from_bits: 16,
        to_bits: 8,
        signed: false,
        overflow: UnitOverflowBehavior::Saturate,
    });
    dest
});

// =============================================================================
// Branch coverage: Drop with non-primitive type
// =============================================================================

shared_test!(shared_drop_non_primitive, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    // Use ANY type — a non-primitive type that triggers the non-primitive branch
    block.instructions.push(MirInst::Drop {
        value: val,
        ty: TypeId::ANY,
    });
    val
});

// =============================================================================
