use super::aot_compiles;
use crate::mir::{BlockId, MirInst, UnitOverflowBehavior};

// =============================================================================
// Coverage probes (coverage.rs) — no-ops in non-coverage mode
// =============================================================================

#[test]
fn codegen_decision_probe() {
    assert!(aot_compiles("dec_probe", |f| {
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
    }));
}

#[test]
fn codegen_condition_probe() {
    assert!(aot_compiles("cond_probe", |f| {
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
    }));
}

#[test]
fn codegen_path_probe() {
    assert!(aot_compiles("path_probe", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::PathProbe {
            path_id: 0,
            block_id: 0,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
        ret
    }));
}

// =============================================================================
// Unit type operations (units.rs)
// =============================================================================

#[test]
fn codegen_unit_bound_check() {
    assert!(aot_compiles("unit_bound", |f| {
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
    }));
}

#[test]
fn codegen_unit_widen() {
    assert!(aot_compiles("unit_widen", |f| {
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
    }));
}

#[test]
fn codegen_unit_narrow() {
    assert!(aot_compiles("unit_narrow", |f| {
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
    }));
}

#[test]
fn codegen_unit_saturate() {
    assert!(aot_compiles("unit_sat", |f| {
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
    }));
}
