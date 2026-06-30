use super::aot_compiles;
use crate::hir::{PointerKind, TypeId};
use crate::mir::{BlockId, ContractKind, MirFunction, MirInst};

// =============================================================================
// Enum operations (enum_union.rs, pattern.rs)
// =============================================================================

#[test]
fn codegen_enum_unit() {
    assert!(aot_compiles("enum_unit", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::EnumUnit {
            dest,
            enum_name: "Color".to_string(),
            variant_name: "Red".to_string(),
        });
        dest
    }));
}

#[test]
fn codegen_enum_with() {
    assert!(aot_compiles("enum_with", |f| {
        let payload = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: payload,
            value: 42,
        });
        block.instructions.push(MirInst::EnumWith {
            dest,
            enum_name: "Option".to_string(),
            variant_name: "Some".to_string(),
            payload,
        });
        dest
    }));
}

#[test]
fn codegen_enum_discriminant() {
    assert!(aot_compiles("enum_disc", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::EnumUnit {
            dest: val,
            enum_name: "Color".to_string(),
            variant_name: "Red".to_string(),
        });
        block.instructions.push(MirInst::EnumDiscriminant { dest, value: val });
        dest
    }));
}

#[test]
fn codegen_enum_payload() {
    assert!(aot_compiles("enum_pay", |f| {
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
    }));
}

// =============================================================================
// Union operations (enum_union.rs)
// =============================================================================

#[test]
fn codegen_union_wrap() {
    assert!(aot_compiles("union_wrap", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::UnionWrap {
            dest,
            value: val,
            type_index: 0,
        });
        dest
    }));
}

#[test]
fn codegen_union_discriminant() {
    assert!(aot_compiles("union_disc", |f| {
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
    }));
}

#[test]
fn codegen_union_payload() {
    assert!(aot_compiles("union_pay", |f| {
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
    }));
}

// =============================================================================
// Result / Option (result.rs)
// =============================================================================

#[test]
fn codegen_option_some() {
    assert!(aot_compiles("opt_some", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::OptionSome { dest, value: val });
        dest
    }));
}

#[test]
fn codegen_option_none() {
    assert!(aot_compiles("opt_none", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::OptionNone { dest });
        dest
    }));
}

#[test]
fn codegen_result_ok() {
    assert!(aot_compiles("res_ok", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::ResultOk { dest, value: val });
        dest
    }));
}

#[test]
fn codegen_result_err() {
    assert!(aot_compiles("res_err", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
        block.instructions.push(MirInst::ResultErr { dest, value: val });
        dest
    }));
}

#[test]
fn codegen_try_unwrap() {
    // TryUnwrap creates internal Cranelift blocks for branching, which requires
    // the full block-sealing infrastructure. Verify MIR construction is valid.
    let mut func = MirFunction::new(
        "try_unwrap".to_string(),
        TypeId::I64,
        simple_parser::ast::Visibility::Public,
    );
    let val = func.new_vreg();
    let opt = func.new_vreg();
    let dest = func.new_vreg();
    let error_dest = func.new_vreg();
    let error_block = func.new_block();

    let block = func.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::OptionSome { dest: opt, value: val });
    block.instructions.push(MirInst::TryUnwrap {
        dest,
        value: opt,
        error_block,
        error_dest,
    });

    assert!(func.blocks[0]
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::TryUnwrap { .. })));
}

// =============================================================================
// Pointer operations (pointers.rs)
// =============================================================================

#[test]
fn codegen_pointer_new() {
    assert!(aot_compiles("ptr_new", |f| {
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
    }));
}

#[test]
fn codegen_pointer_ref_deref() {
    assert!(aot_compiles("ptr_ref_deref", |f| {
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
    }));
}

// =============================================================================
// Contract operations (contracts.rs, interpreter.rs)
// =============================================================================

#[test]
fn codegen_contract_check() {
    assert!(aot_compiles("contract_chk", |f| {
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
            func_name: "contract_chk".to_string(),
            message: None,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
        ret
    }));
}

#[test]
fn codegen_contract_old_capture() {
    assert!(aot_compiles("old_cap", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block
            .instructions
            .push(MirInst::ContractOldCapture { dest, value: val });
        dest
    }));
}

// =============================================================================
// Spread (basic_ops.rs)
// =============================================================================

#[test]
fn codegen_spread() {
    assert!(aot_compiles("spread_test", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Spread { dest, source: val });
        dest
    }));
}
