use super::aot_compiles;
use crate::mir::{BlockId, MirFunction, MirInst, VReg};

// =============================================================================
// SIMD vector operations (simd_stubs.rs, collections.rs)
// =============================================================================

/// Helper: build a single-element vector vreg
fn push_vec1(f: &mut MirFunction) -> VReg {
    let elem = f.new_vreg();
    let vec = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: elem, value: 1 });
    block.instructions.push(MirInst::VecLit {
        dest: vec,
        elements: vec![elem],
    });
    vec
}

#[test]
fn codegen_vec_sum() {
    assert!(aot_compiles("vec_sum", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecSum { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_product() {
    assert!(aot_compiles("vec_product", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecProduct { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_min() {
    assert!(aot_compiles("vec_min", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecMin { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_max() {
    assert!(aot_compiles("vec_max", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecMax { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_all() {
    assert!(aot_compiles("vec_all", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecAll { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_any() {
    assert!(aot_compiles("vec_any", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecAny { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_extract() {
    assert!(aot_compiles("vec_extract", |f| {
        let src = push_vec1(f);
        let idx = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block.instructions.push(MirInst::VecExtract {
            dest,
            vector: src,
            index: idx,
        });
        dest
    }));
}

#[test]
fn codegen_vec_with() {
    assert!(aot_compiles("vec_with", |f| {
        let src = push_vec1(f);
        let idx = f.new_vreg();
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: val, value: 99 });
        block.instructions.push(MirInst::VecWith {
            dest,
            vector: src,
            index: idx,
            value: val,
        });
        dest
    }));
}

#[test]
fn codegen_vec_sqrt() {
    assert!(aot_compiles("vec_sqrt", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecSqrt { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_abs() {
    assert!(aot_compiles("vec_abs", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecAbs { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_floor() {
    assert!(aot_compiles("vec_floor", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecFloor { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_ceil() {
    assert!(aot_compiles("vec_ceil", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecCeil { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_round() {
    assert!(aot_compiles("vec_round", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecRound { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_recip() {
    assert!(aot_compiles("vec_recip", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecRecip { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_shuffle() {
    assert!(aot_compiles("vec_shuffle", |f| {
        let src = push_vec1(f);
        let indices = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecShuffle {
            dest,
            source: src,
            indices,
        });
        dest
    }));
}

#[test]
fn codegen_vec_blend() {
    assert!(aot_compiles("vec_blend", |f| {
        let a = push_vec1(f);
        let b = push_vec1(f);
        let indices = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecBlend {
            dest,
            first: a,
            second: b,
            indices,
        });
        dest
    }));
}

#[test]
fn codegen_vec_select() {
    assert!(aot_compiles("vec_select", |f| {
        let mask = push_vec1(f);
        let a = push_vec1(f);
        let b = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecSelect {
            dest,
            mask,
            if_true: a,
            if_false: b,
        });
        dest
    }));
}

#[test]
fn codegen_vec_load() {
    assert!(aot_compiles("vec_load", |f| {
        let arr = f.new_vreg();
        let off = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
        block.instructions.push(MirInst::VecLoad {
            dest,
            array: arr,
            offset: off,
        });
        dest
    }));
}

#[test]
fn codegen_vec_store() {
    assert!(aot_compiles("vec_store", |f| {
        let src = push_vec1(f);
        let arr = f.new_vreg();
        let off = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
        block.instructions.push(MirInst::VecStore {
            source: src,
            array: arr,
            offset: off,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_vec_gather() {
    assert!(aot_compiles("vec_gather", |f| {
        let arr = f.new_vreg();
        let indices = push_vec1(f);
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::VecGather {
            dest,
            array: arr,
            indices,
        });
        dest
    }));
}

#[test]
fn codegen_vec_scatter() {
    assert!(aot_compiles("vec_scatter", |f| {
        let src = push_vec1(f);
        let arr = f.new_vreg();
        let indices = push_vec1(f);
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::VecScatter {
            source: src,
            array: arr,
            indices,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_vec_fma() {
    assert!(aot_compiles("vec_fma", |f| {
        let a = push_vec1(f);
        let b = push_vec1(f);
        let c = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecFma { dest, a, b, c });
        dest
    }));
}

#[test]
fn codegen_vec_masked_load() {
    assert!(aot_compiles("vec_mload", |f| {
        let arr = f.new_vreg();
        let off = f.new_vreg();
        let mask = push_vec1(f);
        let def = push_vec1(f);
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
        block.instructions.push(MirInst::VecMaskedLoad {
            dest,
            array: arr,
            offset: off,
            mask,
            default: def,
        });
        dest
    }));
}

#[test]
fn codegen_vec_masked_store() {
    assert!(aot_compiles("vec_mstore", |f| {
        let src = push_vec1(f);
        let arr = f.new_vreg();
        let off = f.new_vreg();
        let mask = push_vec1(f);
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
        block.instructions.push(MirInst::VecMaskedStore {
            source: src,
            array: arr,
            offset: off,
            mask,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_vec_min_vec() {
    assert!(aot_compiles("vec_min_vec", |f| {
        let a = push_vec1(f);
        let b = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecMinVec { dest, a, b });
        dest
    }));
}

#[test]
fn codegen_vec_max_vec() {
    assert!(aot_compiles("vec_max_vec", |f| {
        let a = push_vec1(f);
        let b = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::VecMaxVec { dest, a, b });
        dest
    }));
}

#[test]
fn codegen_vec_clamp() {
    assert!(aot_compiles("vec_clamp", |f| {
        let src = push_vec1(f);
        let lo = push_vec1(f);
        let hi = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecClamp {
            dest,
            source: src,
            lo,
            hi,
        });
        dest
    }));
}
