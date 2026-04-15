use super::*;

// =============================================================================
// Phase 3: GPU — remaining intrinsics
// =============================================================================

shared_test!(shared_gpu_local_id, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GpuLocalId { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_group_id, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GpuGroupId { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_global_size, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GpuGlobalSize { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_local_size, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GpuLocalSize { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_num_groups, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GpuNumGroups { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_mem_fence, |f: &mut MirFunction| {
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::GpuMemFence {
        scope: GpuMemoryScope::Device,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

shared_test!(shared_gpu_atomic, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
    block.instructions.push(MirInst::GpuAtomic {
        dest,
        op: GpuAtomicOp::Add,
        ptr,
        value: val,
    });
    dest
});

shared_test!(shared_gpu_atomic_cmpxchg, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let expected = f.new_vreg();
    let desired = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt {
        dest: expected,
        value: 0,
    });
    block.instructions.push(MirInst::ConstInt {
        dest: desired,
        value: 1,
    });
    block.instructions.push(MirInst::GpuAtomicCmpXchg {
        dest,
        ptr,
        expected,
        desired,
    });
    dest
});

shared_test!(shared_neighbor_load, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::NeighborLoad {
        dest,
        array: arr,
        direction: hir::NeighborDirection::Left,
    });
    dest
});

// =============================================================================
// Phase 3: Parallel — remaining
// =============================================================================

shared_test!(shared_par_reduce, |f: &mut MirFunction| {
    let input = f.new_vreg();
    let initial = f.new_vreg();
    let closure = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
    block.instructions.push(MirInst::ConstInt {
        dest: initial,
        value: 0,
    });
    block.instructions.push(MirInst::ConstInt {
        dest: closure,
        value: 0,
    });
    block.instructions.push(MirInst::ParReduce {
        dest,
        input,
        initial,
        closure,
        backend: None,
    });
    dest
});

shared_test!(shared_par_filter, |f: &mut MirFunction| {
    let input = f.new_vreg();
    let pred = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: pred, value: 0 });
    block.instructions.push(MirInst::ParFilter {
        dest,
        input,
        predicate: pred,
        backend: None,
    });
    dest
});

// =============================================================================
// Phase 3: SIMD vector operations
// =============================================================================

/// Helper: build a single-element vector vreg using raw instructions
fn push_vec1_shared(f: &mut MirFunction) -> VReg {
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

shared_test!(shared_vec_sum, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecSum { dest, source: src });
    dest
});

shared_test!(shared_vec_product, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecProduct { dest, source: src });
    dest
});

shared_test!(shared_vec_min, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecMin { dest, source: src });
    dest
});

shared_test!(shared_vec_max, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecMax { dest, source: src });
    dest
});

shared_test!(shared_vec_all, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecAll { dest, source: src });
    dest
});

shared_test!(shared_vec_any, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecAny { dest, source: src });
    dest
});

shared_test!(shared_vec_extract, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
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
});

shared_test!(shared_vec_with, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
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
});

shared_test!(shared_vec_sqrt, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecSqrt { dest, source: src });
    dest
});

shared_test!(shared_vec_abs, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecAbs { dest, source: src });
    dest
});

shared_test!(shared_vec_floor, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecFloor { dest, source: src });
    dest
});

shared_test!(shared_vec_ceil, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecCeil { dest, source: src });
    dest
});

shared_test!(shared_vec_round, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecRound { dest, source: src });
    dest
});

shared_test!(shared_vec_recip, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecRecip { dest, source: src });
    dest
});

shared_test!(shared_vec_shuffle, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let indices = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecShuffle {
        dest,
        source: src,
        indices,
    });
    dest
});

shared_test!(shared_vec_blend, |f: &mut MirFunction| {
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let indices = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecBlend {
        dest,
        first: a,
        second: b,
        indices,
    });
    dest
});

shared_test!(shared_vec_select, |f: &mut MirFunction| {
    let mask = push_vec1_shared(f);
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecSelect {
        dest,
        mask,
        if_true: a,
        if_false: b,
    });
    dest
});

shared_test!(shared_vec_load, |f: &mut MirFunction| {
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
});

shared_test!(shared_vec_store, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
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
});

shared_test!(shared_vec_gather, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let indices = push_vec1_shared(f);
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::VecGather {
        dest,
        array: arr,
        indices,
    });
    dest
});

shared_test!(shared_vec_scatter, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let arr = f.new_vreg();
    let indices = push_vec1_shared(f);
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
});

shared_test!(shared_vec_fma, |f: &mut MirFunction| {
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let c = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecFma { dest, a, b, c });
    dest
});

shared_test!(shared_vec_masked_load, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let off = f.new_vreg();
    let mask = push_vec1_shared(f);
    let def = push_vec1_shared(f);
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
});

shared_test!(shared_vec_masked_store, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let arr = f.new_vreg();
    let off = f.new_vreg();
    let mask = push_vec1_shared(f);
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
});

shared_test!(shared_vec_min_vec, |f: &mut MirFunction| {
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecMinVec { dest, a, b });
    dest
});

shared_test!(shared_vec_max_vec, |f: &mut MirFunction| {
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::VecMaxVec { dest, a, b });
    dest
});

shared_test!(shared_vec_clamp, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let lo = push_vec1_shared(f);
    let hi = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecClamp {
        dest,
        source: src,
        lo,
        hi,
    });
    dest
});

// =============================================================================
// Interpreter-only value verification tests
// =============================================================================
