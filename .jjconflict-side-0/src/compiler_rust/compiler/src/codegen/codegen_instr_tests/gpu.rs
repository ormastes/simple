use super::aot_compiles;
use crate::hir;
use crate::mir::{BlockId, GpuAtomicOp, GpuMemoryScope, MirInst};

// =============================================================================
// GPU instructions (instr_gpu.rs, simd_stubs.rs, collections.rs)
// =============================================================================

#[test]
fn codegen_gpu_shared_alloc() {
    assert!(aot_compiles("gpu_shmem", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GpuSharedAlloc {
                dest,
                element_type: crate::hir::TypeId::F64,
                size: 64,
            });
        dest
    }));
}

#[test]
fn codegen_neighbor_load() {
    assert!(aot_compiles("neighbor", |f| {
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
    }));
}

// =============================================================================
// GPU atomic operations
// =============================================================================

#[test]
fn codegen_gpu_atomic() {
    assert!(aot_compiles("gpu_atomic", |f| {
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
    }));
}

#[test]
fn codegen_gpu_atomic_cmpxchg() {
    assert!(aot_compiles("gpu_cmpxchg", |f| {
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
    }));
}

// =============================================================================
// GPU intrinsics (work item queries, barriers, fences)
// =============================================================================

#[test]
fn codegen_gpu_global_id() {
    assert!(aot_compiles("gpu_gid", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GpuGlobalId { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_local_id() {
    assert!(aot_compiles("gpu_lid", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GpuLocalId { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_group_id() {
    assert!(aot_compiles("gpu_grid", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GpuGroupId { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_global_size() {
    assert!(aot_compiles("gpu_gsz", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GpuGlobalSize { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_local_size() {
    assert!(aot_compiles("gpu_lsz", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GpuLocalSize { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_num_groups() {
    assert!(aot_compiles("gpu_ngrp", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GpuNumGroups { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_barrier() {
    assert!(aot_compiles("gpu_bar", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::GpuBarrier);
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_gpu_mem_fence() {
    assert!(aot_compiles("gpu_fence", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::GpuMemFence {
            scope: GpuMemoryScope::Device,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

// =============================================================================
// Actor operations (missing from codegen tests)
// =============================================================================

#[test]
fn codegen_actor_join() {
    assert!(aot_compiles("actor_join", |f| {
        let actor = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: actor, value: 0 });
        block.instructions.push(MirInst::ActorJoin { dest, actor });
        dest
    }));
}

#[test]
fn codegen_actor_reply() {
    assert!(aot_compiles("actor_reply", |f| {
        let msg = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: msg, value: 42 });
        block.instructions.push(MirInst::ActorReply { message: msg });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}
