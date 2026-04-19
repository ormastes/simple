//! Concurrent instruction tests: async, generators, actors, parallel iterators.
//!
//! Covers: FutureCreate, Await, ActorSpawn/Send/Recv, GeneratorCreate, Yield,
//! GeneratorNext, ParMap, ParReduce, ParFilter, ParForEach.

use super::{aot_compiles, aot_compiles_module};
use crate::hir::TypeId;
use crate::mir::{BlockId, MirInst, Terminator, VReg};

// =============================================================================
// Async / Generator / Actor (async_ops.rs, actors.rs)
// =============================================================================

#[test]
fn codegen_future_create() {
    assert!(aot_compiles("future_c", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let ret = f.new_vreg();
        f.block_mut(body_block)
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: ret, value: 42 });
        f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::FutureCreate { dest, body_block });
        dest
    }));
}

#[test]
fn codegen_await() {
    assert!(aot_compiles("await_test", |f| {
        let future = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: future, value: 0 });
        block.instructions.push(MirInst::Await { dest, future });
        dest
    }));
}

#[test]
fn codegen_actor_spawn() {
    assert!(aot_compiles("actor_sp", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let ret = f.new_vreg();
        f.block_mut(body_block)
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: ret, value: 0 });
        f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ActorSpawn { dest, body_block });
        dest
    }));
}

#[test]
fn codegen_actor_send() {
    assert!(aot_compiles("actor_send", |f| {
        let actor = f.new_vreg();
        let msg = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: actor, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: msg, value: 42 });
        block.instructions.push(MirInst::ActorSend { actor, message: msg });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_actor_recv() {
    assert!(aot_compiles("actor_recv", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ActorRecv { dest });
        dest
    }));
}

#[test]
fn codegen_generator_create() {
    assert!(aot_compiles("gen_create", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let ret = f.new_vreg();
        f.block_mut(body_block)
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: ret, value: 0 });
        f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GeneratorCreate { dest, body_block });
        dest
    }));
}

#[test]
fn codegen_yield() {
    assert!(aot_compiles("yield_test", |f| {
        let val = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Yield { value: val });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_generator_next() {
    assert!(aot_compiles("gen_next", |f| {
        let gen = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: gen, value: 0 });
        block.instructions.push(MirInst::GeneratorNext { dest, generator: gen });
        dest
    }));
}

// =============================================================================
// Parallel iterators (parallel.rs)
// =============================================================================

#[test]
fn codegen_par_map() {
    assert!(aot_compiles("par_map", |f| {
        let input = f.new_vreg();
        let closure = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: closure,
            value: 0,
        });
        block.instructions.push(MirInst::ParMap {
            dest,
            input,
            closure,
            backend: None,
        });
        dest
    }));
}

#[test]
fn codegen_par_reduce() {
    assert!(aot_compiles("par_reduce", |f| {
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
    }));
}

#[test]
fn codegen_par_filter() {
    assert!(aot_compiles("par_filter", |f| {
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
    }));
}

#[test]
fn codegen_par_for_each() {
    assert!(aot_compiles("par_each", |f| {
        let input = f.new_vreg();
        let closure = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt {
            dest: closure,
            value: 0,
        });
        block.instructions.push(MirInst::ParForEach {
            input,
            closure,
            backend: None,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}
