//! Async state machine transformation for futures with multiple await points.
//!
//! This module transforms async function bodies into state machines, similar to
//! how generator.rs handles generators. Each `Await` instruction becomes a
//! suspension point where the state machine can pause and resume.

use std::collections::{HashMap, HashSet};

use super::{BlockId, MirBlock, MirFunction, MirInst, Terminator, VReg};
use crate::hir::TypeId;

/// Metadata for a single async state created from an `Await`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AsyncState {
    /// Monotonic state identifier (0-based).
    pub state_id: u32,
    /// Block that ends with the await.
    pub await_block: BlockId,
    /// Block to resume execution at when the future is ready.
    pub resume_block: BlockId,
    /// Register holding the future being awaited.
    pub future_reg: VReg,
    /// Register that receives the await result.
    pub result_reg: VReg,
    /// Live registers that must survive across the suspension.
    pub live_after_await: Vec<VReg>,
}

/// Result of lowering an async body into a dispatcher + resume blocks.
#[derive(Debug, Clone)]
pub struct AsyncLowering {
    /// The rewritten function containing a dispatcher entry block.
    pub rewritten: MirFunction,
    /// Ordered states discovered while rewriting `Await` instructions.
    pub states: Vec<AsyncState>,
    /// Block that marks async completion (Jump target when done).
    pub complete_block: BlockId,
}

/// Rewrite an async function body into a state-machine-friendly shape:
/// - Adds a dispatcher entry block (id 0) that jumps to the original body or resumes at a state.
/// - Splits blocks at each `Await`, turning the await block into a short block
///   that returns immediately and a resume block that continues execution.
/// - Collects per-await state metadata (state id, resume target, live-after set).
///
/// This pass prepares structured MIR + metadata that codegen can consume to emit
/// the real dispatcher and frame layout for async functions.
pub fn lower_async(func: &MirFunction, body_block: BlockId) -> AsyncLowering {
    // Dispatcher block (0) + completion block (1) are always present.
    let dispatcher = BlockId(0);

    let mut rewritten = MirFunction::new(func.name.clone(), TypeId::I64, func.visibility);
    rewritten.params = func.params.clone();
    rewritten.locals = func.locals.clone();
    rewritten.outlined_bodies = func.outlined_bodies.clone();

    // Prepare dispatcher and completion blocks.
    let complete_block = rewritten.new_block();
    if let Some(block) = rewritten.block_mut(complete_block) {
        block.terminator = Terminator::Return(None);
    }

    // Collect reachable blocks from the async body.
    let reachable = reachable_from(func, body_block);

    // Map original block ids to new block ids (after dispatcher + completion).
    let mut block_map: HashMap<BlockId, BlockId> = HashMap::new();
    for orig in &reachable {
        let new_id = rewritten.new_block();
        block_map.insert(*orig, new_id);
    }

    // Compute liveness for the original function to derive live-after sets.
    let live_ins = func.compute_live_ins();
    let live_outs = compute_live_outs(func, &live_ins);

    let mut states = Vec::new();

    for orig in &reachable {
        let mapped = block_map[orig];
        let orig_block = func
            .block(*orig)
            .unwrap_or_else(|| panic!("missing original block {:?}", orig));

        let live_after = live_after_each_inst(orig_block, live_outs.get(orig));

        let mut current_id = mapped;
        let mut current_block = MirBlock::new(current_id);

        for (idx, inst) in orig_block.instructions.iter().enumerate() {
            if let MirInst::Await { dest, future } = inst {
                let state_id = states.len() as u32;

                // Create a resume block for the remaining instructions (if any).
                let resume_id = if idx + 1 < orig_block.instructions.len()
                    || !matches!(orig_block.terminator, Terminator::Return(_))
                {
                    let resume = rewritten.new_block();
                    let mut resume_block = MirBlock::new(resume);
                    for inst_after in orig_block.instructions.iter().skip(idx + 1) {
                        resume_block.instructions.push(inst_after.clone());
                    }
                    resume_block.terminator =
                        remap_terminator(orig_block.terminator.clone(), &block_map)
                            .unwrap_or_else(|| Terminator::Return(None));
                    write_block(&mut rewritten, resume_block);
                    resume
                } else {
                    complete_block
                };

                let mut live: Vec<VReg> = live_after
                    .get(idx + 1)
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .collect();
                live.sort_by_key(|v| v.0);

                states.push(AsyncState {
                    state_id,
                    await_block: current_id,
                    resume_block: resume_id,
                    future_reg: *future,
                    result_reg: *dest,
                    live_after_await: live,
                });

                // The await block ends by polling the future and returning if pending.
                // For now, we use eager execution (poll returns result immediately).
                current_block.terminator = Terminator::Return(None);
                write_block(&mut rewritten, current_block);

                // Continue rewriting the suffix (if any) from the resume block.
                current_id = resume_id;
                current_block = rewritten
                    .block(current_id)
                    .cloned()
                    .unwrap_or_else(|| MirBlock::new(current_id));
                // Ensure resume block exists in the function even if empty.
                if rewritten.block(current_id).is_none() {
                    rewritten.blocks.push(MirBlock::new(current_id));
                }
                continue;
            }

            current_block.instructions.push(inst.clone());
        }

        // If the block ended without an await, copy the original terminator.
        if !current_block.terminator.is_sealed() {
            current_block.terminator = remap_terminator(orig_block.terminator.clone(), &block_map)
                .unwrap_or(Terminator::Return(None));
            write_block(&mut rewritten, current_block);
        } else {
            write_block(&mut rewritten, current_block);
        }
    }

    // Dispatcher jumps to the mapped async body entry.
    if let Some(block) = rewritten.block_mut(dispatcher) {
        if let Some(mapped_entry) = block_map.get(&body_block) {
            block.terminator = Terminator::Jump(*mapped_entry);
        } else {
            block.terminator = Terminator::Return(None);
        }
    }

    AsyncLowering {
        rewritten: {
            let mut r = rewritten;
            r.async_states = Some(states.clone());
            r.async_complete = Some(complete_block);
            r
        },
        states,
        complete_block,
    }
}

fn reachable_from(func: &MirFunction, start: BlockId) -> HashSet<BlockId> {
    let mut reachable = HashSet::new();
    let mut stack = vec![start];
    while let Some(bid) = stack.pop() {
        if !reachable.insert(bid) {
            continue;
        }
        if let Some(b) = func.block(bid) {
            for succ in b.terminator.successors() {
                stack.push(succ);
            }
        }
    }
    reachable
}

fn compute_live_outs(
    func: &MirFunction,
    live_ins: &HashMap<BlockId, HashSet<VReg>>,
) -> HashMap<BlockId, HashSet<VReg>> {
    let mut live_outs = HashMap::new();
    for block in &func.blocks {
        let mut out = HashSet::new();
        for succ in block.terminator.successors() {
            if let Some(ins) = live_ins.get(&succ) {
                out.extend(ins.iter().copied());
            }
        }
        live_outs.insert(block.id, out);
    }
    live_outs
}

fn live_after_each_inst(block: &MirBlock, live_out: Option<&HashSet<VReg>>) -> Vec<HashSet<VReg>> {
    let mut live = live_out.cloned().unwrap_or_default();
    let mut states = Vec::with_capacity(block.instructions.len() + 1);
    states.push(live.clone()); // After the final instruction

    for inst in block.instructions.iter().rev() {
        if let Some(dest) = inst.dest() {
            live.remove(&dest);
        }
        for u in inst.uses() {
            live.insert(u);
        }
        states.push(live.clone());
    }

    states.reverse();
    states
}

fn remap_terminator(term: Terminator, map: &HashMap<BlockId, BlockId>) -> Option<Terminator> {
    match term {
        Terminator::Jump(target) => map.get(&target).copied().map(Terminator::Jump),
        Terminator::Branch {
            cond,
            then_block,
            else_block,
        } => Some(Terminator::Branch {
            cond,
            then_block: map.get(&then_block).copied().unwrap_or(then_block),
            else_block: map.get(&else_block).copied().unwrap_or(else_block),
        }),
        Terminator::Return(v) => Some(Terminator::Return(v)),
        Terminator::Unreachable => None,
    }
}

fn write_block(func: &mut MirFunction, block: MirBlock) {
    if let Some(existing) = func.block_mut(block.id) {
        *existing = block;
    } else {
        func.blocks.push(block);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::TypeId;
    use crate::mir::Visibility;

    fn const_inst(dest: VReg, value: i64) -> MirInst {
        MirInst::ConstInt { dest, value }
    }

    #[test]
    fn splits_blocks_at_await_points() {
        // Original async body:
        // b0:
        //   v0 = const 1
        //   v1 = await v0
        //   v2 = const 2
        //   v3 = await v2
        //   return v3
        let mut func = MirFunction::new("async_fn".into(), TypeId::I64, Visibility::Public);
        func.blocks.clear();
        func.entry_block = BlockId(0);

        let mut b0 = MirBlock::new(BlockId(0));
        b0.instructions.push(const_inst(VReg(0), 1));
        b0.instructions.push(MirInst::Await {
            dest: VReg(1),
            future: VReg(0),
        });
        b0.instructions.push(const_inst(VReg(2), 2));
        b0.instructions.push(MirInst::Await {
            dest: VReg(3),
            future: VReg(2),
        });
        b0.terminator = Terminator::Return(Some(VReg(3)));
        func.blocks.push(b0);

        let lowered = lower_async(&func, BlockId(0));
        let states = lowered.states;

        assert_eq!(states.len(), 2, "should discover two await points");
        assert_eq!(states[0].state_id, 0);
        assert_eq!(states[0].future_reg, VReg(0));
        assert_eq!(states[0].result_reg, VReg(1));
        assert_eq!(states[1].state_id, 1);
        assert_eq!(states[1].future_reg, VReg(2));
        assert_eq!(states[1].result_reg, VReg(3));

        // Dispatcher is block 0, completion is block 1, mapped entry starts after that.
        assert_eq!(lowered.rewritten.entry_block, BlockId(0));
        let dispatcher = lowered
            .rewritten
            .block(BlockId(0))
            .expect("dispatcher present");
        if let Terminator::Jump(target) = dispatcher.terminator {
            assert_ne!(target, lowered.complete_block);
        } else {
            panic!("dispatcher should jump to body");
        }

        // Resume targets should differ from await blocks to guarantee splitting occurred.
        assert_ne!(states[0].await_block, states[0].resume_block);
        assert_ne!(states[1].await_block, states[1].resume_block);
    }
}
