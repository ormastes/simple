//! Common utilities for state machine transformations.
//!
//! Shared by both async_sm.rs (async/await) and generator.rs (yield).
//! These utilities handle:
//! - Reachability analysis
//! - Liveness analysis
//! - Block remapping
//! - Block writing

use crate::mir::{BlockId, MirBlock, MirFunction, Terminator, VReg};
use std::collections::{HashMap, HashSet};

/// Compute all blocks reachable from a given starting block.
pub(crate) fn reachable_from(func: &MirFunction, start: BlockId) -> HashSet<BlockId> {
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

/// Compute live-out sets for all blocks given their live-in sets.
pub(crate) fn compute_live_outs(
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

/// Compute live registers after each instruction in a block.
///
/// Returns a vector where element i contains the set of live registers
/// after instruction i. The final element is the live-out set for the block.
pub(crate) fn live_after_each_inst(block: &MirBlock, live_out: Option<&HashSet<VReg>>) -> Vec<HashSet<VReg>> {
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

/// Remap block IDs in a terminator using the provided mapping.
///
/// Returns None if the terminator becomes unreachable after remapping.
pub(crate) fn remap_terminator(term: Terminator, map: &HashMap<BlockId, BlockId>) -> Option<Terminator> {
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

/// Write a block to a function, updating existing block or appending new one.
pub(crate) fn write_block(func: &mut MirFunction, block: MirBlock) {
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
    use crate::mir::{MirInst, Visibility};

    #[test]
    fn test_reachable_from_simple() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);
        let b0 = func.new_block();
        let b1 = func.new_block();
        let b2 = func.new_block();

        func.block_mut(b0).unwrap().terminator = Terminator::Jump(b1);
        func.block_mut(b1).unwrap().terminator = Terminator::Jump(b2);
        func.block_mut(b2).unwrap().terminator = Terminator::Return(Some(VReg(0)));

        let reachable = reachable_from(&func, b0);
        assert_eq!(reachable.len(), 3);
        assert!(reachable.contains(&b0));
        assert!(reachable.contains(&b1));
        assert!(reachable.contains(&b2));
    }

    #[test]
    fn test_reachable_from_branch() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);
        let b0 = func.new_block();
        let b1 = func.new_block();
        let b2 = func.new_block();
        let b3 = func.new_block();

        func.block_mut(b0).unwrap().terminator = Terminator::Branch {
            cond: VReg(0),
            then_block: b1,
            else_block: b2,
        };
        func.block_mut(b1).unwrap().terminator = Terminator::Jump(b3);
        func.block_mut(b2).unwrap().terminator = Terminator::Jump(b3);
        func.block_mut(b3).unwrap().terminator = Terminator::Return(Some(VReg(0)));

        let reachable = reachable_from(&func, b0);
        assert_eq!(reachable.len(), 4);
    }

    #[test]
    fn test_live_after_each_inst() {
        let mut block = MirBlock::new(BlockId(0));
        block.instructions.push(MirInst::ConstInt {
            dest: VReg(1),
            value: 42,
        });
        block.instructions.push(MirInst::Copy {
            dest: VReg(2),
            src: VReg(1),
        });
        block.terminator = Terminator::Return(Some(VReg(2)));

        let mut live_out = HashSet::new();
        live_out.insert(VReg(2));

        let live_states = live_after_each_inst(&block, Some(&live_out));

        // Should have 3 states: after inst 0, after inst 1, live-out
        assert_eq!(live_states.len(), 3);
    }
}
