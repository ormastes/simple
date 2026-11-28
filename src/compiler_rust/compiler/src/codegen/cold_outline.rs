//! Cold-branch call outlining for the Cranelift backends (JIT and AOT).
//!
//! Root cause pinned by
//! doc/08_tracking/bug/seed_jit_never_taken_branch_calls_cost_frame_on_every_entry_2026-11-27.md:
//! Cranelift has no shrink-wrapping, so the frame of a function is set up in
//! full on every entry — every callee-saved register that ANY call sequence in
//! the function needs is spilled, and the whole frame is reserved, even when
//! the branch holding those calls is never taken. Measured on the seed JIT
//! (x86_64, this tree): 30 calls inside `if k > 5:` (never true on the hot
//! path) add `sub rsp, 0x120` plus 7 callee-saved spill slots to the
//! function's prologue, ~+1 ns on every entry; the doc measured +2.1 ns/call
//! on aarch64. Outlining those same calls into a helper called from the arm
//! is flat. This pass performs that outlining at MIR level so source does not
//! have to do it by hand.
//!
//! Transform: a conditional-branch arm block that
//! - has exactly one predecessor, reached via a conditional `Branch`,
//! - is not part of a cycle (so hot loop bodies are never outlined),
//! - contains at least `min_calls` call-like instructions,
//! - ends in `return <vreg defined in the block>`,
//! - uses only portable instructions: constants, copies, arithmetic, casts,
//!   calls, and local accesses (`LocalAddr` consumed only by `Load`/`Store`
//!   within the block). Local slots are Cranelift variables, not memory
//!   (`LocalAddr` is an index constant, see instr/memory.rs
//!   `compile_local_addr`), so a touched slot becomes one more helper
//!   parameter and every `LocalAddr` in the block is re-indexed to it; a
//!   store redefines the parameter's variable inside the helper. Raw asm and
//!   interpreter bridges make the whole block stay inline.
//! - has at most 32 parameters total (live-in vregs plus read locals), every
//!   live-in vreg carrying a known, non-void type (the uniform I64 ABI slot
//!   transports every scalar bit-transparently, floats included),
//! is replaced by a single call to a synthetic `__cold_outline_*` helper that
//! contains the block's original instructions and returns the returned vreg.
//! The helper is appended to the module's function list, so the existing
//! declaration, runtime-import, global, and reachability walks pick it up
//! exactly like a source-level helper.
//!
//! Behavior is unchanged: the moved instructions execute in the same order on
//! the only path that ever executed them; local reads see the same variable
//! values (no store can intervene — stores bail out); and no other path could
//! observe the block's vregs (the single-predecessor + return shape
//! guarantees the block defines nothing used elsewhere; the pass verifies
//! that before rewriting).
//!
//! `SIMPLE_COLD_OUTLINE_MIN_CALLS` overrides the call-count threshold
//! (default 8); `0` disables the pass. Outlining trades one extra call when
//! the arm IS taken against smaller frame setup on every entry when it is
//! not, so the threshold is deliberately conservative.

use std::collections::{HashMap, HashSet};

use crate::hir::TypeId;
use crate::mir::{BlockId, CallTarget, LocalKind, MirBlock, MirFunction, MirInst, MirLocal, Terminator, VReg, Visibility};

use super::instr::body::build_vreg_types;

/// Name prefix of synthetic outline helpers. Distinct from the
/// `__erased_none_arm_slow_*` source-level workaround helpers so the two are
/// greppable apart in traces.
pub(crate) const COLD_OUTLINE_PREFIX: &str = "__cold_outline_";

const DEFAULT_MIN_CALLS: usize = 8;
const MAX_OUTLINE_PARAMS: usize = 32;

fn min_calls_threshold() -> usize {
    std::env::var("SIMPLE_COLD_OUTLINE_MIN_CALLS")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .unwrap_or(DEFAULT_MIN_CALLS)
}

fn is_call_like(inst: &MirInst) -> bool {
    matches!(
        inst,
        MirInst::Call { .. }
            | MirInst::MethodCallStatic { .. }
            | MirInst::IndirectCall { .. }
            | MirInst::ExternMethodCall { .. }
    )
}

/// Instructions that may move into an outlined helper unchanged, local
/// reads AND writes included. Local slots are Cranelift variables, not
/// memory (`LocalAddr` is an index constant, see instr/memory.rs
/// `compile_local_addr`), so slot accesses become helper parameters and
/// every `LocalAddr` in the block is re-indexed to them. Raw asm and the
/// interpreter bridge keep their block inline by bailing out.
fn is_portable(inst: &MirInst) -> bool {
    matches!(
        inst,
        MirInst::ConstInt { .. }
            | MirInst::ConstFloat { .. }
            | MirInst::ConstBool { .. }
            | MirInst::ConstString { .. }
            | MirInst::Copy { .. }
            | MirInst::BinOp { .. }
            | MirInst::UnaryOp { .. }
            | MirInst::Cast { .. }
            | MirInst::Call { .. }
            | MirInst::MethodCallStatic { .. }
            | MirInst::IndirectCall { .. }
            | MirInst::ExternMethodCall { .. }
            | MirInst::Drop { .. }
            | MirInst::LocalAddr { .. }
            | MirInst::Load { .. }
            | MirInst::Store { .. }
    )
}

/// One local slot touched by the candidate block and how the helper
/// receives it.
#[derive(Debug)]
struct SlotPlan {
    orig_index: usize,
    ty: TypeId,
    /// `true` when a load may read the slot's incoming value (a load of the
    /// slot precedes its first store in the block). Such slots are
    /// materialized as a load at the call site — safe because the original
    /// load proves the slot is defined on every path into the block (the
    /// frontend fails closed otherwise). Otherwise the helper receives a 0
    /// placeholder: the slot is stored before any read, or never read.
    needs_incoming: bool,
}

/// One planned outline: move `block_id`'s instructions into `helper_name`.
struct Outline {
    block_id: BlockId,
    helper_name: String,
    /// Live-in vregs, in a deterministic order, becoming the first params.
    live_ins: Vec<VReg>,
    /// Types matching `live_ins` (known, non-void).
    live_in_types: Vec<TypeId>,
    /// Local slots touched by the block, sorted by original index; each
    /// becomes one more helper parameter (see `SlotPlan` for how the value
    /// is supplied).
    local_slots: Vec<SlotPlan>,
    /// The vreg the block returns; defined inside the block.
    ret_vreg: VReg,
    /// `true` when every moved call is `Pure` (the synthesized call keeps the
    /// strongest moved effect so effect metadata never lies).
    all_pure: bool,
}

fn block_is_in_cycle(func: &MirFunction, block_id: BlockId, pred: BlockId, index_of: &HashMap<BlockId, usize>) -> bool {
    // DFS from the block's successors; reaching `pred` means the block sits
    // on a cycle with its predecessor (e.g. a loop body), i.e. it is hot.
    let mut seen: HashSet<BlockId> = HashSet::new();
    let mut stack: Vec<BlockId> = func
        .blocks
        .get(index_of[&block_id])
        .map(|b| b.terminator.successors())
        .unwrap_or_default();
    while let Some(id) = stack.pop() {
        if id == pred {
            return true;
        }
        if seen.insert(id) {
            if let Some(&idx) = index_of.get(&id) {
                stack.extend(func.blocks[idx].terminator.successors());
            }
        }
    }
    false
}

fn plan_block_outlines(
    func: &MirFunction,
    min_calls: usize,
    vreg_types: &HashMap<VReg, TypeId>,
    index_of: &HashMap<BlockId, usize>,
) -> Vec<Outline> {
    // Predecessor edges: block -> predecessor blocks reached via a
    // conditional Branch (Switch arms keep their shape out of scope).
    let mut pred_edges: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for b in &func.blocks {
        if let Terminator::Branch {
            then_block, else_block, ..
        } = &b.terminator
        {
            pred_edges.entry(*then_block).or_default().push(b.id);
            pred_edges.entry(*else_block).or_default().push(b.id);
        }
    }

    // Every LocalAddr in the function: addr vreg -> local index, so a Load in
    // the candidate block through a foreign LocalAddr is caught (its slot
    // index would dangle in the helper).
    let mut addr_to_local: HashMap<VReg, usize> = HashMap::new();
    for b in &func.blocks {
        for inst in &b.instructions {
            if let MirInst::LocalAddr { dest, local_index } = inst {
                addr_to_local.insert(*dest, *local_index);
            }
        }
    }

    let live_in_sets = func.compute_live_ins();
    let mut plans = Vec::new();
    for (block_idx, block) in func.blocks.iter().enumerate() {
        if block.id == func.entry_block {
            continue;
        }
        let preds = match pred_edges.get(&block.id) {
            Some(p) if p.len() == 1 => p,
            _ => continue,
        };
        let pred = preds[0];
        if block_is_in_cycle(func, block.id, pred, index_of) {
            continue;
        }
        let call_count = block.instructions.iter().filter(|i| is_call_like(i)).count();
        if call_count < min_calls {
            continue;
        }
        // Return shape: `return <vreg defined in this block>`.
        let ret_vreg = match &block.terminator {
            Terminator::Return(Some(v)) => *v,
            _ => continue,
        };
        let defs_here: HashSet<VReg> = block.instructions.iter().filter_map(|i| i.dest()).collect();
        if !defs_here.contains(&ret_vreg) {
            continue;
        }
        if !block.instructions.iter().all(is_portable) {
            continue;
        }

        // Local slots: walk the block in order. Every LocalAddr must be
        // consumed in-block (by Load or Store — anything else escapes), and
        // every Load through a LocalAddr-defined address must use one from
        // this block (a foreign one would dangle in the helper). A slot's
        // load and store types must agree. Whether a slot needs its incoming
        // value depends purely on program order within the block.
        let mut own_addrs: HashMap<VReg, usize> = HashMap::new();
        for inst in &block.instructions {
            if let MirInst::LocalAddr { dest, local_index } = inst {
                own_addrs.insert(*dest, *local_index);
            }
        }
        let mut slots: HashMap<usize, SlotPlan> = HashMap::new();
        let mut slots_ok = true;
        let mut seen_store: HashSet<usize> = HashSet::new();
        let mut record_ty = |slots: &mut HashMap<usize, SlotPlan>, idx: usize, ty: TypeId, ok: &mut bool| {
            match slots.get(&idx) {
                Some(plan) if plan.ty != ty => *ok = false,
                None => {
                    slots.insert(
                        idx,
                        SlotPlan {
                            orig_index: idx,
                            ty,
                            needs_incoming: false,
                        },
                    );
                }
                _ => {}
            }
        };
        for inst in &block.instructions {
            match inst {
                MirInst::LocalAddr { .. } => {}
                MirInst::Load { addr, ty, .. } => {
                    if let Some(&idx) = own_addrs.get(addr) {
                        record_ty(&mut slots, idx, *ty, &mut slots_ok);
                        // A load before the slot's first store reads the
                        // incoming value; one after reads the helper's copy.
                        if !seen_store.contains(&idx) {
                            slots.get_mut(&idx).expect("recorded").needs_incoming = true;
                        }
                    } else if addr_to_local.contains_key(addr) {
                        // Defined by a LocalAddr outside this block: the
                        // remapped helper would read its own slot instead.
                        slots_ok = false;
                    }
                }
                MirInst::Store { addr, ty, .. } => {
                    match own_addrs.get(addr) {
                        Some(&idx) => {
                            record_ty(&mut slots, idx, *ty, &mut slots_ok);
                            seen_store.insert(idx);
                        }
                        // Storing through a non-local address (raw pointer)
                        // cannot be remapped.
                        None => slots_ok = false,
                    }
                }
                _ => {}
            }
        }
        // Every own LocalAddr must have at least one in-block consumer, and
        // no consumer anywhere else in the function.
        for (addr, _idx) in &own_addrs {
            let mut consumers = 0usize;
            for inst in &block.instructions {
                if inst.uses().iter().any(|u| u == addr) {
                    consumers += 1;
                }
            }
            if consumers == 0 {
                slots_ok = false;
            }
            for (i, b) in func.blocks.iter().enumerate() {
                if i == block_idx {
                    continue;
                }
                let foreign_uses = b
                    .instructions
                    .iter()
                    .flat_map(|inst| inst.uses())
                    .chain(b.terminator.uses())
                    .any(|u| u == *addr);
                if foreign_uses {
                    slots_ok = false;
                }
            }
        }
        let mut local_slots: Vec<SlotPlan> = slots.into_values().collect();
        local_slots.sort_by_key(|s| s.orig_index);
        if !slots_ok {
            continue;
        }

        // Live-in vregs must carry a known, non-void type so the helper
        // parameter can be declared faithfully.
        let live_in_set = match live_in_sets.get(&block.id) {
            Some(s) => s,
            None => continue,
        };
        if live_in_set.len() + local_slots.len() > MAX_OUTLINE_PARAMS {
            continue;
        }
        let mut live_ins: Vec<VReg> = live_in_set.iter().copied().collect();
        live_ins.sort_by_key(|v| v.0);
        let mut live_in_types = Vec::with_capacity(live_ins.len());
        let mut ok = true;
        for v in &live_ins {
            match vreg_types.get(v) {
                Some(ty) if *ty != TypeId::VOID => live_in_types.push(*ty),
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }

        // The block's own defs (including its LocalAddr/Load results) must
        // not be used anywhere else; the single-predecessor + return shape
        // makes that the SSA rule, and this verifies it before rewriting.
        let mut used_elsewhere = false;
        for (i, b) in func.blocks.iter().enumerate() {
            if i == block_idx {
                continue;
            }
            let uses: HashSet<VReg> = b
                .instructions
                .iter()
                .flat_map(|inst| inst.uses())
                .chain(b.terminator.uses())
                .collect();
            if uses.iter().any(|u| defs_here.contains(u)) {
                used_elsewhere = true;
                break;
            }
        }
        if used_elsewhere {
            continue;
        }

        let all_pure = block
            .instructions
            .iter()
            .filter_map(|inst| match inst {
                MirInst::Call { target, .. } => Some(target),
                _ => None,
            })
            .all(|t| matches!(t, CallTarget::Pure(_)));
        plans.push(Outline {
            block_id: block.id,
            helper_name: format!("{}{}_{}", COLD_OUTLINE_PREFIX, func.name, block.id.0),
            live_ins,
            live_in_types,
            local_slots,
            ret_vreg,
            all_pure,
        });
    }
    plans
}

fn build_helper(func: &MirFunction, plan: &Outline) -> MirFunction {
    let mut helper = MirFunction::new(plan.helper_name.clone(), func.return_type, Visibility::Private);
    helper.module_path = func.module_path.clone();
    helper.effects = func.effects.clone();
    helper.inferred_effect = func.inferred_effect.clone();
    let mut local_remap: HashMap<usize, usize> = HashMap::new();
    for (i, ty) in plan.live_in_types.iter().enumerate() {
        helper.params.push(MirLocal {
            name: format!("cold_p{i}"),
            ty: *ty,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
    }
    for (offset, slot) in plan.local_slots.iter().enumerate() {
        // Touched locals ride along as trailing parameters; the helper has
        // no implicit slots, so parameter i owns variable slot i. A store in
        // the block redefines the parameter's variable — the frontend treats
        // parameters as mutable locals, exactly like the caller's slot.
        let param_index = plan.live_in_types.len() + offset;
        local_remap.insert(slot.orig_index, param_index);
        helper.params.push(MirLocal {
            name: format!("cold_l{}", slot.orig_index),
            ty: slot.ty,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
    }
    let block = func
        .blocks
        .iter()
        .find(|b| b.id == plan.block_id)
        .expect("planned block exists");
    let mut helper_block = MirBlock::new(BlockId(0));
    helper_block.instructions = block
        .instructions
        .iter()
        .map(|inst| match inst {
            MirInst::LocalAddr { dest, local_index } => MirInst::LocalAddr {
                dest: *dest,
                local_index: local_remap[local_index],
            },
            other => other.clone(),
        })
        .collect();
    helper_block.terminator = Terminator::Return(Some(plan.ret_vreg));
    helper.blocks = vec![helper_block];
    helper.entry_block = BlockId(0);
    let max_vreg = helper
        .blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .flat_map(|i| i.dest().into_iter().chain(i.uses()))
        .chain(std::iter::once(plan.ret_vreg))
        .map(|v| v.0)
        .max()
        .unwrap_or(0);
    helper.set_vreg_counter(max_vreg + 1);
    helper
}

/// Apply one outline to `func`, appending the synthetic helper to `helpers`.
fn apply_outline(func: &mut MirFunction, plan: &Outline, helpers: &mut Vec<MirFunction>) {
    helpers.push(build_helper(func, plan));
    let target = if plan.all_pure {
        CallTarget::Pure(plan.helper_name.clone())
    } else {
        CallTarget::Io(plan.helper_name.clone())
    };
    // Materialize the incoming slot values at the call site, in the same
    // order the helper declares them; slots written before any read get a 0
    // placeholder (their incoming value is unread). Then the outlining call.
    let mut args = plan.live_ins.clone();
    let mut materialized: Vec<MirInst> = Vec::new();
    for slot in &plan.local_slots {
        if slot.needs_incoming {
            let addr = func.new_vreg();
            let value = func.new_vreg();
            materialized.push(MirInst::LocalAddr {
                dest: addr,
                local_index: slot.orig_index,
            });
            materialized.push(MirInst::Load {
                dest: value,
                addr,
                ty: slot.ty,
            });
            args.push(value);
        } else {
            let placeholder = func.new_vreg();
            materialized.push(MirInst::ConstInt {
                dest: placeholder,
                value: 0,
            });
            args.push(placeholder);
        }
    }
    let result = func.new_vreg();
    let block = func
        .blocks
        .iter_mut()
        .find(|b| b.id == plan.block_id)
        .expect("planned block exists");
    materialized.push(MirInst::Call {
        dest: Some(result),
        target,
        args,
    });
    block.instructions = materialized;
    block.terminator = Terminator::Return(Some(result));
}

/// Outline call-heavy conditional arms that return, so their frame cost is
/// paid only when the arm is taken. Returns the function list with helpers
/// appended; functions that qualify for nothing pass through unchanged.
pub fn outline_cold_branch_calls(
    functions: Vec<MirFunction>,
    function_return_types: &HashMap<String, TypeId>,
) -> Vec<MirFunction> {
    let min_calls = min_calls_threshold();
    if min_calls == 0 {
        return functions;
    }
    let mut functions = functions;
    let mut helpers = Vec::new();
    let original_len = functions.len();
    for idx in 0..original_len {
        let func = &functions[idx];
        if func.blocks.is_empty()
            || func.name.starts_with(COLD_OUTLINE_PREFIX)
            || func.attributes.iter().any(|a| a == "naked")
            || func.generator_states.is_some()
            || func.async_states.is_some()
            || func.is_generic_template
        {
            continue;
        }
        let index_of: HashMap<BlockId, usize> = func.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect();
        let vreg_types = build_vreg_types(func, function_return_types);
        let plans = plan_block_outlines(func, min_calls, &vreg_types, &index_of);
        if plans.is_empty() {
            continue;
        }
        let mut func = functions[idx].clone();
        for plan in &plans {
            apply_outline(&mut func, plan, &mut helpers);
        }
        functions[idx] = func;
    }
    functions.extend(helpers);
    functions
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::BinOp;

    fn i64_param(name: &str) -> MirLocal {
        MirLocal {
            name: name.to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: false,
        }
    }

    /// Build `g(k)`: hot path returns k+1; cold arm `if k > 5` performs 8
    /// calls (reading the param slot for each) and returns their last result.
    fn cold_arm_module(with_calls: usize) -> MirFunction {
        let mut func = MirFunction::new("g".to_string(), TypeId::I64, Visibility::Private);
        func.params.push(i64_param("k"));
        let k_local = 0usize; // params occupy local slot 0
        let k_addr = func.new_vreg();
        let k = func.new_vreg();
        let five = func.new_vreg();
        let cond = func.new_vreg();
        let mut entry = MirBlock::new(BlockId(0));
        entry.instructions = vec![
            MirInst::LocalAddr {
                dest: k_addr,
                local_index: k_local,
            },
            MirInst::Load {
                dest: k,
                addr: k_addr,
                ty: TypeId::I64,
            },
            MirInst::ConstInt { dest: five, value: 5 },
            MirInst::BinOp {
                dest: cond,
                op: BinOp::Gt,
                left: k,
                right: five,
            },
        ];
        entry.terminator = Terminator::Branch {
            cond,
            then_block: BlockId(1),
            else_block: BlockId(2),
        };
        let mut cold = MirBlock::new(BlockId(1));
        let mut insts = vec![];
        let mut last = None;
        for i in 0..with_calls {
            let addr = func.new_vreg();
            let kv = func.new_vreg();
            let c = func.new_vreg();
            let d = func.new_vreg();
            insts.push(MirInst::LocalAddr {
                dest: addr,
                local_index: k_local,
            });
            insts.push(MirInst::Load {
                dest: kv,
                addr,
                ty: TypeId::I64,
            });
            insts.push(MirInst::ConstInt { dest: c, value: (i + 1) as i64 });
            insts.push(MirInst::Call {
                dest: Some(d),
                target: CallTarget::Pure("h".to_string()),
                args: vec![kv, c],
            });
            last = Some(d);
        }
        let ret = func.new_vreg();
        insts.push(MirInst::Copy {
            dest: ret,
            src: last.unwrap(),
        });
        cold.instructions = insts;
        cold.terminator = Terminator::Return(Some(ret));
        let mut hot = MirBlock::new(BlockId(2));
        let one = func.new_vreg();
        let hot_ret = func.new_vreg();
        hot.instructions = vec![
            MirInst::ConstInt { dest: one, value: 1 },
            MirInst::BinOp {
                dest: hot_ret,
                op: BinOp::Add,
                left: k,
                right: one,
            },
        ];
        hot.terminator = Terminator::Return(Some(hot_ret));
        func.blocks = vec![entry, cold, hot];
        func.entry_block = BlockId(0);
        func.set_vreg_counter(1000);
        func
    }

    fn return_types() -> HashMap<String, TypeId> {
        let mut m = HashMap::new();
        m.insert("h".to_string(), TypeId::I64);
        m
    }

    #[test]
    fn outlines_cold_arm_with_enough_calls() {
        let out = outline_cold_branch_calls(vec![cold_arm_module(8)], &return_types());
        assert_eq!(
            out.len(),
            2,
            "helper appended: {:?}",
            out.iter().map(|f| &f.name).collect::<Vec<_>>()
        );
        let g = out.iter().find(|f| f.name == "g").unwrap();
        let cold_block = g.blocks.iter().find(|b| b.id == BlockId(1)).unwrap();
        assert!(
            matches!(cold_block.instructions.last(), Some(MirInst::Call { .. })),
            "cold arm collapses to materializing loads plus one call: {:?}",
            cold_block.instructions
        );
        let helper = out.iter().find(|f| f.name.starts_with(COLD_OUTLINE_PREFIX)).unwrap();
        assert_eq!(helper.params.len(), 1, "the k slot is the only parameter");
        assert_eq!(helper.return_type, TypeId::I64);
        assert!(matches!(helper.blocks[0].terminator, Terminator::Return(Some(_))));
        assert_eq!(
            helper.blocks[0].instructions.iter().filter(|i| is_call_like(i)).count(),
            8,
            "all eight calls moved verbatim"
        );
        // The helper's LocalAddr now targets its own parameter slot 0.
        assert!(helper.blocks[0].instructions.iter().all(|i| {
            match i {
                MirInst::LocalAddr { local_index, .. } => *local_index == 0,
                _ => true,
            }
        }));
    }

    #[test]
    fn keeps_small_arms_inline() {
        let out = outline_cold_branch_calls(vec![cold_arm_module(3)], &return_types());
        assert_eq!(out.len(), 1, "below threshold: no helper");
    }

    /// A block whose defs are used elsewhere is left alone (SSA safety).
    #[test]
    fn keeps_block_when_defs_escape() {
        let mut func = cold_arm_module(8);
        // Make the hot arm read a vreg defined inside the cold arm.
        let cold_shared = func.blocks[1]
            .instructions
            .iter()
            .find_map(|i| match i {
                MirInst::Call { dest: Some(d), .. } => Some(*d),
                _ => None,
            })
            .unwrap();
        let hot_ret = func.new_vreg();
        func.blocks[2].instructions.push(MirInst::Copy {
            dest: hot_ret,
            src: cold_shared,
        });
        func.blocks[2].terminator = Terminator::Return(Some(hot_ret));
        let out = outline_cold_branch_calls(vec![func], &return_types());
        assert_eq!(out.len(), 1, "escaping def: no outline");
    }

    /// A store to a slot that is never read before the store moves with the
    /// block: the helper receives a 0 placeholder and redefines its own
    /// parameter variable, exactly like the caller's slot on that path.
    #[test]
    fn outlines_block_with_local_store() {
        let mut func = cold_arm_module(8);
        let addr = func.new_vreg();
        let zero = func.new_vreg();
        func.blocks[1].instructions.insert(
            0,
            MirInst::LocalAddr {
                dest: addr,
                local_index: 9,
            },
        );
        func.blocks[1]
            .instructions
            .insert(1, MirInst::ConstInt { dest: zero, value: 0 });
        func.blocks[1].instructions.insert(
            2,
            MirInst::Store {
                addr,
                value: zero,
                ty: TypeId::I64,
            },
        );
        let out = outline_cold_branch_calls(vec![func], &return_types());
        assert_eq!(out.len(), 2, "store-only slot: helper still created");
        let helper = out.iter().find(|f| f.name.starts_with(COLD_OUTLINE_PREFIX)).unwrap();
        assert!(
            helper.blocks[0]
                .instructions
                .iter()
                .any(|i| matches!(i, MirInst::Store { .. })),
            "the store moved verbatim"
        );
        assert_eq!(helper.params.len(), 2, "k slot plus the stored slot");
        let g = out.iter().find(|f| f.name == "g").unwrap();
        let cold_block = g.blocks.iter().find(|b| b.id == BlockId(1)).unwrap();
        assert!(
            cold_block.instructions.iter().any(|i| matches!(i, MirInst::ConstInt { value: 0, .. })),
            "store-only slot is supplied as a 0 placeholder, no load"
        );
        assert!(
            !cold_block.instructions.iter().any(|i| matches!(i, MirInst::Store { .. })),
            "no store remains in the caller"
        );
    }

    /// A slot read BEFORE its first store keeps the incoming value: the call
    /// site materializes a load for it.
    #[test]
    fn read_before_store_materializes_incoming() {
        let mut func = cold_arm_module(8);
        // Prepend: load slot 9, then store slot 9 — the load must see the
        // caller's value.
        let a1 = func.new_vreg();
        let v1 = func.new_vreg();
        let a2 = func.new_vreg();
        let v2 = func.new_vreg();
        let prepend = vec![
            MirInst::LocalAddr {
                dest: a1,
                local_index: 9,
            },
            MirInst::Load {
                dest: v1,
                addr: a1,
                ty: TypeId::I64,
            },
            MirInst::LocalAddr {
                dest: a2,
                local_index: 9,
            },
            MirInst::Store {
                addr: a2,
                value: v1,
                ty: TypeId::I64,
            },
        ];
        for (at, inst) in prepend.into_iter().enumerate() {
            func.blocks[1].instructions.insert(at, inst);
        }
        // Make the block use the loaded value so the load stays live.
        let ret = match &func.blocks[1].terminator {
            Terminator::Return(Some(v)) => *v,
            _ => panic!("test shape"),
        };
        let sum = func.new_vreg();
        func.blocks[1].instructions.push(MirInst::BinOp {
            dest: sum,
            op: BinOp::Add,
            left: v1,
            right: ret,
        });
        let out = outline_cold_branch_calls(vec![func], &return_types());
        assert_eq!(out.len(), 2, "read-before-store slot: helper created");
        let g = out.iter().find(|f| f.name == "g").unwrap();
        let cold_block = g.blocks.iter().find(|b| b.id == BlockId(1)).unwrap();
        assert!(
            cold_block.instructions.iter().any(|i| matches!(i, MirInst::Load { .. })),
            "incoming value materialized as a load at the call site"
        );
        assert!(
            !cold_block
                .instructions
                .iter()
                .any(|i| matches!(i, MirInst::ConstInt { value: 0, .. })),
            "no placeholder for a slot that reads the incoming value"
        );
    }
}
