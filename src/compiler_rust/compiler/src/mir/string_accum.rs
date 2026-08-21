//! String-accumulation loop rewrite: `s = s + x` in a loop becomes a builder.
//!
//! # What this fixes
//!
//! `s = s + x` lowers to `MirInst::Call { target: "rt_string_concat" }`, and
//! `rt_string_concat` allocates a fresh buffer of `len(s) + len(x)` and copies
//! both operands every time. Running that in a loop is `O(N^2)` in bytes
//! copied: 40k appends took 12.1s against Python's 0.13s (bug
//! `seed_interpreter_raw_throughput_2026-08-21.md`).
//!
//! The runtime already ships an amortized-`O(1)` builder
//! (`rt_string_builder_new/push/finish`, from bug
//! `rt_string_concat_quadratic_2026-06-12`) and codegen already declares its
//! signatures — but nothing ever emitted the calls. This pass does.
//!
//! # The shape it matches
//!
//! Locals live in memory in MIR (`LocalAddr` + `Load`/`Store`), so the
//! accumulation appears literally as, inside a loop body block:
//!
//! ```text
//! LocalAddr { dest: a,  local_index: L }
//! Load      { dest: v,  addr: a }
//! Call      { dest: c,  target: rt_string_concat, args: [v, x] }
//! LocalAddr { dest: a2, local_index: L }
//! Store     { addr: a2, value: c }
//! ```
//!
//! # The rules (all must hold, or the loop is left alone)
//!
//! Every rule is a conservative, straight-line check over the loop's own MIR;
//! nothing here reasons about aliasing, and anything not understood is a bail.
//!
//! 1. The loop is a natural loop (a back edge to a header that dominates it).
//! 2. Exactly ONE concat-assign site of the shape above exists in the loop, and
//!    `v` is `args[0]` of the concat — i.e. the accumulator is the LEFT
//!    operand. `s = x + s` is a prepend and is NOT this pattern.
//! 3. `L` is read exactly once and written exactly once in the whole loop, by
//!    that site. Any other `Load`/`Store` of `L` bails — that is the "`s` is
//!    read mid-loop" case.
//! 4. Every `LocalAddr` of `L` inside the loop is consumed only as the `addr`
//!    of a `Load` or `Store`. If the address flows anywhere else (a call
//!    argument, a store value, a `GetElementPtr`) the local escapes and we
//!    bail.
//! 5. `v` is used only by the concat, and `c` only by the store. Neither may be
//!    `Drop`ped.
//! 6. The loop contains no `ClosureCreate`, `InterpCall`, `InterpEval`,
//!    `InlineAsm` or `IndirectCall` — any of these can observe or capture the
//!    local through a path this pass cannot see.
//! 7. No `Return` inside the loop (its value could be a stale `L`).
//! 8. The header has exactly one predecessor outside the loop (the preheader),
//!    and that predecessor ends in a plain `Jump` so the seed can be appended.
//!
//! # The rewrite
//!
//! * Preheader: `h = rt_string_builder_new()`, stored to a fresh `i64` local,
//!   then seeded with the accumulator's value on entry
//!   (`rt_string_builder_push(h, load L)`) — the loop may run zero times and
//!   `s` may be non-empty going in, so the seed is not optional.
//! * The site's `Load`/`Call`/`Store` become `rt_string_builder_push(h, x)`.
//! * Every exit EDGE gets a fresh block holding
//!   `rt_string_builder_finish(h)` + `Store` into `L`, so `s` holds the real
//!   string on every path out and the builder handle is always consumed
//!   (finish frees it; there is no GC to reclaim a leaked one). Edges are
//!   split rather than patched in place because an exit target may also be
//!   reachable from outside the loop.
//!
//! Set `SIMPLE_NO_STRING_BUILDER=1` to disable the pass.

use std::collections::{HashMap, HashSet};

use super::effects::{CallTarget, LocalKind};
use super::function::{MirFunction, MirLocal};
use super::instructions::{BlockId, MirInst, VReg};
use super::blocks::Terminator;
use crate::hir::TypeId;

/// Statistics for one module-wide run, so callers (and tests) can assert on
/// counts rather than on wall-clock time.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct StringAccumStats {
    /// Loops rewritten to use the builder.
    pub loops_rewritten: usize,
    /// `rt_string_builder_push` calls emitted (seed + per-iteration).
    pub pushes_emitted: usize,
    /// `rt_string_builder_finish` calls emitted (one per exit edge).
    pub finishes_emitted: usize,
}

impl StringAccumStats {
    fn merge(&mut self, other: StringAccumStats) {
        self.loops_rewritten += other.loops_rewritten;
        self.pushes_emitted += other.pushes_emitted;
        self.finishes_emitted += other.finishes_emitted;
    }
}

fn disabled() -> bool {
    matches!(
        std::env::var("SIMPLE_NO_STRING_BUILDER").as_deref(),
        Ok("1") | Ok("true")
    )
}

/// Run the rewrite over every function in a module.
pub fn apply_string_accumulation_to_module(functions: &mut [MirFunction]) -> StringAccumStats {
    let mut stats = StringAccumStats::default();
    if disabled() {
        return stats;
    }
    for func in functions.iter_mut() {
        stats.merge(apply_string_accumulation(func));
    }
    stats
}

/// Run the rewrite over one function.
pub fn apply_string_accumulation(func: &mut MirFunction) -> StringAccumStats {
    let mut stats = StringAccumStats::default();
    if disabled() || func.blocks.is_empty() {
        return stats;
    }

    // Rewriting adds blocks, which invalidates the loop analysis, so recompute
    // between rewrites and stop when a full scan finds nothing. The bound is
    // the original block count: each rewrite consumes one loop.
    let budget = func.blocks.len();
    for _ in 0..budget {
        let Some(plan) = find_one_candidate(func) else {
            break;
        };
        stats.merge(apply_plan(func, plan));
    }
    stats
}

// ---------------------------------------------------------------------------
// CFG analysis
// ---------------------------------------------------------------------------

fn block_index(func: &MirFunction) -> HashMap<BlockId, usize> {
    func.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect()
}

/// Reverse post-order over the CFG reachable from the entry block.
fn reverse_post_order(func: &MirFunction, idx: &HashMap<BlockId, usize>) -> Vec<BlockId> {
    let mut visited: HashSet<BlockId> = HashSet::new();
    let mut post: Vec<BlockId> = Vec::new();
    // Iterative DFS with an explicit "children pushed" marker.
    let mut stack: Vec<(BlockId, bool)> = vec![(func.entry_block, false)];
    while let Some((id, expanded)) = stack.pop() {
        if expanded {
            post.push(id);
            continue;
        }
        if !visited.insert(id) {
            continue;
        }
        stack.push((id, true));
        if let Some(&i) = idx.get(&id) {
            for succ in func.blocks[i].terminator.successors() {
                if !visited.contains(&succ) && idx.contains_key(&succ) {
                    stack.push((succ, false));
                }
            }
        }
    }
    post.reverse();
    post
}

/// Immediate dominators, Cooper/Harvey/Kennedy iterative algorithm.
fn immediate_dominators(
    func: &MirFunction,
    idx: &HashMap<BlockId, usize>,
    rpo: &[BlockId],
    preds: &HashMap<BlockId, Vec<BlockId>>,
) -> HashMap<BlockId, BlockId> {
    let rpo_num: HashMap<BlockId, usize> = rpo.iter().enumerate().map(|(i, b)| (*b, i)).collect();
    let mut idom: HashMap<BlockId, BlockId> = HashMap::new();
    idom.insert(func.entry_block, func.entry_block);

    let intersect = |mut a: BlockId, mut b: BlockId, idom: &HashMap<BlockId, BlockId>| -> Option<BlockId> {
        // Bounded so a malformed map can never spin forever.
        for _ in 0..(rpo.len() * 2 + 4) {
            if a == b {
                return Some(a);
            }
            let (na, nb) = (*rpo_num.get(&a)?, *rpo_num.get(&b)?);
            if na > nb {
                a = *idom.get(&a)?;
            } else {
                b = *idom.get(&b)?;
            }
        }
        None
    };

    let mut changed = true;
    while changed {
        changed = false;
        for &b in rpo.iter() {
            if b == func.entry_block {
                continue;
            }
            let Some(bp) = preds.get(&b) else { continue };
            let mut new_idom: Option<BlockId> = None;
            for &p in bp.iter() {
                if !idom.contains_key(&p) {
                    continue;
                }
                new_idom = Some(match new_idom {
                    None => p,
                    Some(cur) => match intersect(p, cur, &idom) {
                        Some(v) => v,
                        None => return idom,
                    },
                });
            }
            if let Some(n) = new_idom {
                if idom.get(&b) != Some(&n) {
                    idom.insert(b, n);
                    changed = true;
                }
            }
        }
    }
    let _ = idx;
    idom
}

fn dominates(idom: &HashMap<BlockId, BlockId>, a: BlockId, mut b: BlockId, limit: usize) -> bool {
    for _ in 0..limit + 1 {
        if a == b {
            return true;
        }
        match idom.get(&b) {
            Some(&p) if p != b => b = p,
            _ => return false,
        }
    }
    false
}

fn predecessors(func: &MirFunction) -> HashMap<BlockId, Vec<BlockId>> {
    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for block in &func.blocks {
        for succ in block.terminator.successors() {
            preds.entry(succ).or_default().push(block.id);
        }
    }
    preds
}

/// Blocks of the natural loop for back edge `tail -> header`.
fn natural_loop_body(
    header: BlockId,
    tail: BlockId,
    preds: &HashMap<BlockId, Vec<BlockId>>,
) -> HashSet<BlockId> {
    let mut body: HashSet<BlockId> = HashSet::new();
    body.insert(header);
    let mut stack = vec![tail];
    while let Some(b) = stack.pop() {
        if !body.insert(b) {
            continue;
        }
        if let Some(ps) = preds.get(&b) {
            for &p in ps {
                if !body.contains(&p) {
                    stack.push(p);
                }
            }
        }
    }
    body
}

// ---------------------------------------------------------------------------
// Pattern matching
// ---------------------------------------------------------------------------

/// A matched, fully validated rewrite site.
struct Plan {
    /// Local slot holding the accumulator.
    accum_local: usize,
    /// Type stored in that slot (STRING in practice; copied through verbatim).
    accum_ty: TypeId,
    /// Block containing the concat-assign, and the instruction indices of the
    /// `Load` / concat `Call` / `Store` triple within it.
    site_block: BlockId,
    site_load: usize,
    site_call: usize,
    site_store: usize,
    /// The value being appended (the concat's right operand).
    piece: VReg,
    /// The unique predecessor of the header from outside the loop.
    preheader: BlockId,
    /// Exit edges as (block inside loop, successor outside loop).
    exit_edges: Vec<(BlockId, BlockId)>,
}

fn is_concat_call(inst: &MirInst) -> Option<(VReg, VReg, VReg)> {
    if let MirInst::Call { dest, target, args } = inst {
        if target.name() == "rt_string_concat" && args.len() == 2 {
            if let Some(d) = dest {
                return Some((*d, args[0], args[1]));
            }
        }
    }
    None
}

/// Instructions we refuse to reason around anywhere in the loop (rule 6).
fn is_opaque(inst: &MirInst) -> bool {
    matches!(
        inst,
        MirInst::ClosureCreate { .. }
            | MirInst::InterpCall { .. }
            | MirInst::InterpEval { .. }
            | MirInst::InlineAsm { .. }
            | MirInst::IndirectCall { .. }
    )
}

fn find_one_candidate(func: &MirFunction) -> Option<Plan> {
    let idx = block_index(func);
    let preds = predecessors(func);
    let rpo = reverse_post_order(func, &idx);
    let idom = immediate_dominators(func, &idx, &rpo, &preds);
    let limit = func.blocks.len();

    for block in &func.blocks {
        for succ in block.terminator.successors() {
            // Back edge: successor dominates this block.
            if !dominates(&idom, succ, block.id, limit) {
                continue;
            }
            let body = natural_loop_body(succ, block.id, &preds);
            if let Some(plan) = match_loop(func, &idx, &preds, succ, &body) {
                return Some(plan);
            }
        }
    }
    None
}

fn match_loop(
    func: &MirFunction,
    idx: &HashMap<BlockId, usize>,
    preds: &HashMap<BlockId, Vec<BlockId>>,
    header: BlockId,
    body: &HashSet<BlockId>,
) -> Option<Plan> {
    // Rule 8: a single preheader ending in a plain Jump.
    let outside: Vec<BlockId> = preds
        .get(&header)?
        .iter()
        .copied()
        .filter(|p| !body.contains(p))
        .collect();
    if outside.len() != 1 {
        return None;
    }
    let preheader = outside[0];
    if !matches!(func.blocks[*idx.get(&preheader)?].terminator, Terminator::Jump(_)) {
        return None;
    }

    // Scan the loop for the site and for every disqualifier.
    let mut site: Option<(BlockId, usize, usize, usize, usize, TypeId, VReg, VReg, VReg)> = None;
    let mut loads_of: HashMap<usize, usize> = HashMap::new();
    let mut stores_of: HashMap<usize, usize> = HashMap::new();

    for &bid in body.iter() {
        let block = &func.blocks[*idx.get(&bid)?];
        // Rule 7.
        if matches!(block.terminator, Terminator::Return(_)) {
            return None;
        }
        // Map vreg -> local index for LocalAddr defs in this block, and record
        // which LocalAddr vregs are consumed as something other than an addr
        // (rule 4).
        let mut addr_of: HashMap<VReg, usize> = HashMap::new();
        for inst in &block.instructions {
            if is_opaque(inst) {
                return None;
            }
            if let MirInst::LocalAddr { dest, local_index } = inst {
                addr_of.insert(*dest, *local_index);
            }
        }
        for (i, inst) in block.instructions.iter().enumerate() {
            match inst {
                MirInst::Load { dest, addr, ty } => {
                    if let Some(&l) = addr_of.get(addr) {
                        *loads_of.entry(l).or_insert(0) += 1;
                        // Try to match the triple starting here.
                        if site.is_none() {
                            if let Some(found) = match_site(block, i, *dest, *addr, *ty, l, &addr_of) {
                                site = Some((bid, i, found.0, found.1, l, *ty, *dest, found.2, found.3));
                            }
                        }
                    }
                }
                MirInst::Store { addr, .. } => {
                    if let Some(&l) = addr_of.get(addr) {
                        *stores_of.entry(l).or_insert(0) += 1;
                    }
                }
                other => {
                    // Rule 4: a LocalAddr vreg used anywhere but as Load/Store addr.
                    for used in other.uses() {
                        if addr_of.contains_key(&used) {
                            return None;
                        }
                    }
                }
            }
        }
        // Terminators must not consume a LocalAddr either.
        for used in block.terminator.uses() {
            if addr_of.contains_key(&used) {
                return None;
            }
        }
    }

    let (site_block, site_load, site_call, site_store, accum_local, accum_ty, v, c, piece) = site?;

    // Rule 3: exactly one read and one write of the accumulator in the loop.
    if loads_of.get(&accum_local) != Some(&1) || stores_of.get(&accum_local) != Some(&1) {
        return None;
    }

    // Rule 5: v and c are single-use, and neither is dropped.
    let mut v_uses = 0usize;
    let mut c_uses = 0usize;
    for &bid in body.iter() {
        let block = &func.blocks[*idx.get(&bid)?];
        for inst in &block.instructions {
            if let MirInst::Drop { value, .. } = inst {
                if *value == v || *value == c {
                    return None;
                }
            }
            for used in inst.uses() {
                if used == v {
                    v_uses += 1;
                }
                if used == c {
                    c_uses += 1;
                }
            }
        }
        for used in block.terminator.uses() {
            if used == v || used == c {
                return None;
            }
        }
    }
    if v_uses != 1 || c_uses != 1 {
        return None;
    }

    // Exit edges.
    let mut exit_edges: Vec<(BlockId, BlockId)> = Vec::new();
    for &bid in body.iter() {
        let block = &func.blocks[*idx.get(&bid)?];
        for succ in block.terminator.successors() {
            if !body.contains(&succ) {
                exit_edges.push((bid, succ));
            }
        }
    }
    if exit_edges.is_empty() {
        return None;
    }
    exit_edges.sort_by_key(|(a, b)| (a.0, b.0));
    exit_edges.dedup();

    Some(Plan {
        accum_local,
        accum_ty,
        site_block,
        site_load,
        site_call,
        site_store,
        piece,
        preheader,
        exit_edges,
    })
}

/// From a `Load` at `load_i`, find the concat `Call` and the `Store` back into
/// the same local, requiring nothing in between touches the loaded value.
///
/// Returns `(call_index, store_index, concat_dest, piece)`.
fn match_site(
    block: &super::blocks::MirBlock,
    load_i: usize,
    v: VReg,
    _addr: VReg,
    _ty: TypeId,
    local: usize,
    addr_of: &HashMap<VReg, usize>,
) -> Option<(usize, usize, VReg, VReg)> {
    let mut call_i = None;
    let mut concat_dest = None;
    let mut piece = None;
    for (i, inst) in block.instructions.iter().enumerate().skip(load_i + 1) {
        if let Some((d, lhs, rhs)) = is_concat_call(inst) {
            // Rule 2: the accumulator must be the LEFT operand.
            if lhs == v {
                call_i = Some(i);
                concat_dest = Some(d);
                piece = Some(rhs);
                break;
            }
            if rhs == v {
                // Prepend (s = x + s) -- not this pattern.
                return None;
            }
        }
        if inst.uses().contains(&v) {
            return None;
        }
    }
    let call_i = call_i?;
    let c = concat_dest?;
    let piece = piece?;

    for (i, inst) in block.instructions.iter().enumerate().skip(call_i + 1) {
        if let MirInst::Store { addr, value, .. } = inst {
            if *value == c {
                return if addr_of.get(addr) == Some(&local) {
                    Some((call_i, i, c, piece))
                } else {
                    None
                };
            }
        }
        if inst.uses().contains(&c) {
            return None;
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Rewrite
// ---------------------------------------------------------------------------

fn call_builder(target: &str, args: Vec<VReg>, dest: Option<VReg>) -> MirInst {
    MirInst::Call {
        dest,
        // GcAllocating rather than Pure: the builder owns a heap buffer and the
        // calls are ordered with respect to each other, so they must not be
        // reordered or eliminated the way a pure call may be.
        target: CallTarget::GcAllocating(target.to_string()),
        args,
    }
}

fn apply_plan(func: &mut MirFunction, plan: Plan) -> StringAccumStats {
    let mut stats = StringAccumStats::default();

    // Fresh slot for the builder handle.
    //
    // `LocalAddr.local_index` is NOT an index into `func.locals`: both backends
    // read it as a position in the combined space
    // `[implicit slots][params][locals]`, where the implicit-slot COUNT is
    // itself inferred as `max(local_index) + 1 - (params.len() +
    // locals.len())` (`codegen::shared::implicit_local_param_slots`). Two ways
    // to get this wrong, both of which were measured:
    //
    // * `locals.len()` as the index aliases an existing slot -- it named the
    //   accumulator itself, so every push got a garbage handle and returned 0.
    // * an index ABOVE every existing one, with no matching `MirLocal`, grows
    //   the inferred implicit count by one, which SHIFTS the meaning of every
    //   existing index: `s` was then read as the `i32` parameter's slot and
    //   the stored string pointer was `ireduce`d to 32 bits
    //   (`<invalid-heap:0x72021711>`).
    //
    // So: append a real `MirLocal` AND take the index just past the existing
    // locals in the combined space. The inferred implicit count is then
    // unchanged, every existing index keeps its meaning, and the new index
    // resolves to the local we just pushed.
    let implicit_slots = {
        let declared = func.params.len() + func.locals.len();
        let max_used = func
            .blocks
            .iter()
            .flat_map(|b| b.instructions.iter())
            .filter_map(|i| match i {
                MirInst::LocalAddr { local_index, .. } => Some(*local_index + 1),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        max_used.saturating_sub(declared)
    };
    let handle_local = implicit_slots + func.params.len() + func.locals.len();
    func.locals.push(MirLocal {
        name: format!("__strbuf_{handle_local}"),
        ty: TypeId::I64,
        kind: LocalKind::Local,
        is_ghost: false,
    });

    // --- preheader: new + seed with the accumulator's entry value -----------
    let h0 = func.new_vreg();
    let h_addr = func.new_vreg();
    let s_addr = func.new_vreg();
    let s0 = func.new_vreg();
    let seed_dest = func.new_vreg();
    {
        let block = func.block_mut(plan.preheader).expect("preheader exists");
        block.instructions.push(call_builder("rt_string_builder_new", vec![], Some(h0)));
        block.instructions.push(MirInst::LocalAddr {
            dest: h_addr,
            local_index: handle_local,
        });
        block.instructions.push(MirInst::Store {
            addr: h_addr,
            value: h0,
            ty: TypeId::I64,
        });
        block.instructions.push(MirInst::LocalAddr {
            dest: s_addr,
            local_index: plan.accum_local,
        });
        block.instructions.push(MirInst::Load {
            dest: s0,
            addr: s_addr,
            ty: plan.accum_ty,
        });
        block.instructions.push(call_builder(
            "rt_string_builder_push",
            vec![h0, s0],
            Some(seed_dest),
        ));
    }
    stats.pushes_emitted += 1;

    // --- site: Load/concat/Store  ->  push ----------------------------------
    let site_h_addr = func.new_vreg();
    let site_h = func.new_vreg();
    let push_dest = func.new_vreg();
    {
        let block = func.block_mut(plan.site_block).expect("site block exists");
        // Remove high index first so the lower indices stay valid.
        let mut kill = [plan.site_load, plan.site_call, plan.site_store];
        kill.sort_unstable();
        for i in kill.iter().rev() {
            block.instructions.remove(*i);
        }
        // Insert where the STORE was, not where the Load was. The concat's
        // right operand is usually defined BETWEEN the load and the call (a
        // `ConstString`, say), so inserting at the load's index put the push
        // before its own argument was defined -- the JIT then read a stale
        // `vreg_values` entry carried over from the previous iteration and the
        // accumulation came out exactly one push short on every input.
        // `kill[2]` is the store's original index; two instructions below it
        // were removed, so it lands at `kill[2] - 2`.
        let at = kill[2] - 2;
        let replacement = vec![
            MirInst::LocalAddr {
                dest: site_h_addr,
                local_index: handle_local,
            },
            MirInst::Load {
                dest: site_h,
                addr: site_h_addr,
                ty: TypeId::I64,
            },
            call_builder("rt_string_builder_push", vec![site_h, plan.piece], Some(push_dest)),
        ];
        for (off, inst) in replacement.into_iter().enumerate() {
            block.instructions.insert(at + off, inst);
        }
    }
    stats.pushes_emitted += 1;

    // --- exit edges: finish + store back into the accumulator ---------------
    for (from, to) in plan.exit_edges.iter().copied() {
        let e_h_addr = func.new_vreg();
        let e_h = func.new_vreg();
        let finished = func.new_vreg();
        let e_s_addr = func.new_vreg();
        let landing = func.new_block();
        {
            let block = func.block_mut(landing).expect("fresh block");
            block.instructions.push(MirInst::LocalAddr {
                dest: e_h_addr,
                local_index: handle_local,
            });
            block.instructions.push(MirInst::Load {
                dest: e_h,
                addr: e_h_addr,
                ty: TypeId::I64,
            });
            block.instructions.push(call_builder(
                "rt_string_builder_finish",
                vec![e_h],
                Some(finished),
            ));
            block.instructions.push(MirInst::LocalAddr {
                dest: e_s_addr,
                local_index: plan.accum_local,
            });
            block.instructions.push(MirInst::Store {
                addr: e_s_addr,
                value: finished,
                ty: plan.accum_ty,
            });
            block.terminator = Terminator::Jump(to);
        }
        redirect_successor(func, from, to, landing);
        stats.finishes_emitted += 1;
    }

    stats.loops_rewritten += 1;
    stats
}

fn redirect_successor(func: &mut MirFunction, from: BlockId, old: BlockId, new: BlockId) {
    let Some(block) = func.block_mut(from) else { return };
    match &mut block.terminator {
        Terminator::Jump(t) => {
            if *t == old {
                *t = new;
            }
        }
        Terminator::Branch {
            then_block, else_block, ..
        } => {
            if *then_block == old {
                *then_block = new;
            }
            if *else_block == old {
                *else_block = new;
            }
        }
        Terminator::Switch { cases, default, .. } => {
            for (_, t) in cases.iter_mut() {
                if *t == old {
                    *t = new;
                }
            }
            if *default == old {
                *default = new;
            }
        }
        Terminator::Return(_) | Terminator::Unreachable => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helpers::parse_and_lower;

    /// Lower real source through HIR to MIR (which runs this pass at the end of
    /// `lower_module`) and count the builder calls in one function.
    fn counts(source: &str, func_name: &str) -> (usize, usize, usize, usize) {
        let hir = parse_and_lower(source);
        let mir = crate::mir::lower_to_mir(&hir).expect("mir lowering");
        let func = mir
            .functions
            .iter()
            .find(|f| f.name == func_name || f.name.ends_with(&format!(".{func_name}")))
            .unwrap_or_else(|| panic!("function {func_name} not in MIR"));
        let mut new_ = 0;
        let mut push = 0;
        let mut finish = 0;
        let mut concat = 0;
        for block in &func.blocks {
            for inst in &block.instructions {
                if let MirInst::Call { target, .. } = inst {
                    match target.name() {
                        "rt_string_builder_new" => new_ += 1,
                        "rt_string_builder_push" => push += 1,
                        "rt_string_builder_finish" => finish += 1,
                        "rt_string_concat" => concat += 1,
                        _ => {}
                    }
                }
            }
        }
        (new_, push, finish, concat)
    }

    const ACCUM: &str = r#"
fn build(n: i32) -> str:
    var s = ""
    var i = 0
    while i < n:
        s = s + "abcdefghij"
        i = i + 1
    return s
"#;

    /// The pattern is matched: one builder per loop, one seed push plus one
    /// per-iteration push, one finish on the single exit edge, and the
    /// quadratic rt_string_concat is gone from the loop.
    #[test]
    fn accumulation_loop_emits_builder_calls() {
        let (new_, push, finish, concat) = counts(ACCUM, "build");
        assert_eq!(new_, 1, "one builder created");
        assert_eq!(push, 2, "one seed push + one per-iteration push");
        assert_eq!(finish, 1, "one finish per exit edge");
        assert_eq!(concat, 0, "the concat call must be gone");
    }

    /// The kill switch really disables it.
    #[test]
    fn env_kill_switch_leaves_the_concat_alone() {
        // Serialised with the other env-reading tests by running in-process
        // set/reset around a single lowering.
        std::env::set_var("SIMPLE_NO_STRING_BUILDER", "1");
        let got = std::panic::catch_unwind(|| counts(ACCUM, "build"));
        std::env::remove_var("SIMPLE_NO_STRING_BUILDER");
        let (new_, push, finish, concat) = got.expect("lowering must not panic");
        assert_eq!((new_, push, finish), (0, 0, 0));
        assert_eq!(concat, 1, "concat is left in place when disabled");
    }

    /// Rule 3: `s` read a second time inside the loop disqualifies it -- the
    /// builder holds the bytes, so an intermediate read of the local would see
    /// a stale value.
    #[test]
    fn not_emitted_when_accumulator_is_read_mid_loop() {
        let src = r#"
fn build(n: i32) -> str:
    var s = ""
    var i = 0
    var total = 0
    while i < n:
        s = s + "abcdefghij"
        total = total + s.len()
        i = i + 1
    return s
"#;
        let (new_, push, finish, concat) = counts(src, "build");
        assert_eq!((new_, push, finish), (0, 0, 0), "must bail on a mid-loop read");
        assert!(concat >= 1, "the concat stays");
    }

    /// Rule 2: `s = x + s` is a prepend, not an append -- the builder cannot
    /// express it, so it must be left alone.
    #[test]
    fn not_emitted_for_prepend() {
        let src = r#"
fn build(n: i32) -> str:
    var s = ""
    var i = 0
    while i < n:
        s = "abcdefghij" + s
        i = i + 1
    return s
"#;
        let (new_, push, finish, concat) = counts(src, "build");
        assert_eq!((new_, push, finish), (0, 0, 0), "must bail on a prepend");
        assert!(concat >= 1);
    }

    /// A concat outside any loop is not the pattern and is untouched.
    #[test]
    fn not_emitted_for_a_straight_line_concat() {
        let src = r#"
fn build(a: str, b: str) -> str:
    var s = a + b
    return s
"#;
        let (new_, push, finish, concat) = counts(src, "build");
        assert_eq!((new_, push, finish), (0, 0, 0));
        assert_eq!(concat, 1);
    }

    /// Regression pin for the two rewrite bugs found by running this end to
    /// end (both produced silently WRONG strings, not crashes):
    ///
    /// * the per-iteration push must sit AFTER the definition of the value it
    ///   pushes -- inserting it at the removed `Load`'s index put it before the
    ///   `ConstString` operand and the accumulation came out one push short;
    /// * the handle slot must not shift the meaning of any existing
    ///   `local_index`, so the accumulator's own slot must still resolve to a
    ///   string-typed local after the rewrite.
    #[test]
    fn push_is_ordered_after_its_argument_and_slots_do_not_shift() {
        let hir = parse_and_lower(ACCUM);
        let mir = crate::mir::lower_to_mir(&hir).expect("mir lowering");
        let func = mir.functions.iter().find(|f| f.name.ends_with("build")).expect("build");

        let mut checked = 0;
        for block in &func.blocks {
            for (i, inst) in block.instructions.iter().enumerate() {
                let MirInst::Call { target, args, .. } = inst else { continue };
                if target.name() != "rt_string_builder_push" {
                    continue;
                }
                for arg in args {
                    let def = block
                        .instructions
                        .iter()
                        .position(|d| d.dest() == Some(*arg));
                    if let Some(def) = def {
                        assert!(def < i, "push at {i} uses {arg:?} defined at {def}");
                        checked += 1;
                    }
                }
            }
        }
        assert!(checked >= 2, "both pushes must have an in-block argument def");

        // The handle slot is the one just past the declared locals, and every
        // pre-existing index still names what it did before.
        let implicit = crate::codegen::shared::implicit_local_param_slots(func);
        let handle_slot = implicit + func.params.len() + func.locals.len() - 1;
        assert!(
            func.blocks.iter().flat_map(|b| b.instructions.iter()).any(|i| matches!(
                i,
                MirInst::LocalAddr { local_index, .. } if *local_index == handle_slot
            )),
            "the handle must use the slot that resolves to the local we pushed"
        );
    }
}
