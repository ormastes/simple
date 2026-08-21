//! Intraprocedural closure-signature propagation into `MirInst::IndirectCall`.
//!
//! # Why
//!
//! `IndirectCall` carries `param_types` / `return_type` so that a backend can
//! choose a value encoding for the call boundary. Those are filled from the
//! CALLEE EXPRESSION's static HIR type
//! (`mir::lower::lowering_expr_call::function_signature_for_callee`), which
//! works for a typed function-valued parameter but not for the overwhelmingly
//! common shape:
//!
//! ```text
//! val f = \x: x * 10
//! f(32)
//! ```
//!
//! Here the callee is a plain local. HIR types a `Lambda` expression as its
//! BODY type, never as a `HirType::Function`, so the local's type is not a
//! function type and the signature falls back to `ANY` for the result and every
//! parameter. An untyped call boundary is unimplementable for the Cranelift
//! closure ABI: a tagged encoding mis-decodes an f64, a raw encoding mis-decodes
//! an i64, and neither is right for both — which is exactly why the previous
//! closure-ABI attempt had to be reverted. See
//! `doc/08_tracking/bug/seed_jit_coverage_self_hosted_compiler_2026-08-21.md`.
//!
//! # What
//!
//! `ClosureCreate` already records the lambda's real signature
//! (`lambda_params[..].ty` and `return_type`, the latter taken from the HIR
//! body type). This pass follows that signature from the `ClosureCreate` dest
//! through the `Store`/`Load` pair that a `val` binding lowers to, and stamps
//! it onto any `IndirectCall` whose callee is one of those registers and whose
//! own types are still `ANY`.
//!
//! # Soundness
//!
//! - Only `ANY` fields are overwritten; an already-typed call site (from a real
//!   function-typed callee) is left exactly as it was.
//! - Arity must match, or nothing is written.
//! - A local that is observed to hold two DIFFERENT closure signatures is
//!   poisoned and propagates nothing, so a reassigned function-valued variable
//!   cannot be given one branch's signature.
//! - Purely intraprocedural and flow-insensitive-but-conservative: a closure
//!   that escapes the function (returned, stored in a field, passed as an
//!   argument) is simply not matched here and keeps `ANY`, which every backend
//!   must already handle.

use crate::hir::TypeId;
use crate::mir::function::MirFunction;
use crate::mir::{MirInst, MirModule, VReg};
use std::collections::HashMap;

/// A lambda's real signature: parameter types and result type.
type ClosureSig = (Vec<TypeId>, TypeId);

/// Either a known signature, or `None` for "poisoned — conflicting closures".
type SigSlot = Option<ClosureSig>;

/// Stamp inferred closure signatures onto untyped `IndirectCall` sites.
pub fn propagate_closure_call_types(module: &mut MirModule) {
    for function in &mut module.functions {
        propagate_in_function(function);
    }
}

fn merge(slot: Option<&SigSlot>, sig: ClosureSig) -> SigSlot {
    match slot {
        None => Some(sig),
        Some(None) => None,
        Some(Some(existing)) if *existing == sig => Some(sig),
        Some(Some(_)) => None,
    }
}

/// Every register in `function` that holds a closure built in this function,
/// including the ones a `val` binding produces by storing the closure into a
/// local and loading it back.
///
/// The JIT admission guard needs exactly this set: a check that only knows
/// `ClosureCreate` dest registers misses the `Load` that an `IndirectCall`
/// actually names as its callee, and would admit a module whose call boundary
/// this pass deliberately poisoned to `ANY`.
pub fn outlined_body_block_ids(function: &MirFunction) -> std::collections::HashSet<crate::mir::BlockId> {
    outlined_body_blocks(function)
}

pub fn closure_value_regs(function: &MirFunction) -> std::collections::HashSet<VReg> {
    let (reg_sig, _, _) = closure_flow(function);
    reg_sig.into_keys().collect()
}

type ClosureFlow = (
    HashMap<VReg, SigSlot>,
    HashMap<VReg, usize>,
    HashMap<usize, SigSlot>,
);

/// Blocks belonging to an outlined body (lambda / generator / future / actor).
///
/// These are still stored inside the PARENT `MirFunction` until
/// `codegen::shared::expand_with_outlined` moves them out, and they must be
/// excluded from any analysis of the parent. A lambda's parameter reuses the
/// parent's local slots (HIR truncates the lambda's locals after lowering the
/// body, so `\\x: ...` bound to `val f` gives BOTH `x` and `f` local index 0),
/// which makes the body's read of its own parameter look exactly like a load of
/// the closure. Treating it as one made every lambda look like an escaping
/// closure value.
fn outlined_body_blocks(function: &MirFunction) -> std::collections::HashSet<crate::mir::BlockId> {
    let mut roots = Vec::new();
    for block in &function.blocks {
        for inst in &block.instructions {
            match inst {
                MirInst::ClosureCreate {
                    body_block: Some(bb), ..
                } => roots.push(*bb),
                MirInst::GeneratorCreate { body_block, .. }
                | MirInst::FutureCreate { body_block, .. }
                | MirInst::ActorSpawn { body_block, .. } => roots.push(*body_block),
                _ => {}
            }
        }
    }
    let mut reachable = std::collections::HashSet::new();
    while let Some(id) = roots.pop() {
        if !reachable.insert(id) {
            continue;
        }
        if let Some(block) = function.blocks.iter().find(|b| b.id == id) {
            roots.extend(block.terminator.successors());
        }
    }
    reachable
}

fn closure_flow(function: &MirFunction) -> ClosureFlow {
    // vreg -> signature of the closure it holds
    let mut reg_sig: HashMap<VReg, SigSlot> = HashMap::new();
    // vreg -> the local it is the address of (from `LocalAddr`)
    let mut addr_local: HashMap<VReg, usize> = HashMap::new();
    // local index -> signature of the closure stored in it
    let mut local_sig: HashMap<usize, SigSlot> = HashMap::new();

    // Two forward sweeps: the second one lets a closure stored in a local
    // before a back edge reach call sites that the first sweep visited early.
    let body_blocks = outlined_body_blocks(function);
    for _ in 0..2 {
        for block in function.blocks.iter().filter(|b| !body_blocks.contains(&b.id)) {
            for inst in &block.instructions {
                match inst {
                    MirInst::ClosureCreate {
                        dest,
                        lambda_params,
                        return_type,
                        ..
                    } => {
                        let sig = (lambda_params.iter().map(|p| p.ty).collect(), *return_type);
                        let merged = merge(reg_sig.get(dest), sig);
                        reg_sig.insert(*dest, merged);
                    }
                    MirInst::LocalAddr { dest, local_index } => {
                        addr_local.insert(*dest, *local_index);
                    }
                    MirInst::Store { addr, value, .. } => {
                        let (Some(local_index), Some(Some(sig))) = (addr_local.get(addr), reg_sig.get(value)) else {
                            continue;
                        };
                        let (local_index, sig) = (*local_index, sig.clone());
                        let merged = merge(local_sig.get(&local_index), sig);
                        local_sig.insert(local_index, merged);
                    }
                    MirInst::Load { dest, addr, .. } => {
                        let (Some(local_index), Some(dest)) = (addr_local.get(addr), Some(*dest)) else {
                            continue;
                        };
                        let Some(Some(sig)) = local_sig.get(local_index) else {
                            continue;
                        };
                        let sig = sig.clone();
                        let merged = merge(reg_sig.get(&dest), sig);
                        reg_sig.insert(dest, merged);
                    }
                    _ => {}
                }
            }
        }
    }

    (reg_sig, addr_local, local_sig)
}

fn propagate_in_function(function: &mut MirFunction) {
    let (reg_sig, addr_local, local_sig) = closure_flow(function);
    let body_blocks = outlined_body_blocks(function);

    // The local that holds a closure is typed by HIR as the LAMBDA BODY's type
    // (HIR has no function type for a lambda), so `val f = \\x: x * 1.5` gives
    // the slot type f64 and the `Store`/`Load` pair moves the closure POINTER
    // as an f64 — Cranelift then rejects `load.i64` on it. The slot holds an
    // address; retype it.
    let closure_locals: Vec<usize> = local_sig
        .iter()
        .filter(|(_, sig)| sig.is_some())
        .map(|(local_index, _)| *local_index)
        .collect();
    let closure_addr_regs: std::collections::HashSet<VReg> = addr_local
        .iter()
        .filter(|(_, local_index)| closure_locals.contains(local_index))
        .map(|(reg, _)| *reg)
        .collect();

    for block in function.blocks.iter_mut().filter(|b| !body_blocks.contains(&b.id)) {
        for inst in &mut block.instructions {
            match inst {
                MirInst::Store { addr, ty, .. } if closure_addr_regs.contains(addr) => *ty = TypeId::I64,
                MirInst::Load { addr, ty, .. } if closure_addr_regs.contains(addr) => *ty = TypeId::I64,
                _ => {}
            }
        }
    }

    for block in function.blocks.iter_mut().filter(|b| !body_blocks.contains(&b.id)) {
        for inst in &mut block.instructions {
            let MirInst::IndirectCall {
                callee,
                param_types,
                return_type,
                args,
                ..
            } = inst
            else {
                continue;
            };
            let Some(Some((sig_params, sig_ret))) = reg_sig.get(callee) else {
                continue;
            };
            if sig_params.len() != args.len() || param_types.len() != args.len() {
                continue;
            }
            // The outlined lambda body is COMPILED with `sig_params`. If the
            // caller passes something else — the common case being an untyped
            // lambda parameter, which HIR defaults to I64, called with a text
            // or f64 — then handing the backend a typed boundary would make it
            // reinterpret the argument's bits. Poison the site to ANY instead;
            // the JIT admission guard refuses such a module and the interpreter
            // (which is dynamically typed) produces the right answer.
            let compatible = param_types
                .iter()
                .zip(sig_params.iter())
                .all(|(caller, callee)| *caller == TypeId::ANY || caller == callee);
            if !compatible {
                param_types.iter_mut().for_each(|slot| *slot = TypeId::ANY);
                *return_type = TypeId::ANY;
                continue;
            }
            for (slot, inferred) in param_types.iter_mut().zip(sig_params.iter()) {
                *slot = *inferred;
            }
            if *return_type == TypeId::ANY {
                *return_type = *sig_ret;
            }
        }
    }
}
