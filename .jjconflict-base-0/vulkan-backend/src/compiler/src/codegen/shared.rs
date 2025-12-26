//! Shared codegen utilities used by both AOT (cranelift.rs) and JIT (jit.rs) backends.
//!
//! This module extracts common functionality to reduce code duplication.

use std::collections::HashSet;

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, Signature, UserFuncName};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module};

use crate::hir::TypeId;
use crate::mir::{
    lower_generator, LocalKind, MirFunction, MirInst, MirLocal, MirModule, Terminator, Visibility,
};

use super::types_util::type_to_cranelift;

/// Body kind for outlined functions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BodyKind {
    Actor,
    Generator,
    Future,
}

/// Create a no-op body stub function. Returns the function ID.
/// This is used by both AOT and JIT when we don't yet outline a body_block.
pub fn create_body_stub<M: Module>(
    module: &mut M,
    ctx: &mut cranelift_codegen::Context,
    name: &str,
) -> Result<cranelift_module::FuncId, String> {
    let call_conv = CallConv::SystemV;
    let sig = Signature::new(call_conv);

    let func_id = module
        .declare_function(name, Linkage::Local, &sig)
        .map_err(|e| e.to_string())?;

    ctx.func.signature = Signature::new(call_conv);
    ctx.func.name = UserFuncName::user(0, func_id.as_u32());

    {
        let mut fb_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);
        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);
        builder.ins().return_(&[]);
        builder.finalize();
    }

    module
        .define_function(func_id, ctx)
        .map_err(|e| e.to_string())?;
    module.clear_context(ctx);

    Ok(func_id)
}

/// Declare all functions in a MIR module to the Cranelift module.
/// Returns a map of function names to their FuncIds.
pub fn declare_functions<M: Module>(
    module: &mut M,
    functions: &[MirFunction],
) -> Result<std::collections::HashMap<String, cranelift_module::FuncId>, String> {
    let mut func_ids = std::collections::HashMap::new();

    for func in functions {
        let sig = build_mir_signature(func);
        let linkage = if func.is_public() {
            Linkage::Export
        } else {
            Linkage::Local
        };

        let func_id = module
            .declare_function(&func.name, linkage, &sig)
            .map_err(|e| e.to_string())?;

        func_ids.insert(func.name.clone(), func_id);
    }

    Ok(func_ids)
}

/// Build a Cranelift signature for a MIR function
pub fn build_mir_signature(func: &MirFunction) -> Signature {
    let call_conv = CallConv::SystemV;
    let mut sig = Signature::new(call_conv);

    // Add parameters
    for param in &func.params {
        let ty = type_to_cranelift(param.ty);
        sig.params.push(AbiParam::new(ty));
    }

    // Add return type
    if func.return_type != TypeId::VOID {
        let ret_ty = type_to_cranelift(func.return_type);
        sig.returns.push(AbiParam::new(ret_ty));
    }

    sig
}

/// Return a function address for an outlined MIR block.
///
/// Panics if the function is not declared in func_ids.
pub fn get_func_block_addr<M: Module>(
    func_ids: &std::collections::HashMap<String, cranelift_module::FuncId>,
    module: &mut M,
    parent_name: &str,
    block: crate::mir::BlockId,
    builder: &mut FunctionBuilder,
) -> cranelift_codegen::ir::Value {
    let name = format!("{}_outlined_{}", parent_name, block.0);
    let func_id = *func_ids
        .get(&name)
        .unwrap_or_else(|| panic!("outlined function {name} not declared"));
    let func_ref = module.declare_func_in_func(func_id, builder.func);
    builder.ins().func_addr(types::I64, func_ref)
}

/// Extract body kind from a MIR instruction if it creates an outlined body
pub fn get_body_kind(inst: &MirInst) -> Option<(crate::mir::BlockId, BodyKind)> {
    match inst {
        MirInst::ActorSpawn { body_block, .. } => Some((*body_block, BodyKind::Actor)),
        MirInst::GeneratorCreate { body_block, .. } => Some((*body_block, BodyKind::Generator)),
        MirInst::FutureCreate { body_block, .. } => Some((*body_block, BodyKind::Future)),
        _ => None,
    }
}

/// Expand MIR module with outlined functions for each body_block use.
///
/// This is used by both AOT and JIT backends to handle actors, generators, and futures
/// by extracting their body blocks into separate functions.
pub fn expand_with_outlined(mir: &MirModule) -> Vec<MirFunction> {
    let mut functions = mir.functions.clone();
    let mut seen = HashSet::new();

    for func in &mir.functions {
        let live_ins_map = func.compute_live_ins();
        for block in &func.blocks {
            for inst in &block.instructions {
                if let Some((body_block, kind)) = get_body_kind(inst) {
                    let name = format!("{}_outlined_{}", func.name, body_block.0);
                    if seen.contains(&name) {
                        continue;
                    }
                    seen.insert(name.clone());

                    // Create outlined function from parent
                    let outlined = create_outlined_function(
                        func,
                        &name,
                        body_block,
                        kind,
                        &live_ins_map,
                        &mut functions,
                    );
                    functions.push(outlined);
                }
            }
        }
    }
    functions
}

/// Create an outlined function from a parent function's body block
fn create_outlined_function(
    func: &MirFunction,
    name: &str,
    body_block: crate::mir::BlockId,
    kind: BodyKind,
    live_ins_map: &std::collections::HashMap<
        crate::mir::BlockId,
        std::collections::HashSet<crate::mir::VReg>,
    >,
    functions: &mut Vec<MirFunction>,
) -> MirFunction {
    let mut outlined = func.clone();
    outlined.name = name.to_string();
    outlined.visibility = Visibility::Private;
    outlined.entry_block = body_block;
    outlined.return_type = match kind {
        BodyKind::Generator | BodyKind::Future => crate::hir::TypeId::I64,
        BodyKind::Actor => crate::hir::TypeId::VOID,
    };
    outlined.outlined_bodies.clear();
    outlined.retain_reachable_from(body_block);

    // Only strip returns for actors (void bodies)
    if kind == BodyKind::Actor {
        for b in &mut outlined.blocks {
            if let Terminator::Return(Some(_)) = b.terminator {
                b.terminator = Terminator::Return(None);
            }
        }
    }

    // Set parameters based on body kind
    if kind == BodyKind::Generator {
        outlined.params.clear();
        outlined.params.push(MirLocal {
            name: "generator".to_string(),
            ty: crate::hir::TypeId::I64,
            kind: LocalKind::Parameter,
        });
    } else {
        outlined.params.push(MirLocal {
            name: "ctx".to_string(),
            ty: crate::hir::TypeId::I64,
            kind: LocalKind::Parameter,
        });
    }

    // Compute and record live-ins
    let mut live_ins: Vec<_> = live_ins_map
        .get(&body_block)
        .cloned()
        .unwrap_or_default()
        .into_iter()
        .collect();
    live_ins.sort_by_key(|v| v.0);

    // Update original function's metadata
    if let Some(orig) = functions.iter_mut().find(|f| f.name == func.name) {
        orig.outlined_bodies.insert(
            body_block,
            crate::mir::OutlinedBody {
                name: name.to_string(),
                live_ins: live_ins.clone(),
                frame_slots: None,
            },
        );
    }

    // Set metadata on outlined function
    outlined.outlined_bodies.insert(
        body_block,
        crate::mir::OutlinedBody {
            name: name.to_string(),
            live_ins: live_ins.clone(),
            frame_slots: None,
        },
    );

    // Handle generator lowering
    if kind == BodyKind::Generator {
        let lowered = lower_generator(&outlined, body_block);
        let slots = lowered
            .states
            .iter()
            .map(|s| s.live_after_yield.len())
            .max()
            .unwrap_or(0);

        // Update frame_slots in original
        if let Some(orig) = functions.iter_mut().find(|f| f.name == func.name) {
            if let Some(meta) = orig.outlined_bodies.get_mut(&body_block) {
                meta.frame_slots = Some(slots);
            }
        }

        let mut lowered_func = lowered.rewritten;
        if let Some(meta) = lowered_func.outlined_bodies.get_mut(&body_block) {
            meta.frame_slots = Some(slots);
        }
        lowered_func
    } else {
        outlined
    }
}
