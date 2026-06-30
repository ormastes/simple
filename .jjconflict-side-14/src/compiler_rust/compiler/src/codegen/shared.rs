//! Shared codegen utilities used by both AOT (cranelift.rs) and JIT (jit.rs) backends.
//!
//! This module extracts common functionality to reduce code duplication.

use std::collections::{HashMap, HashSet};

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, Signature, UserFuncName};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module};

use crate::hir::TypeId;
use crate::mir::{
    lower_generator, LambdaParamBinding, LocalKind, MirFunction, MirInst, MirLocal, MirModule, Terminator, Visibility,
};

use super::types_util::type_to_cranelift;

/// Return the platform-appropriate calling convention.
///
/// On Windows, Cranelift JIT-compiled code must use WindowsFastcall to match
/// the ABI that Rust `fn()` pointers expect. On other platforms, SystemV is used.
pub fn platform_call_conv() -> CallConv {
    if cfg!(target_os = "windows") {
        CallConv::WindowsFastcall
    } else {
        CallConv::SystemV
    }
}

/// Body kind for outlined functions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BodyKind {
    Actor,
    Generator,
    Future,
    Lambda,
}

/// Create a no-op body stub function. Returns the function ID.
/// This is used by both AOT and JIT when we don't yet outline a body_block.
pub fn create_body_stub<M: Module>(
    module: &mut M,
    ctx: &mut cranelift_codegen::Context,
    name: &str,
) -> Result<cranelift_module::FuncId, String> {
    let call_conv = platform_call_conv();
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

    module.define_function(func_id, ctx).map_err(|e| e.to_string())?;
    module.clear_context(ctx);

    Ok(func_id)
}

/// Declare all functions in a MIR module to the Cranelift module.
/// Returns a map of function names to their FuncIds.
pub fn declare_functions<M: Module>(
    module: &mut M,
    functions: &[MirFunction],
) -> Result<std::collections::BTreeMap<String, cranelift_module::FuncId>, String> {
    let mut func_ids = std::collections::BTreeMap::new();

    for func in functions {
        // Skip if already declared (handles duplicate functions in MIR)
        if func_ids.contains_key(&func.name) {
            continue;
        }

        let sig = build_mir_signature(func);

        // Determine linkage:
        // - Extern functions (empty blocks) use Import linkage
        // - "main" is always exported for native binary compatibility
        // - Other functions use Export (public) or Local (private) based on visibility
        let linkage = if func.blocks.is_empty() {
            Linkage::Import
        } else if func.is_public() || func.name == "main" {
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

/// Build a Cranelift signature for a MIR function.
///
/// Uses uniform I64 for all parameters and returns to match cross-module
/// import convention. All Simple values are i64-tagged at the ABI level,
/// and function body variables are declared as I64 (body.rs).
/// `adapt_args_to_signature` handles type conversions at call sites.
pub fn build_mir_signature(func: &MirFunction) -> Signature {
    let call_conv = platform_call_conv();
    let mut sig = Signature::new(call_conv);
    let runtime_param_types = crate::codegen::runtime_sffi::RUNTIME_FUNCS
        .iter()
        .find(|spec| spec.name == func.name)
        .and_then(|spec| {
            if spec.params.len() == func.params.len()
                && spec
                    .params
                    .iter()
                    .zip(func.params.iter())
                    .all(|(runtime_ty, param)| *runtime_ty == type_to_cranelift(param.ty))
            {
                Some(spec.params)
            } else {
                None
            }
        });

    // User functions use uniform I64 parameters for cross-module imports.
    // Pure-Simple runtime helpers may opt into exact runtime ABI parameters
    // when their declared Simple parameter types already match the runtime
    // table. This lets simple-core provide narrow ABI symbols like rt_enum_new.
    let implicit_local_params = implicit_local_param_slots(func);

    if let Some(params) = runtime_param_types {
        for param_ty in params {
            sig.params.push(AbiParam::new(*param_ty));
        }
    } else {
        for _ in 0..implicit_local_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        for _param in &func.params {
            sig.params.push(AbiParam::new(types::I64));
        }
    }

    // Return type: main() must return I32 for process exit code.
    // All other functions get I64 return — Simple semantics guarantee every
    // function returns a value (nil when no explicit return), and MIR
    // return_type is VOID for inferred-return functions.
    if func.name == "main" {
        sig.returns.push(AbiParam::new(types::I32));
    } else {
        let runtime_return = crate::codegen::runtime_sffi::RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == func.name)
            .and_then(|spec| spec.returns.first().copied());
        sig.returns.push(AbiParam::new(runtime_return.unwrap_or(types::I64)));
    }

    sig
}

pub fn implicit_local_param_slots(func: &MirFunction) -> usize {
    let declared_slots = func.params.len() + func.locals.len();
    let mut max_local_index = None;
    for block in &func.blocks {
        for inst in &block.instructions {
            if let crate::mir::MirInst::LocalAddr { local_index, .. } = inst {
                max_local_index = Some(max_local_index.map_or(*local_index, |cur: usize| cur.max(*local_index)));
            }
        }
    }

    match max_local_index {
        Some(max_idx) if max_idx + 1 > declared_slots => (max_idx + 1) - declared_slots,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::{BlockId, VReg};

    fn param(name: &str, ty: TypeId) -> MirLocal {
        MirLocal {
            name: name.to_string(),
            ty,
            kind: LocalKind::Parameter,
            is_ghost: false,
        }
    }

    #[test]
    fn runtime_helper_uses_exact_params_when_simple_decl_matches_runtime_abi() {
        let mut func = MirFunction::new("rt_enum_new".to_string(), TypeId::I64, Visibility::Public);
        func.params.push(param("enum_id", TypeId::I32));
        func.params.push(param("discriminant", TypeId::I32));
        func.params.push(param("payload", TypeId::I64));

        let sig = build_mir_signature(&func);

        assert_eq!(sig.params[0].value_type, types::I32);
        assert_eq!(sig.params[1].value_type, types::I32);
        assert_eq!(sig.params[2].value_type, types::I64);
        assert_eq!(sig.returns[0].value_type, types::I64);
    }

    #[test]
    fn runtime_helper_keeps_uniform_params_when_simple_decl_does_not_match_runtime_abi() {
        let mut func = MirFunction::new("rt_enum_new".to_string(), TypeId::I64, Visibility::Public);
        func.params.push(param("enum_id", TypeId::I64));
        func.params.push(param("discriminant", TypeId::I64));
        func.params.push(param("payload", TypeId::I64));

        let sig = build_mir_signature(&func);

        assert_eq!(sig.params[0].value_type, types::I64);
        assert_eq!(sig.params[1].value_type, types::I64);
        assert_eq!(sig.params[2].value_type, types::I64);
        assert_eq!(sig.returns[0].value_type, types::I64);
    }

    #[test]
    fn outlined_lambda_preserves_user_params_after_ctx() {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        func.locals.push(MirLocal {
            name: "$lambda_param_a_hole".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: false,
        });
        func.locals.push(MirLocal {
            name: "$lambda_param_b_hole".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: false,
        });
        func.locals.push(MirLocal {
            name: "temp".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: false,
        });

        let body_block = func.new_block();
        func.block_mut(body_block).unwrap().instructions.extend([
            MirInst::LocalAddr {
                dest: VReg(10),
                local_index: 0,
            },
            MirInst::LocalAddr {
                dest: VReg(11),
                local_index: 1,
            },
            MirInst::LocalAddr {
                dest: VReg(12),
                local_index: 2,
            },
        ]);
        func.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(VReg(10)));
        func.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ClosureCreate {
                dest: VReg(0),
                func_name: "main_outlined_1".to_string(),
                closure_size: 8,
                capture_offsets: vec![],
                capture_types: vec![],
                captures: vec![],
                lambda_params: vec![
                    LambdaParamBinding {
                        local_index: 0,
                        name: "a".to_string(),
                        ty: TypeId::I64,
                    },
                    LambdaParamBinding {
                        local_index: 1,
                        name: "b".to_string(),
                        ty: TypeId::I64,
                    },
                ],
                body_block: Some(body_block),
            });

        let mut module = MirModule::new();
        module.functions.push(func);

        let expanded = expand_with_outlined(&module);
        let outlined = expanded.iter().find(|f| f.name == "main_outlined_1").unwrap();
        let param_names: Vec<_> = outlined.params.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(param_names, vec!["ctx", "a", "b"]);

        let local_indices: Vec<_> = outlined
            .block(body_block)
            .unwrap()
            .instructions
            .iter()
            .filter_map(|inst| match inst {
                MirInst::LocalAddr { local_index, .. } => Some(*local_index),
                _ => None,
            })
            .collect();
        assert_eq!(local_indices, vec![1, 2, 5]);
    }

    #[test]
    fn outlined_lambda_maps_captured_parent_param_and_local_to_closure_slots() {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        func.params.push(param("seed_param", TypeId::I64));
        func.locals.push(MirLocal {
            name: "seed_local".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: false,
        });

        let body_block = func.new_block();
        func.block_mut(body_block).unwrap().instructions.extend([
            MirInst::LocalAddr {
                dest: VReg(10),
                local_index: 0,
            },
            MirInst::LocalAddr {
                dest: VReg(11),
                local_index: 1,
            },
        ]);
        func.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(VReg(10)));
        func.block_mut(BlockId(0)).unwrap().instructions.extend([
            MirInst::LocalAddr {
                dest: VReg(20),
                local_index: 0,
            },
            MirInst::Load {
                dest: VReg(21),
                addr: VReg(20),
                ty: TypeId::I64,
            },
            MirInst::LocalAddr {
                dest: VReg(22),
                local_index: 1,
            },
            MirInst::Load {
                dest: VReg(23),
                addr: VReg(22),
                ty: TypeId::I64,
            },
            MirInst::ClosureCreate {
                dest: VReg(0),
                func_name: "main_outlined_1".to_string(),
                closure_size: 24,
                capture_offsets: vec![8, 16],
                capture_types: vec![TypeId::I64, TypeId::I64],
                captures: vec![VReg(21), VReg(23)],
                lambda_params: vec![],
                body_block: Some(body_block),
            },
        ]);

        let mut module = MirModule::new();
        module.functions.push(func);

        let expanded = expand_with_outlined(&module);
        let outlined = expanded.iter().find(|f| f.name == "main_outlined_1").unwrap();
        let meta = outlined.outlined_bodies.get(&body_block).unwrap();
        assert!(meta.is_lambda);
        assert_eq!(meta.lambda_capture_local_indices, vec![2, 3]);
        let local_names: Vec<_> = outlined.locals.iter().map(|local| local.name.as_str()).collect();
        assert_eq!(
            local_names,
            vec!["seed_local", "$lambda_capture_0", "$lambda_capture_1"]
        );

        let local_indices: Vec<_> = outlined
            .block(body_block)
            .unwrap()
            .instructions
            .iter()
            .filter_map(|inst| match inst {
                MirInst::LocalAddr { local_index, .. } => Some(*local_index),
                _ => None,
            })
            .collect();
        assert_eq!(local_indices, vec![2, 3]);
    }
}

/// Return a function address for an outlined MIR block.
///
/// Panics if the function is not declared in func_ids.
pub fn get_func_block_addr<M: Module>(
    func_ids: &std::collections::BTreeMap<String, cranelift_module::FuncId>,
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
pub fn get_body_kind(
    inst: &MirInst,
) -> Option<(
    crate::mir::BlockId,
    BodyKind,
    Vec<LambdaParamBinding>,
    Vec<crate::mir::VReg>,
)> {
    match inst {
        MirInst::ActorSpawn { body_block, .. } => Some((*body_block, BodyKind::Actor, Vec::new(), Vec::new())),
        MirInst::GeneratorCreate { body_block, .. } => Some((*body_block, BodyKind::Generator, Vec::new(), Vec::new())),
        MirInst::FutureCreate { body_block, .. } => Some((*body_block, BodyKind::Future, Vec::new(), Vec::new())),
        MirInst::ClosureCreate {
            body_block: Some(bb),
            lambda_params,
            captures,
            ..
        } => Some((*bb, BodyKind::Lambda, lambda_params.clone(), captures.clone())),
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
            for (inst_index, inst) in block.instructions.iter().enumerate() {
                if let Some((body_block, kind, lambda_params, capture_regs)) = get_body_kind(inst) {
                    let name = format!("{}_outlined_{}", func.name, body_block.0);
                    if seen.contains(&name) {
                        continue;
                    }
                    seen.insert(name.clone());
                    let capture_local_indices = if kind == BodyKind::Lambda {
                        lambda_capture_local_indices(block, inst_index, &capture_regs)
                    } else {
                        Vec::new()
                    };

                    // Create outlined function from parent
                    let outlined = create_outlined_function(
                        func,
                        &name,
                        body_block,
                        kind,
                        &lambda_params,
                        &capture_local_indices,
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
    lambda_params: &[LambdaParamBinding],
    capture_local_indices: &[usize],
    live_ins_map: &std::collections::HashMap<crate::mir::BlockId, std::collections::HashSet<crate::mir::VReg>>,
    functions: &mut [MirFunction],
) -> MirFunction {
    let original_param_count = func.params.len();
    let mut outlined = func.clone();
    outlined.name = name.to_string();
    outlined.visibility = Visibility::Private;
    outlined.entry_block = body_block;
    outlined.return_type = match kind {
        BodyKind::Generator | BodyKind::Future | BodyKind::Lambda => crate::hir::TypeId::I64,
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
            is_ghost: false,
        });
    } else if kind == BodyKind::Lambda {
        outlined.params.clear();
        outlined.params.push(MirLocal {
            name: "ctx".to_string(),
            ty: crate::hir::TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
        for param in lambda_params {
            outlined.params.push(MirLocal {
                name: param.name.clone(),
                ty: param.ty,
                kind: LocalKind::Parameter,
                is_ghost: false,
            });
        }
        let lambda_capture_local_indices = rewrite_lambda_local_indices(
            &mut outlined,
            original_param_count,
            lambda_params,
            capture_local_indices,
        );
        set_lambda_capture_metadata(
            &mut outlined,
            body_block,
            &name,
            kind,
            &live_ins_map,
            &lambda_capture_local_indices,
            functions,
            &func.name,
        );
    } else {
        outlined.params.push(MirLocal {
            name: "ctx".to_string(),
            ty: crate::hir::TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: false,
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

    if kind != BodyKind::Lambda {
        // Update original function's metadata
        if let Some(orig) = functions.iter_mut().find(|f| f.name == func.name) {
            orig.outlined_bodies.insert(
                body_block,
                crate::mir::OutlinedBody {
                    name: name.to_string(),
                    live_ins: live_ins.clone(),
                    frame_slots: None,
                    is_lambda: false,
                    lambda_capture_local_indices: Vec::new(),
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
                is_lambda: false,
                lambda_capture_local_indices: Vec::new(),
            },
        );
    }

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

fn rewrite_lambda_local_indices(
    outlined: &mut MirFunction,
    original_param_count: usize,
    lambda_params: &[LambdaParamBinding],
    capture_local_indices: &[usize],
) -> Vec<usize> {
    let lambda_param_map: HashMap<usize, usize> = lambda_params
        .iter()
        .enumerate()
        .map(|(i, param)| (param.local_index, i + 1))
        .collect();
    let new_param_count = lambda_params.len() + 1;
    let original_local_count = outlined.locals.len();
    let capture_map: HashMap<usize, usize> = capture_local_indices
        .iter()
        .enumerate()
        .map(|(i, local_index)| (*local_index, new_param_count + original_local_count + i))
        .collect();

    for (i, _local_index) in capture_local_indices.iter().enumerate() {
        outlined.locals.push(MirLocal {
            name: format!("$lambda_capture_{i}"),
            ty: crate::hir::TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: false,
        });
    }

    for block in &mut outlined.blocks {
        for inst in &mut block.instructions {
            if let MirInst::LocalAddr { local_index, .. } = inst {
                if let Some(mapped) = lambda_param_map.get(local_index) {
                    *local_index = *mapped;
                } else if let Some(mapped) = capture_map.get(local_index) {
                    *local_index = *mapped;
                } else if *local_index >= original_param_count {
                    *local_index = new_param_count + (*local_index - original_param_count);
                }
            }
        }
    }
    capture_local_indices
        .iter()
        .filter_map(|local_index| capture_map.get(local_index).copied())
        .collect()
}

fn lambda_capture_local_indices(
    block: &crate::mir::MirBlock,
    closure_inst_index: usize,
    capture_regs: &[crate::mir::VReg],
) -> Vec<usize> {
    let mut addr_to_local = HashMap::new();
    let mut load_to_local = HashMap::new();
    for inst in block.instructions.iter().take(closure_inst_index) {
        match inst {
            MirInst::LocalAddr { dest, local_index } => {
                addr_to_local.insert(*dest, *local_index);
            }
            MirInst::Load { dest, addr, .. } => {
                if let Some(local_index) = addr_to_local.get(addr) {
                    load_to_local.insert(*dest, *local_index);
                }
            }
            _ => {}
        }
    }
    capture_regs
        .iter()
        .filter_map(|reg| load_to_local.get(reg).copied())
        .collect()
}

fn set_lambda_capture_metadata(
    outlined: &mut MirFunction,
    body_block: crate::mir::BlockId,
    name: &str,
    kind: BodyKind,
    live_ins_map: &std::collections::HashMap<crate::mir::BlockId, std::collections::HashSet<crate::mir::VReg>>,
    lambda_capture_local_indices: &[usize],
    functions: &mut [MirFunction],
    original_func_name: &str,
) {
    let mut live_ins: Vec<_> = live_ins_map
        .get(&body_block)
        .cloned()
        .unwrap_or_default()
        .into_iter()
        .collect();
    live_ins.sort_by_key(|v| v.0);

    let meta = crate::mir::OutlinedBody {
        name: name.to_string(),
        live_ins,
        frame_slots: None,
        is_lambda: kind == BodyKind::Lambda,
        lambda_capture_local_indices: lambda_capture_local_indices.to_vec(),
    };
    if let Some(orig) = functions.iter_mut().find(|f| f.name == original_func_name) {
        orig.outlined_bodies.insert(body_block, meta.clone());
    }
    outlined.outlined_bodies.insert(body_block, meta);
}
