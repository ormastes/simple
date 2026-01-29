//! Dependency injection resolution for MIR lowering
//!
//! This module contains methods for resolving dependencies through DI,
//! managing singleton instances, and detecting circular dependencies.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::di::create_di_match_context;
use crate::hir::TypeId;
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn resolve_di_arg(
        &mut self,
        param_ty: TypeId,
        function_name: &str,
        param_index: usize,
    ) -> MirLowerResult<VReg> {
        // Feature #1018: Parameter-level diagnostic for unresolvable dependencies
        let type_name = self
            .type_registry
            .and_then(|registry| registry.get_type_name(param_ty))
            .map(|name| name.to_string())
            .or_else(|| builtin_type_name(param_ty).map(|name| name.to_string()))
            .ok_or_else(|| {
                MirLowerError::Unsupported(format!(
                    "DI resolution failed for parameter #{} in function '{}': \
                     Cannot resolve unnamed type. DI requires parameters to have named types.",
                    param_index, function_name
                ))
            })?;

        let di_config = self.di_config.as_ref().ok_or_else(|| {
            MirLowerError::Unsupported(format!(
                "DI resolution failed for parameter #{} (type '{}') in function '{}': \
                 No DI configuration available. Ensure a DI config is loaded.",
                param_index, type_name, function_name
            ))
        })?;

        let ctx = create_di_match_context(&type_name, "", &[]);
        let binding = di_config
            .select_binding("default", &ctx)
            .map_err(|_| {
                // Get available bindings for diagnostic (#1018)
                let available_bindings = di_config
                    .profiles
                    .get("default")
                    .map(|profile| {
                        profile
                            .bindings
                            .iter()
                            .map(|b| format!("  - {} (scope: {:?}, priority: {})", b.impl_type, b.scope, b.priority))
                            .collect::<Vec<_>>()
                            .join("\n")
                    })
                    .unwrap_or_else(|| "  (no bindings available)".to_string());

                MirLowerError::Unsupported(format!(
                    "DI resolution failed for parameter #{} (type '{}') in function '{}': \
                     Ambiguous binding - multiple bindings match this type.\n\
                     Available bindings:\n{}",
                    param_index, type_name, function_name, available_bindings
                ))
            })?
            .ok_or_else(|| {
                // Get available bindings for diagnostic (#1018)
                let available_bindings = di_config
                    .profiles
                    .get("default")
                    .map(|profile| {
                        if profile.bindings.is_empty() {
                            "  (no bindings configured)".to_string()
                        } else {
                            profile
                                .bindings
                                .iter()
                                .map(|b| {
                                    format!("  - {} (scope: {:?}, priority: {})", b.impl_type, b.scope, b.priority)
                                })
                                .collect::<Vec<_>>()
                                .join("\n")
                        }
                    })
                    .unwrap_or_else(|| "  (no profile 'default' found)".to_string());

                MirLowerError::Unsupported(format!(
                    "DI resolution failed for parameter #{} (type '{}') in function '{}': \
                     No binding found for this type.\n\
                     Available bindings:\n{}",
                    param_index, type_name, function_name, available_bindings
                ))
            })?;

        let impl_name = binding.impl_type.clone();
        let scope = binding.scope;

        // Check singleton cache first
        if scope == crate::di::DiScope::Singleton {
            if let Some(&cached_reg) = self.singleton_cache.get(&impl_name) {
                tracing::debug!("DI: Reusing cached singleton instance for '{}'", impl_name);
                return Ok(cached_reg);
            }
        }

        // Circular dependency detection (#1009)
        if self.di_resolution_stack.contains(&impl_name) {
            // Build the dependency chain for error message
            let mut chain = self.di_resolution_stack.clone();
            chain.push(impl_name.clone());
            let chain_str = chain.join(" -> ");
            tracing::error!("DI: Circular dependency detected: {}", chain_str);
            return Err(MirLowerError::CircularDependency(chain_str));
        }

        // Add to dependency graph for validation
        if let Some(current_type) = self.di_resolution_stack.last() {
            tracing::debug!("DI: Adding dependency edge: {} -> {}", current_type, impl_name);
            self.dependency_graph
                .add_dependency(current_type.clone(), impl_name.clone());
        }

        // Push current type onto resolution stack
        self.di_resolution_stack.push(impl_name.clone());
        tracing::debug!("DI: Resolution stack depth: {}", self.di_resolution_stack.len());

        // Check if the constructor has injectable parameters that need to be resolved
        let constructor_args = if let Some(param_info) = self.inject_functions.get(&impl_name).cloned() {
            let mut args = Vec::new();
            for (param_idx, (param_ty, is_injectable)) in param_info.iter().enumerate() {
                if *is_injectable {
                    // Recursively resolve this parameter's dependency
                    let injected = self.resolve_di_arg(*param_ty, &impl_name, param_idx)?;
                    args.push(injected);
                } else {
                    // Non-injectable parameters in a DI constructor is an error (#1018)
                    return Err(MirLowerError::Unsupported(format!(
                        "DI constructor '{}' has non-injectable parameter #{}: \
                         All parameters in an @inject constructor must be marked as injectable.",
                        impl_name, param_idx
                    )));
                }
            }
            args
        } else {
            Vec::new()
        };

        // Create new instance with resolved dependencies
        let instance_reg = self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::Call {
                dest: Some(dest),
                target: CallTarget::from_name(&impl_name),
                args: constructor_args,
            });
            dest
        })?;

        // Cache singleton instances
        if scope == crate::di::DiScope::Singleton {
            tracing::debug!("DI: Caching singleton instance for '{}'", impl_name);
            self.singleton_cache.insert(impl_name.clone(), instance_reg);
        }

        // Pop from resolution stack after successful creation (#1009)
        self.di_resolution_stack.pop();
        tracing::debug!(
            "DI: Resolution stack depth after pop: {}",
            self.di_resolution_stack.len()
        );

        Ok(instance_reg)
    }
}

/// Map built-in type IDs to their names for DI resolution
pub(super) fn builtin_type_name(type_id: TypeId) -> Option<&'static str> {
    match type_id {
        TypeId::VOID => Some("void"),
        TypeId::BOOL => Some("bool"),
        TypeId::I8 => Some("i8"),
        TypeId::I16 => Some("i16"),
        TypeId::I32 => Some("i32"),
        TypeId::I64 => Some("i64"),
        TypeId::U8 => Some("u8"),
        TypeId::U16 => Some("u16"),
        TypeId::U32 => Some("u32"),
        TypeId::U64 => Some("u64"),
        TypeId::F32 => Some("f32"),
        TypeId::F64 => Some("f64"),
        TypeId::STRING => Some("str"),
        TypeId::NIL => Some("nil"),
        _ => None,
    }
}
