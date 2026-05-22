//! Dependency injection resolution for MIR lowering
//!
//! This module contains methods for resolving dependencies through DI,
//! managing singleton instances, and detecting circular dependencies.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::di::{create_di_match_context, DiScope};
use crate::hir::TypeId;
use crate::mir::effects::CallTarget;
use crate::mir::instructions::{MirInst, VReg};

#[derive(Debug, Clone)]
struct ResolvedDiBinding {
    impl_name: String,
    scope: DiScope,
}

impl<'a> MirLowerer<'a> {
    pub(super) fn resolve_di_arg(
        &mut self,
        param_ty: TypeId,
        function_name: &str,
        param_index: usize,
    ) -> MirLowerResult<VReg> {
        self.resolve_di_arg_with_hint(param_ty, None, function_name, param_index)
    }

    pub(super) fn resolve_di_arg_with_hint(
        &mut self,
        param_ty: TypeId,
        type_name_hint: Option<&str>,
        function_name: &str,
        param_index: usize,
    ) -> MirLowerResult<VReg> {
        // Feature #1018: Parameter-level diagnostic for unresolvable dependencies
        let type_name = self
            .type_registry
            .and_then(|registry| registry.get_type_name(param_ty))
            .map(|name| name.to_string())
            .or_else(|| type_name_hint.map(|name| name.to_string()))
            .or_else(|| builtin_type_name(param_ty).map(|name| name.to_string()))
            .ok_or_else(|| {
                MirLowerError::Unsupported(format!(
                    "DI resolution failed for parameter #{} in function '{}': \
                     Cannot resolve unnamed type. DI requires parameters to have named types.",
                    param_index, function_name
                ))
            })?;

        let ctx = create_di_match_context(&type_name, "", &[]);
        let profile = self.di_profile.as_str();
        let resolved = if let Some(di_config) = self.di_config.as_ref() {
            match di_config.select_binding(profile, &ctx) {
                Ok(Some(binding)) => ResolvedDiBinding {
                    impl_name: binding.impl_type.clone(),
                    scope: binding.scope,
                },
                Ok(None) => self
                    .resolve_runtime_slot_default(&type_name)
                    .or_else(|| self.resolve_convention_binding(&type_name).ok())
                    .ok_or_else(|| {
                        let convention_message = self
                            .resolve_convention_binding(&type_name)
                            .err()
                            .unwrap_or_else(|| "no runtime slot default".to_string());
                        self.no_di_binding_error(param_index, &type_name, function_name, profile, &convention_message)
                    })?,
                Err(_) => {
                    let available_bindings = self.format_available_bindings(profile);
                    return Err(MirLowerError::Unsupported(format!(
                        "DI resolution failed for parameter #{} (type '{}') in function '{}': \
                         Ambiguous binding - multiple bindings match this type.\n\
                         Active DI profile: '{}'\n\
                         Available bindings:\n{}",
                        param_index, type_name, function_name, profile, available_bindings
                    )));
                }
            }
        } else {
            self.resolve_convention_binding(&type_name).map_err(|message| {
                self.no_di_binding_error(param_index, &type_name, function_name, profile, &message)
            })?
        };

        let impl_name = resolved.impl_name;
        let scope = resolved.scope;

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
            for (param_idx, (param_ty, type_name_hint, is_injectable)) in param_info.iter().enumerate() {
                if *is_injectable {
                    // Recursively resolve this parameter's dependency
                    let injected =
                        self.resolve_di_arg_with_hint(*param_ty, type_name_hint.as_deref(), &impl_name, param_idx)?;
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

    fn resolve_convention_binding(&self, type_name: &str) -> Result<ResolvedDiBinding, String> {
        let conventions = self
            .di_config
            .as_ref()
            .map(|config| config.conventions)
            .unwrap_or_default();

        if conventions.self_binding && self.has_constructor(type_name) {
            return Ok(ResolvedDiBinding {
                impl_name: format!("{}.new", type_name),
                scope: DiScope::Transient,
            });
        }

        if conventions.single_visible_impl {
            match self.dependency_graph.resolve_single_visible_implementation(type_name) {
                Ok(Some(impl_type)) => {
                    if self.has_constructor(&impl_type) {
                        return Ok(ResolvedDiBinding {
                            impl_name: format!("{}.new", impl_type),
                            scope: DiScope::Transient,
                        });
                    }
                }
                Ok(None) => {}
                Err(candidates) => {
                    return Err(format!(
                        "ambiguous convention binding for '{}': {}",
                        type_name,
                        candidates.join(", ")
                    ));
                }
            }
        }

        let mut naming_candidates = Vec::new();
        if conventions.folder_fallback {
            naming_candidates.extend(self.folder_convention_candidates(type_name));
        }
        if conventions.naming_fallback {
            for candidate in self.naming_convention_candidates(type_name) {
                if !naming_candidates.contains(&candidate) {
                    naming_candidates.push(candidate);
                }
            }
        }
        if conventions.std_defaults {
            for candidate in self.std_default_candidates(type_name) {
                if !naming_candidates.contains(&candidate) {
                    naming_candidates.push(candidate);
                }
            }
        }
        match naming_candidates.as_slice() {
            [impl_type] => Ok(ResolvedDiBinding {
                impl_name: format!("{}.new", impl_type),
                scope: DiScope::Transient,
            }),
            [] => Err(format!("no explicit binding or convention binding for '{}'", type_name)),
            candidates => Err(format!(
                "ambiguous convention binding for '{}': {}",
                type_name,
                candidates.join(", ")
            )),
        }
    }

    fn resolve_runtime_slot_default(&self, type_name: &str) -> Option<ResolvedDiBinding> {
        let config = self.di_config.as_ref()?;
        config
            .runtime_slots
            .iter()
            .find(|slot| slot.type_name == type_name)
            .and_then(|slot| slot.default_impl.as_deref())
            .filter(|default_impl| self.has_constructor(default_impl))
            .map(|default_impl| ResolvedDiBinding {
                impl_name: format!("{}.new", default_impl),
                scope: DiScope::Transient,
            })
    }

    fn has_constructor(&self, type_name: &str) -> bool {
        self.available_functions.contains(&format!("{}.new", type_name))
    }

    fn naming_convention_candidates(&self, type_name: &str) -> Vec<String> {
        let mut candidates = Vec::new();
        for prefix in ["Sql", "System", "Console", "Json", "Memory", "Default"] {
            let candidate = format!("{}{}", prefix, type_name);
            if self.has_constructor(&candidate) {
                candidates.push(candidate);
            }
        }
        if type_name.ends_with("Repo") {
            let stem = type_name.trim_end_matches("Repo");
            for prefix in ["Sql", "Postgres", "Sqlite", "Memory"] {
                let candidate = format!("{}{}Repo", prefix, stem);
                if self.has_constructor(&candidate) && !candidates.contains(&candidate) {
                    candidates.push(candidate);
                }
            }
        }
        candidates
    }

    fn folder_convention_candidates(&self, type_name: &str) -> Vec<String> {
        let mut candidates = Vec::new();
        let scans = self
            .di_config
            .as_ref()
            .map(|config| config.scans.as_slice())
            .unwrap_or(&[]);
        let test_profile = self.di_profile == "test" || scans.iter().any(|scan| scan.contains("test"));
        let infra_scan = scans
            .iter()
            .any(|scan| scan.contains("infra") || scan.contains("repo") || scan.contains("db"));

        let mut prefixes = Vec::new();
        if test_profile {
            prefixes.extend(["Fake", "Memory"]);
        }
        if infra_scan {
            prefixes.extend(["Sql", "Postgres", "Sqlite"]);
        }

        for prefix in prefixes {
            let candidate = format!("{}{}", prefix, type_name);
            if self.has_constructor(&candidate) && !candidates.contains(&candidate) {
                candidates.push(candidate);
            }
            if let Some(stem) = type_name.strip_suffix("Repo") {
                let repo_candidate = format!("{}{}Repo", prefix, stem);
                if self.has_constructor(&repo_candidate) && !candidates.contains(&repo_candidate) {
                    candidates.push(repo_candidate);
                }
            }
        }

        let suffix_candidate = format!("{}Fake", type_name);
        if test_profile && self.has_constructor(&suffix_candidate) && !candidates.contains(&suffix_candidate) {
            candidates.push(suffix_candidate);
        }

        candidates
    }

    fn std_default_candidates(&self, type_name: &str) -> Vec<String> {
        let defaults = match type_name {
            "Clock" => &["SystemClock"][..],
            "Logger" => &["ConsoleLogger"][..],
            "CryptoRng" => &["SystemCryptoRng"][..],
            "Random" | "Rng" => &["SystemRandom", "SystemRng"][..],
            _ => &[],
        };
        defaults
            .iter()
            .filter(|candidate| self.has_constructor(candidate))
            .map(|candidate| (*candidate).to_string())
            .collect()
    }

    fn format_available_bindings(&self, profile: &str) -> String {
        self.di_config
            .as_ref()
            .and_then(|di_config| di_config.profiles.get(profile))
            .map(|profile| {
                if profile.bindings.is_empty() {
                    "  (no bindings configured)".to_string()
                } else {
                    profile
                        .bindings
                        .iter()
                        .map(|b| format!("  - {} (scope: {:?}, priority: {})", b.impl_type, b.scope, b.priority))
                        .collect::<Vec<_>>()
                        .join("\n")
                }
            })
            .unwrap_or_else(|| format!("  (no profile '{}' found)", profile))
    }

    fn no_di_binding_error(
        &self,
        param_index: usize,
        type_name: &str,
        function_name: &str,
        profile: &str,
        convention_message: &str,
    ) -> MirLowerError {
        MirLowerError::Unsupported(format!(
            "DI resolution failed for parameter #{} (type '{}') in function '{}': \
             No binding found for this type.\n\
             Active DI profile: '{}'\n\
             Convention result: {}\n\
             Available bindings:\n{}",
            param_index,
            type_name,
            function_name,
            profile,
            convention_message,
            self.format_available_bindings(profile)
        ))
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
