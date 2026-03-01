use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use simple_parser::Pattern;

use super::super::capability::CapabilityEnv;
use super::super::lifetime::LifetimeContext;
use super::super::types::{HirModule, TypeId};
use super::deprecation_warning::DeprecationWarningCollector;
use super::memory_warning::MemoryWarningCollector;
use crate::module_resolver::ModuleResolver;
use crate::type_inference_config::TypeInferenceConfig;

pub struct Lowerer {
    pub(super) module: HirModule,
    pub(super) globals: HashMap<String, TypeId>,
    /// Set of function names that are marked with #[pure] (CTR-031)
    /// These functions can be called from contract expressions
    pub(super) pure_functions: HashSet<String>,
    /// Current class/struct type being lowered (for Self resolution)
    pub(super) current_class_type: Option<TypeId>,
    /// Module resolver for loading types from imports (optional for backward compatibility)
    pub(super) module_resolver: Option<ModuleResolver>,
    /// Current file being compiled (for resolving relative imports)
    pub(super) current_file: Option<PathBuf>,
    /// Track loaded modules to prevent circular dependencies
    pub(super) loaded_modules: HashSet<PathBuf>,
    /// Memory safety warning collector
    pub(super) memory_warnings: MemoryWarningCollector,
    /// Lifetime inference context for tracking reference lifetimes
    pub(super) lifetime_context: LifetimeContext,
    /// Capability environment for tracking active reference capabilities
    pub(super) capability_env: CapabilityEnv,
    /// Type aliases: alias_name -> original_name
    pub(super) type_aliases: HashMap<String, String>,
    /// Function aliases: alias_name -> original_name
    pub(super) function_aliases: HashMap<String, String>,
    /// Reverse lookup for suggestions: original -> Vec<aliases>
    pub(super) type_aliases_reverse: HashMap<String, Vec<String>>,
    /// Reverse lookup for function suggestions: original -> Vec<aliases>
    pub(super) function_aliases_reverse: HashMap<String, Vec<String>>,
    /// Deprecated items: name -> deprecation_message (None if no message)
    pub(super) deprecated_items: HashMap<String, Option<String>>,
    /// Deprecation warning collector
    pub(super) deprecation_warnings: DeprecationWarningCollector,
    /// Type inference configuration for empty collections
    pub(super) type_inference_config: TypeInferenceConfig,
    /// Pre-registered method return types: "ClassName.method" -> return TypeId
    pub(super) method_return_types: HashMap<String, TypeId>,
    /// When true, unknown types resolve to ANY instead of erroring.
    /// This allows compilation to proceed even when imports can't be fully resolved.
    pub(super) lenient_types: bool,
    /// Names of extern function declarations for codegen
    pub(super) extern_fn_names: HashSet<String>,
}

impl Lowerer {
    /// Create a new lowerer with STRICT memory mode (Rust-level safety)
    /// Memory safety violations are compile-time ERRORS by default.
    /// Use `with_lenient_mode()` for backwards compatibility during migration.
    pub fn new() -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
            module_resolver: None,
            current_file: None,
            loaded_modules: HashSet::new(),
            memory_warnings: MemoryWarningCollector::strict(), // STRICT mode for Rust-level safety
            lifetime_context: LifetimeContext::new(),
            capability_env: CapabilityEnv::new(),
            type_aliases: HashMap::new(),
            function_aliases: HashMap::new(),
            type_aliases_reverse: HashMap::new(),
            function_aliases_reverse: HashMap::new(),
            deprecated_items: HashMap::new(),
            deprecation_warnings: DeprecationWarningCollector::new(),
            type_inference_config: TypeInferenceConfig::default(),
            method_return_types: HashMap::new(),
            lenient_types: false,
            extern_fn_names: HashSet::new(),
        }
    }

    /// Create a new lowerer with module resolution support for loading imported types
    /// Uses strict memory mode by default.
    pub fn with_module_resolver(module_resolver: ModuleResolver, current_file: PathBuf) -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
            module_resolver: Some(module_resolver),
            current_file: Some(current_file),
            loaded_modules: HashSet::new(),
            memory_warnings: MemoryWarningCollector::strict(), // STRICT by default
            lifetime_context: LifetimeContext::new(),
            capability_env: CapabilityEnv::new(),
            type_aliases: HashMap::new(),
            function_aliases: HashMap::new(),
            type_aliases_reverse: HashMap::new(),
            function_aliases_reverse: HashMap::new(),
            deprecated_items: HashMap::new(),
            deprecation_warnings: DeprecationWarningCollector::new(),
            type_inference_config: TypeInferenceConfig::default(),
            method_return_types: HashMap::new(),
            lenient_types: false,
            extern_fn_names: HashSet::new(),
        }
    }

    /// Create a lowerer with custom type inference configuration
    pub fn with_type_inference_config(mut self, config: TypeInferenceConfig) -> Self {
        self.type_inference_config = config;
        self
    }

    /// Set type inference configuration
    pub fn set_type_inference_config(&mut self, config: TypeInferenceConfig) {
        self.type_inference_config = config;
    }

    /// Get the current type inference configuration
    pub fn type_inference_config(&self) -> &TypeInferenceConfig {
        &self.type_inference_config
    }

    /// Alias for `new()` - strict mode is now the default
    #[deprecated(since = "1.0.0", note = "strict mode is now the default; use `new()` instead")]
    pub fn with_strict_memory_mode() -> Self {
        Self::new()
    }

    /// Create a new lowerer with LENIENT memory mode (for backwards compatibility)
    /// In lenient mode, capability violations produce WARNINGS instead of errors.
    /// Use this during migration to strict mode.
    pub fn with_lenient_mode() -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
            module_resolver: None,
            current_file: None,
            loaded_modules: HashSet::new(),
            memory_warnings: MemoryWarningCollector::new(), // Lenient mode (warnings only)
            lifetime_context: LifetimeContext::new(),
            capability_env: CapabilityEnv::new(),
            type_aliases: HashMap::new(),
            function_aliases: HashMap::new(),
            type_aliases_reverse: HashMap::new(),
            function_aliases_reverse: HashMap::new(),
            deprecated_items: HashMap::new(),
            deprecation_warnings: DeprecationWarningCollector::new(),
            type_inference_config: TypeInferenceConfig::default(),
            method_return_types: HashMap::new(),
            lenient_types: false,
            extern_fn_names: HashSet::new(),
        }
    }

    /// Get the collected memory warnings
    pub fn memory_warnings(&self) -> &MemoryWarningCollector {
        &self.memory_warnings
    }

    /// Get mutable access to the memory warnings collector
    pub fn memory_warnings_mut(&mut self) -> &mut MemoryWarningCollector {
        &mut self.memory_warnings
    }

    /// Set whether to use strict mode for memory safety checks
    pub fn set_strict_mode(&mut self, strict: bool) {
        self.memory_warnings.set_strict(strict);
    }

    /// Set whether to use lenient type resolution.
    /// When enabled, unknown types resolve to ANY instead of producing errors.
    /// This allows compilation to proceed even when imports can't be fully resolved.
    pub fn set_lenient_types(&mut self, lenient: bool) {
        self.lenient_types = lenient;
    }

    /// Take ownership of the memory warnings
    pub fn take_memory_warnings(&mut self) -> MemoryWarningCollector {
        std::mem::take(&mut self.memory_warnings)
    }

    /// Get the collected deprecation warnings
    pub fn deprecation_warnings(&self) -> &DeprecationWarningCollector {
        &self.deprecation_warnings
    }

    /// Take ownership of the deprecation warnings
    pub fn take_deprecation_warnings(&mut self) -> DeprecationWarningCollector {
        std::mem::take(&mut self.deprecation_warnings)
    }

    /// Check if a function is marked as pure
    pub fn is_pure_function(&self, name: &str) -> bool {
        self.pure_functions.contains(name)
    }

    pub(super) fn extract_pattern_name(pattern: &Pattern) -> Option<String> {
        match pattern {
            Pattern::Identifier(n) => Some(n.clone()),
            Pattern::MutIdentifier(n) => Some(n.clone()),
            Pattern::MoveIdentifier(n) => Some(n.clone()),
            Pattern::Typed { pattern: inner, .. } => Self::extract_pattern_name(inner),
            _ => None,
        }
    }

    /// Extract type annotation from a Pattern::Typed wrapper.
    /// Returns None if the pattern doesn't have a type annotation.
    pub(super) fn extract_pattern_type(pattern: &Pattern) -> Option<&simple_parser::Type> {
        match pattern {
            Pattern::Typed { ty, .. } => Some(ty),
            _ => None,
        }
    }

    /// Get the lifetime context
    pub fn lifetime_context(&self) -> &LifetimeContext {
        &self.lifetime_context
    }

    /// Get mutable access to the lifetime context
    pub fn lifetime_context_mut(&mut self) -> &mut LifetimeContext {
        &mut self.lifetime_context
    }

    /// Check if there are any lifetime violations
    pub fn has_lifetime_violations(&self) -> bool {
        self.lifetime_context.has_violations()
    }

    /// Get all lifetime violations
    pub fn lifetime_violations(&self) -> &[super::super::lifetime::LifetimeViolation] {
        self.lifetime_context.violations()
    }

    /// Generate Lean 4 verification code for lifetime constraints
    pub fn generate_lean4_lifetime_verification(&self) -> String {
        self.lifetime_context.generate_lean4()
    }

    /// Get the capability environment
    pub fn capability_env(&self) -> &CapabilityEnv {
        &self.capability_env
    }

    /// Get mutable access to the capability environment
    pub fn capability_env_mut(&mut self) -> &mut CapabilityEnv {
        &mut self.capability_env
    }

    // === Alias and Deprecation Tracking ===

    /// Register a type alias name mapping: alias NewName = OldName
    pub(super) fn register_type_alias_mapping(&mut self, alias_name: String, target_name: String) {
        // Add forward mapping
        self.type_aliases.insert(alias_name.clone(), target_name.clone());

        // Add reverse mapping for suggestion lookup
        self.type_aliases_reverse
            .entry(target_name)
            .or_default()
            .push(alias_name);
    }

    /// Register a function alias: fn new_name = old_name
    pub(super) fn register_function_alias(&mut self, alias_name: String, target_name: String) {
        // Add forward mapping
        self.function_aliases.insert(alias_name.clone(), target_name.clone());

        // Add reverse mapping for suggestion lookup
        self.function_aliases_reverse
            .entry(target_name)
            .or_default()
            .push(alias_name);
    }

    /// Mark an item as deprecated with an optional message
    pub(super) fn mark_deprecated(&mut self, name: String, message: Option<String>) {
        self.deprecated_items.insert(name, message);
    }

    /// Check if an item is deprecated
    pub fn is_deprecated(&self, name: &str) -> bool {
        self.deprecated_items.contains_key(name)
    }

    /// Get the deprecation message for an item
    pub fn deprecation_message(&self, name: &str) -> Option<&str> {
        self.deprecated_items.get(name).and_then(|opt| opt.as_deref())
    }

    /// Resolve a type alias to its original type name
    pub fn resolve_type_alias(&self, name: &str) -> Option<&str> {
        self.type_aliases.get(name).map(|s| s.as_str())
    }

    /// Resolve a function alias to its original function name
    pub fn resolve_function_alias(&self, name: &str) -> Option<&str> {
        self.function_aliases.get(name).map(|s| s.as_str())
    }

    /// Find non-deprecated alternatives for a deprecated type
    pub fn find_non_deprecated_type_alternative(&self, name: &str) -> Option<String> {
        // Get the original type (if this is an alias)
        let original = self.type_aliases.get(name).map(|s| s.as_str()).unwrap_or(name);

        // Find all aliases of the original
        if let Some(aliases) = self.type_aliases_reverse.get(original) {
            for alias in aliases {
                // Return first non-deprecated alias
                if !self.deprecated_items.contains_key(alias) {
                    return Some(alias.clone());
                }
            }
        }

        // If original itself is not deprecated, suggest it
        if !self.deprecated_items.contains_key(original) {
            return Some(original.to_string());
        }

        None
    }

    /// Find non-deprecated alternatives for a deprecated function
    pub fn find_non_deprecated_function_alternative(&self, name: &str) -> Option<String> {
        // Get the original function (if this is an alias)
        let original = self.function_aliases.get(name).map(|s| s.as_str()).unwrap_or(name);

        // Find all aliases of the original
        if let Some(aliases) = self.function_aliases_reverse.get(original) {
            for alias in aliases {
                // Return first non-deprecated alias
                if !self.deprecated_items.contains_key(alias) {
                    return Some(alias.clone());
                }
            }
        }

        // If original itself is not deprecated, suggest it
        if !self.deprecated_items.contains_key(original) {
            return Some(original.to_string());
        }

        None
    }
}

impl Default for Lowerer {
    fn default() -> Self {
        Self::new()
    }
}
