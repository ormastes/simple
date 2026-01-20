use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use simple_parser::Pattern;

use super::super::lifetime::LifetimeContext;
use super::super::types::{HirModule, TypeId};
use super::memory_warning::MemoryWarningCollector;
use crate::module_resolver::ModuleResolver;

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
}

impl Lowerer {
    pub fn new() -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
            module_resolver: None,
            current_file: None,
            loaded_modules: HashSet::new(),
            memory_warnings: MemoryWarningCollector::new(),
            lifetime_context: LifetimeContext::new(),
        }
    }

    /// Create a new lowerer with module resolution support for loading imported types
    pub fn with_module_resolver(module_resolver: ModuleResolver, current_file: PathBuf) -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
            module_resolver: Some(module_resolver),
            current_file: Some(current_file),
            loaded_modules: HashSet::new(),
            memory_warnings: MemoryWarningCollector::new(),
            lifetime_context: LifetimeContext::new(),
        }
    }

    /// Create a new lowerer with strict memory mode (warnings become errors)
    pub fn with_strict_memory_mode() -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
            module_resolver: None,
            current_file: None,
            loaded_modules: HashSet::new(),
            memory_warnings: MemoryWarningCollector::strict(),
            lifetime_context: LifetimeContext::new(),
        }
    }

    /// Get the collected memory warnings
    pub fn memory_warnings(&self) -> &MemoryWarningCollector {
        &self.memory_warnings
    }

    /// Take ownership of the memory warnings
    pub fn take_memory_warnings(&mut self) -> MemoryWarningCollector {
        std::mem::take(&mut self.memory_warnings)
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
}

impl Default for Lowerer {
    fn default() -> Self {
        Self::new()
    }
}
