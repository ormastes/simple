//! Unified Compilation Context trait (Rust side).
//!
//! Mirrors the Simple-side `CompilationContext` trait for bootstrapping
//! and the Rust JIT instantiator. All three compilation paths (compiler,
//! JIT, linker) use this trait to ensure AOP/DI/contracts are applied.

use std::collections::HashMap;

/// When instantiation occurs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstantiationMode {
    /// During normal compilation
    CompileTime,
    /// During linking
    LinkTime,
    /// During load-time JIT
    JitTime,
}

/// How much contract checking to apply.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractMode {
    /// No contracts
    Off,
    /// Only at module boundaries
    Boundary,
    /// All contracts
    All,
}

/// A generic template loaded from AST cache or SMF.
#[derive(Debug, Clone)]
pub struct GenericTemplate {
    /// Template name
    pub name: String,
    /// Type parameter names
    pub type_params: Vec<String>,
    // TODO: AST data (serialized or in-memory)
}

/// A concrete type used for instantiation.
#[derive(Debug, Clone)]
pub struct ConcreteType {
    /// Type name
    pub name: String,
}

/// Result of compilation.
#[derive(Debug, Clone)]
pub struct CompiledUnit {
    /// Mangled name
    pub name: String,
    /// Generated code bytes
    pub code: Vec<u8>,
    /// Symbol table
    pub symbols: HashMap<String, CompiledSymbol>,
    /// Entry point symbol name
    pub entry_point: Option<String>,
}

/// Symbol in compiled unit.
#[derive(Debug, Clone)]
pub struct CompiledSymbol {
    /// Symbol name
    pub name: String,
    /// Address offset
    pub address: usize,
    /// Size in bytes
    pub size: usize,
}

/// Record of an instantiation.
#[derive(Debug, Clone)]
pub struct InstantiationEntry {
    /// Template base name
    pub template_name: String,
    /// Concrete type arguments (comma-separated)
    pub type_args: String,
    /// Mangled symbol name
    pub mangled_name: String,
    /// Source file
    pub from_file: String,
    /// Source location
    pub from_loc: String,
    /// Output object
    pub to_obj: String,
    /// Status
    pub status: String,
}

/// Unified compilation interface for compiler, JIT, and linker.
///
/// All three paths use this to ensure AOP/DI/contracts are applied.
pub trait CompilationContext {
    /// Load a template by name.
    fn load_template(&self, name: &str) -> Result<GenericTemplate, String>;

    /// Check if a template exists.
    fn has_template(&self, name: &str) -> bool;

    /// Get the contract mode.
    fn contract_mode(&self) -> ContractMode;

    /// Check if coverage is enabled.
    fn coverage_enabled(&self) -> bool;

    /// Compile a template with concrete type arguments.
    fn compile_template(
        &self,
        template: &GenericTemplate,
        type_args: &[ConcreteType],
    ) -> Result<CompiledUnit, String>;

    /// Get the instantiation mode.
    fn instantiation_mode(&self) -> InstantiationMode;

    /// Record an instantiation.
    fn record_instantiation(&mut self, entry: InstantiationEntry);
}

/// Mangle a template name with concrete type arguments.
pub fn mangle(template_name: &str, type_args: &[ConcreteType]) -> String {
    if type_args.is_empty() {
        return template_name.to_string();
    }
    let args: Vec<&str> = type_args.iter().map(|t| t.name.as_str()).collect();
    format!("{}${}", template_name, args.join(","))
}

/// Shared template instantiator with caching and cycle detection.
pub struct TemplateInstantiator<C: CompilationContext> {
    context: C,
    in_progress: std::collections::HashSet<String>,
    cache: HashMap<String, CompiledUnit>,
}

impl<C: CompilationContext> TemplateInstantiator<C> {
    /// Create a new instantiator.
    pub fn new(context: C) -> Self {
        Self {
            context,
            in_progress: std::collections::HashSet::new(),
            cache: HashMap::new(),
        }
    }

    /// Instantiate a template with concrete type arguments.
    pub fn instantiate(
        &mut self,
        template_name: &str,
        type_args: &[ConcreteType],
    ) -> Result<CompiledUnit, String> {
        let key = mangle(template_name, type_args);

        // Cache check
        if let Some(unit) = self.cache.get(&key) {
            return Ok(unit.clone());
        }

        // Cycle detection
        if self.in_progress.contains(&key) {
            return Err(format!("Circular dependency: {}", key));
        }

        self.in_progress.insert(key.clone());

        // Load and compile
        let template = self.context.load_template(template_name)?;
        let unit = self.context.compile_template(&template, type_args)?;

        // Record
        self.context.record_instantiation(InstantiationEntry {
            template_name: template_name.to_string(),
            type_args: type_args.iter().map(|t| t.name.clone()).collect::<Vec<_>>().join(","),
            mangled_name: key.clone(),
            from_file: "instantiator".to_string(),
            from_loc: "instantiator:0:0".to_string(),
            to_obj: "output".to_string(),
            status: "compiled".to_string(),
        });

        // Cache
        self.cache.insert(key.clone(), unit.clone());
        self.in_progress.remove(&key);
        Ok(unit)
    }

    /// Get the underlying context.
    pub fn context(&self) -> &C {
        &self.context
    }

    /// Get mutable context.
    pub fn context_mut(&mut self) -> &mut C {
        &mut self.context
    }

    /// Cache size.
    pub fn cache_size(&self) -> usize {
        self.cache.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Test helper: Mock CompilationContext
    // ========================================================================

    struct MockContext {
        templates: HashMap<String, GenericTemplate>,
        recorded: Vec<InstantiationEntry>,
        mode: InstantiationMode,
        contracts: ContractMode,
    }

    impl MockContext {
        fn new() -> Self {
            Self {
                templates: HashMap::new(),
                recorded: Vec::new(),
                mode: InstantiationMode::CompileTime,
                contracts: ContractMode::All,
            }
        }

        fn with_template(mut self, name: &str, params: Vec<&str>) -> Self {
            self.templates.insert(
                name.to_string(),
                GenericTemplate {
                    name: name.to_string(),
                    type_params: params.into_iter().map(String::from).collect(),
                },
            );
            self
        }

        fn with_mode(mut self, mode: InstantiationMode) -> Self {
            self.mode = mode;
            self
        }

        fn with_contracts(mut self, contracts: ContractMode) -> Self {
            self.contracts = contracts;
            self
        }
    }

    impl CompilationContext for MockContext {
        fn load_template(&self, name: &str) -> Result<GenericTemplate, String> {
            self.templates
                .get(name)
                .cloned()
                .ok_or_else(|| format!("Template not found: {}", name))
        }

        fn has_template(&self, name: &str) -> bool {
            self.templates.contains_key(name)
        }

        fn contract_mode(&self) -> ContractMode {
            self.contracts
        }

        fn coverage_enabled(&self) -> bool {
            false
        }

        fn compile_template(
            &self,
            template: &GenericTemplate,
            type_args: &[ConcreteType],
        ) -> Result<CompiledUnit, String> {
            let mangled = mangle(&template.name, type_args);
            Ok(CompiledUnit {
                name: mangled,
                code: vec![0x90], // NOP as marker
                symbols: HashMap::new(),
                entry_point: None,
            })
        }

        fn instantiation_mode(&self) -> InstantiationMode {
            self.mode
        }

        fn record_instantiation(&mut self, entry: InstantiationEntry) {
            self.recorded.push(entry);
        }
    }

    // ========================================================================
    // Mangle tests
    // ========================================================================

    #[test]
    fn test_mangle_no_args() {
        assert_eq!(mangle("List", &[]), "List");
    }

    #[test]
    fn test_mangle_with_args() {
        let args = vec![ConcreteType { name: "Int".to_string() }];
        assert_eq!(mangle("List", &args), "List$Int");
    }

    #[test]
    fn test_mangle_multiple_args() {
        let args = vec![
            ConcreteType { name: "String".to_string() },
            ConcreteType { name: "Int".to_string() },
        ];
        assert_eq!(mangle("Map", &args), "Map$String,Int");
    }

    #[test]
    fn test_mangle_unique_for_different_args() {
        let args1 = vec![ConcreteType { name: "Int".to_string() }];
        let args2 = vec![ConcreteType { name: "String".to_string() }];
        assert_ne!(mangle("List", &args1), mangle("List", &args2));
    }

    // ========================================================================
    // MockContext trait implementation tests
    // ========================================================================

    #[test]
    fn test_context_has_template() {
        let ctx = MockContext::new().with_template("Vec", vec!["T"]);
        assert!(ctx.has_template("Vec"));
        assert!(!ctx.has_template("Map"));
    }

    #[test]
    fn test_context_load_template_success() {
        let ctx = MockContext::new().with_template("Option", vec!["T"]);
        let result = ctx.load_template("Option");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().name, "Option");
    }

    #[test]
    fn test_context_load_template_not_found() {
        let ctx = MockContext::new();
        let result = ctx.load_template("Missing");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("not found"));
    }

    #[test]
    fn test_context_contract_modes() {
        let ctx_all = MockContext::new().with_contracts(ContractMode::All);
        assert_eq!(ctx_all.contract_mode(), ContractMode::All);

        let ctx_boundary = MockContext::new().with_contracts(ContractMode::Boundary);
        assert_eq!(ctx_boundary.contract_mode(), ContractMode::Boundary);

        let ctx_none = MockContext::new().with_contracts(ContractMode::Off);
        assert_eq!(ctx_none.contract_mode(), ContractMode::Off);
    }

    #[test]
    fn test_context_instantiation_modes() {
        let ctx_compile = MockContext::new().with_mode(InstantiationMode::CompileTime);
        assert_eq!(ctx_compile.instantiation_mode(), InstantiationMode::CompileTime);

        let ctx_jit = MockContext::new().with_mode(InstantiationMode::JitTime);
        assert_eq!(ctx_jit.instantiation_mode(), InstantiationMode::JitTime);

        let ctx_link = MockContext::new().with_mode(InstantiationMode::LinkTime);
        assert_eq!(ctx_link.instantiation_mode(), InstantiationMode::LinkTime);
    }

    #[test]
    fn test_context_compile_template() {
        let ctx = MockContext::new().with_template("List", vec!["T"]);
        let tmpl = ctx.load_template("List").unwrap();
        let args = vec![ConcreteType { name: "Int".to_string() }];
        let result = ctx.compile_template(&tmpl, &args);
        assert!(result.is_ok());
        let unit = result.unwrap();
        assert_eq!(unit.name, "List$Int");
        assert_eq!(unit.code, vec![0x90]); // NOP marker
    }

    #[test]
    fn test_context_record_instantiation() {
        let mut ctx = MockContext::new();
        assert!(ctx.recorded.is_empty());

        ctx.record_instantiation(InstantiationEntry {
            template_name: "List".to_string(),
            type_args: "Int".to_string(),
            mangled_name: "List$Int".to_string(),
            from_file: "test.spl".to_string(),
            from_loc: "test.spl:1:0".to_string(),
            to_obj: "test.o".to_string(),
            status: "compiled".to_string(),
        });

        assert_eq!(ctx.recorded.len(), 1);
        assert_eq!(ctx.recorded[0].template_name, "List");
        assert_eq!(ctx.recorded[0].mangled_name, "List$Int");
    }

    // ========================================================================
    // TemplateInstantiator tests
    // ========================================================================

    #[test]
    fn test_instantiator_empty_cache() {
        let ctx = MockContext::new();
        let inst = TemplateInstantiator::new(ctx);
        assert_eq!(inst.cache_size(), 0);
    }

    #[test]
    fn test_instantiator_successful_instantiation() {
        let ctx = MockContext::new().with_template("List", vec!["T"]);
        let mut inst = TemplateInstantiator::new(ctx);

        let args = vec![ConcreteType { name: "Int".to_string() }];
        let result = inst.instantiate("List", &args);
        assert!(result.is_ok());

        let unit = result.unwrap();
        assert_eq!(unit.name, "List$Int");
        assert_eq!(inst.cache_size(), 1);
    }

    #[test]
    fn test_instantiator_caches_result() {
        let ctx = MockContext::new().with_template("Box", vec!["T"]);
        let mut inst = TemplateInstantiator::new(ctx);

        let args = vec![ConcreteType { name: "Int".to_string() }];
        let r1 = inst.instantiate("Box", &args);
        let r2 = inst.instantiate("Box", &args);
        assert!(r1.is_ok());
        assert!(r2.is_ok());
        // Same cached result
        assert_eq!(r1.unwrap().name, r2.unwrap().name);
        assert_eq!(inst.cache_size(), 1);
    }

    #[test]
    fn test_instantiator_different_args_separate_cache() {
        let ctx = MockContext::new().with_template("Wrapper", vec!["T"]);
        let mut inst = TemplateInstantiator::new(ctx);

        let r1 = inst.instantiate("Wrapper", &[ConcreteType { name: "Int".to_string() }]);
        let r2 = inst.instantiate("Wrapper", &[ConcreteType { name: "String".to_string() }]);
        let r3 = inst.instantiate("Wrapper", &[ConcreteType { name: "Bool".to_string() }]);

        assert!(r1.is_ok());
        assert!(r2.is_ok());
        assert!(r3.is_ok());
        assert_eq!(inst.cache_size(), 3);
        assert_eq!(r1.unwrap().name, "Wrapper$Int");
        assert_eq!(r2.unwrap().name, "Wrapper$String");
        assert_eq!(r3.unwrap().name, "Wrapper$Bool");
    }

    #[test]
    fn test_instantiator_missing_template_error() {
        let ctx = MockContext::new();
        let mut inst = TemplateInstantiator::new(ctx);

        let result = inst.instantiate("NonExistent", &[]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("not found"));
    }

    #[test]
    fn test_instantiator_cycle_detection() {
        let ctx = MockContext::new().with_template("Recursive", vec!["T"]);
        let mut inst = TemplateInstantiator::new(ctx);

        // Manually inject in_progress to simulate cycle
        inst.in_progress.insert("Recursive".to_string());

        let result = inst.instantiate("Recursive", &[]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Circular dependency"));
    }

    #[test]
    fn test_instantiator_records_metadata() {
        let ctx = MockContext::new().with_template("Pair", vec!["A", "B"]);
        let mut inst = TemplateInstantiator::new(ctx);

        let args = vec![
            ConcreteType { name: "Int".to_string() },
            ConcreteType { name: "String".to_string() },
        ];
        let _ = inst.instantiate("Pair", &args);

        let recorded = &inst.context().recorded;
        assert_eq!(recorded.len(), 1);
        assert_eq!(recorded[0].template_name, "Pair");
        assert_eq!(recorded[0].type_args, "Int,String");
        assert_eq!(recorded[0].mangled_name, "Pair$Int,String");
        assert_eq!(recorded[0].status, "compiled");
    }

    #[test]
    fn test_instantiator_no_args() {
        let ctx = MockContext::new().with_template("Unit", vec![]);
        let mut inst = TemplateInstantiator::new(ctx);

        let result = inst.instantiate("Unit", &[]);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().name, "Unit");
        assert_eq!(inst.cache_size(), 1);
    }

    #[test]
    fn test_instantiator_multiple_templates() {
        let ctx = MockContext::new()
            .with_template("List", vec!["T"])
            .with_template("Map", vec!["K", "V"])
            .with_template("Set", vec!["T"]);
        let mut inst = TemplateInstantiator::new(ctx);

        let r1 = inst.instantiate("List", &[ConcreteType { name: "Int".to_string() }]);
        let r2 = inst.instantiate("Map", &[
            ConcreteType { name: "String".to_string() },
            ConcreteType { name: "Int".to_string() },
        ]);
        let r3 = inst.instantiate("Set", &[ConcreteType { name: "Bool".to_string() }]);

        assert!(r1.is_ok());
        assert!(r2.is_ok());
        assert!(r3.is_ok());
        assert_eq!(inst.cache_size(), 3);

        // Verify recorded
        assert_eq!(inst.context().recorded.len(), 3);
    }

    #[test]
    fn test_instantiator_clears_in_progress_after_success() {
        let ctx = MockContext::new().with_template("Clean", vec!["T"]);
        let mut inst = TemplateInstantiator::new(ctx);

        let _ = inst.instantiate("Clean", &[ConcreteType { name: "Int".to_string() }]);

        // in_progress should be empty after successful instantiation
        assert!(inst.in_progress.is_empty());
    }
}
