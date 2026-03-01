use simple_parser::{self as ast, Module, Node};

use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{HirAopAdvice, HirArchRule, HirDiBinding, HirLeanBlock, HirMockDecl, HirModule, HirType, TypeId};

impl Lowerer {
    /// Helper: Register type and function declarations from an AST node
    fn register_declarations_from_node(&mut self, item: &Node) -> LowerResult<()> {
        match item {
            Node::Struct(s) => {
                let struct_type_id = self.register_struct(s)?;
                // Register struct constructor in globals so it can be used as a value
                self.globals.insert(s.name.clone(), struct_type_id);
            }
            Node::Function(f) => {
                let ret_ty = self.resolve_type_opt(&f.return_type)?;
                self.globals.insert(f.name.clone(), ret_ty);
                // Track pure functions for CTR-030-032
                if f.is_pure() {
                    self.pure_functions.insert(f.name.clone());
                }
            }
            Node::Class(c) => {
                let class_type_id = self.register_class(c)?;
                // Register class constructor in globals so it can be used as a value
                self.globals.insert(c.name.clone(), class_type_id);
            }
            Node::Enum(e) => {
                let variants: Vec<_> = e
                    .variants
                    .iter()
                    .map(|v| {
                        let fields = v.fields.as_ref().map(|enum_fields| {
                            enum_fields
                                .iter()
                                .map(|f| self.resolve_type(&f.ty).unwrap_or(TypeId::VOID))
                                .collect()
                        });
                        (v.name.clone(), fields)
                    })
                    .collect();

                // Get the enum type ID
                let enum_type_id = self.module.types.lookup(&e.name).unwrap_or_else(|| {
                    eprintln!("[WARNING] Enum type not found during registration: {}", e.name);
                    TypeId::VOID
                });

                // Use update_named to update the placeholder created in Pass 0
                self.module.types.update_named(
                    e.name.clone(),
                    HirType::Enum {
                        name: e.name.clone(),
                        variants,
                        generic_params: e.generic_params.clone(),
                        is_generic_template: e.is_generic_template,
                        type_bindings: std::collections::HashMap::new(), // Will be filled during specialization
                    },
                );

                // Register enum name in globals so that Backend.Native can be resolved
                // The enum name acts as a namespace for variant constructors
                self.globals.insert(e.name.clone(), enum_type_id);
            }
            Node::Mixin(m) => {
                self.register_mixin(m)?;
            }
            Node::TypeAlias(ta) => {
                self.register_type_alias(ta)?;
            }
            Node::ClassAlias(ca) => {
                // Register class/struct/enum alias mapping
                self.register_type_alias_mapping(ca.name.clone(), ca.target.clone());

                // Check for @deprecated decorator
                for decorator in &ca.decorators {
                    if let ast::Expr::Identifier(name) = &decorator.name {
                        if name == "deprecated" {
                            // Extract message from decorator args if present
                            let msg = decorator.args.as_ref().and_then(|args| {
                                args.first().and_then(|arg| {
                                    if let ast::Expr::String(s) = &arg.value {
                                        Some(s.clone())
                                    } else {
                                        None
                                    }
                                })
                            });
                            self.mark_deprecated(ca.name.clone(), msg);
                        }
                    }
                }
            }
            Node::FunctionAlias(fa) => {
                // Register function alias mapping
                self.register_function_alias(fa.name.clone(), fa.target.clone());

                // Check for @deprecated decorator
                for decorator in &fa.decorators {
                    if let ast::Expr::Identifier(name) = &decorator.name {
                        if name == "deprecated" {
                            // Extract message from decorator args if present
                            let msg = decorator.args.as_ref().and_then(|args| {
                                args.first().and_then(|arg| {
                                    if let ast::Expr::String(s) = &arg.value {
                                        Some(s.clone())
                                    } else {
                                        None
                                    }
                                })
                            });
                            self.mark_deprecated(fa.name.clone(), msg);
                        }
                    }
                }
            }
            Node::Trait(t) => {
                // Register trait with vtable slot information for static polymorphism
                self.register_trait(t)?;
            }
            Node::Extern(e) => {
                // Register extern function in globals so it can be called
                let ret_ty = self.resolve_type_opt(&e.return_type)?;
                self.globals.insert(e.name.clone(), ret_ty);
                // Track as extern function for codegen (BSS slot initialization)
                self.extern_fn_names.insert(e.name.clone());
            }
            Node::ExternClass(ec) => {
                // Register extern class type
                // For now, just register the class name as a named type
                let type_id = self.module.types.register_named(
                    ec.name.clone(),
                    crate::hir::types::HirType::ExternClass { name: ec.name.clone() },
                );
                // Also register it as a global so it can be used in type expressions
                self.globals.insert(ec.name.clone(), type_id);
            }
            Node::Static(s) => {
                // Register global/static variable
                // Resolve the type if provided, otherwise use Any for dynamic typing
                let ty = if let Some(ref t) = s.ty {
                    self.resolve_type(t).unwrap_or(TypeId::ANY)
                } else {
                    TypeId::ANY
                };
                self.globals.insert(s.name.clone(), ty);
            }
            Node::Const(c) => {
                // Register constant
                let ty = if let Some(ref t) = c.ty {
                    self.resolve_type(t).unwrap_or(TypeId::ANY)
                } else {
                    TypeId::ANY
                };
                self.globals.insert(c.name.clone(), ty);
            }
            Node::Let(l) => {
                // Register module-level variable (var at module scope = global)
                // Extract name from pattern, handling Pattern::Typed wrapper
                let name = extract_pattern_name(&l.pattern);
                if let Some(n) = name {
                    let ty = if let Some(ref t) = l.ty {
                        self.resolve_type(t).unwrap_or(TypeId::ANY)
                    } else {
                        TypeId::ANY
                    };
                    self.globals.insert(n, ty);
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Lower Lean 4 blocks from AST to HIR.
    ///
    /// This collects all lean blocks (inline code and imports) for later
    /// emission during Lean code generation.
    fn lower_lean_blocks(&mut self, ast_module: &Module) {
        let module_name = ast_module.name.clone().unwrap_or_else(|| "module".to_string());

        for item in &ast_module.items {
            if let Node::LeanBlock(lean_block) = item {
                let context = module_name.clone();

                let hir_lean_block = if let Some(ref import_path) = lean_block.import_path {
                    if lean_block.code.is_empty() {
                        HirLeanBlock::import(import_path.clone(), context)
                    } else {
                        HirLeanBlock::import_with_code(import_path.clone(), lean_block.code.clone(), context)
                    }
                } else {
                    HirLeanBlock::inline(lean_block.code.clone(), context)
                };

                self.module.lean_blocks.push(hir_lean_block);
            }
        }
    }

    /// Lower AOP constructs (advice, DI bindings, architecture rules, mocks) from AST to HIR.
    ///
    /// This pass processes:
    /// - AOP advice (before/after/around interceptors) #1000-1050
    /// - Dependency injection bindings
    /// - Architecture rules (forbid/allow patterns)
    /// - Mock declarations for testing
    fn lower_aop_constructs(&mut self, ast_module: &Module) -> LowerResult<()> {
        for item in &ast_module.items {
            match item {
                Node::AopAdvice(advice) => {
                    self.module.aop_advices.push(HirAopAdvice {
                        predicate_text: self.predicate_to_string(&advice.pointcut),
                        advice_function: advice.interceptor.clone(),
                        form: advice.advice_type.as_str().to_string(),
                        priority: advice.priority.unwrap_or(0),
                    });
                }
                Node::DiBinding(binding) => {
                    self.module.di_bindings.push(HirDiBinding {
                        predicate_text: self.predicate_to_string(&binding.pointcut),
                        implementation: binding.implementation.clone(),
                        scope: binding.scope.map(|s| s.as_str().to_string()),
                        priority: binding.priority.unwrap_or(0),
                    });
                }
                Node::ArchitectureRule(rule) => {
                    self.module.arch_rules.push(HirArchRule {
                        rule_type: match rule.rule_type {
                            ast::ArchRuleType::Forbid => "forbid".to_string(),
                            ast::ArchRuleType::Allow => "allow".to_string(),
                        },
                        predicate_text: self.predicate_to_string(&rule.pointcut),
                        message: rule.message.clone(),
                        priority: 0,
                    });
                }
                Node::MockDecl(mock) => {
                    let mut expectations = Vec::new();
                    for exp in &mock.expectations {
                        expectations.push(self.lower_mock_expectation(exp)?);
                    }
                    self.module.mock_decls.push(HirMockDecl {
                        name: mock.name.clone(),
                        trait_name: mock.trait_name.clone(),
                        expectations,
                    });
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub fn lower_module(mut self, ast_module: &Module) -> LowerResult<HirModule> {
        self.module.name = ast_module.name.clone();

        // Pass 0: Pre-register all struct/class/enum names to allow self-referential types
        // This registers placeholders so types can reference each other
        for item in &ast_module.items {
            match item {
                Node::Struct(s) => {
                    // Register placeholder struct so it can be referenced by other types
                    self.module.types.register_named(
                        s.name.clone(),
                        HirType::Struct {
                            name: s.name.clone(),
                            fields: vec![],
                            has_snapshot: false,
                            generic_params: s.generic_params.clone(),
                            is_generic_template: s.is_generic_template,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                Node::Class(c) => {
                    // Register placeholder for class (uses Struct internally)
                    self.module.types.register_named(
                        c.name.clone(),
                        HirType::Struct {
                            name: c.name.clone(),
                            fields: vec![],
                            has_snapshot: false,
                            generic_params: c.generic_params.clone(),
                            is_generic_template: c.is_generic_template,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                Node::Enum(e) => {
                    // Register placeholder enum so it can be referenced by other types
                    self.module.types.register_named(
                        e.name.clone(),
                        HirType::Enum {
                            name: e.name.clone(),
                            variants: vec![],
                            generic_params: e.generic_params.clone(),
                            is_generic_template: e.is_generic_template,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                _ => {}
            }
        }

        // Pass 0.5: Load types from imported modules BEFORE declaration registration.
        // This ensures imported types are available when resolving function signatures
        // and struct field types in Pass 1.
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                // Silently ignore import loading failures for backward compatibility
                let _ = self.load_imported_types(&use_stmt.path, &use_stmt.target);
            }
        }

        // First pass: collect type and function declarations (with full field resolution)
        for item in &ast_module.items {
            self.register_declarations_from_node(item)?;
        }

        // Continue with rest of lowering...
        for item in &ast_module.items {
            match item {
                // These were already registered in first pass
                Node::Struct(_)
                | Node::Function(_)
                | Node::Class(_)
                | Node::Enum(_)
                | Node::Mixin(_)
                | Node::TypeAlias(_)
                | Node::Trait(_) => {}
                // Other node types
                Node::Actor(_)
                | Node::Impl(_)
                | Node::Extern(_)
                | Node::ExternClass(_)
                | Node::Macro(_)
                | Node::Unit(_)
                | Node::UnitFamily(_)
                | Node::Bitfield(_)
                | Node::InterfaceBinding(_) => {}
                Node::Let(_)
                | Node::Const(_)
                | Node::Static(_)
                | Node::Assignment(_)
                | Node::Return(_)
                | Node::If(_)
                | Node::Match(_)
                | Node::For(_)
                | Node::While(_)
                | Node::Loop(_)
                | Node::Break(_)
                | Node::Continue(_)
                | Node::Assert(_)
                | Node::Assume(_)
                | Node::Admit(_)
                | Node::ProofHint(_)
                | Node::Calc(_)
                | Node::Context(_)
                | Node::With(_)
                | Node::Expression(_) => {}
                Node::ModDecl(_)
                | Node::UseStmt(_)
                | Node::MultiUse(_)
                | Node::CommonUseStmt(_)
                | Node::ExportUseStmt(_)
                | Node::StructuredExportStmt(_)
                | Node::AutoImportStmt(_)
                | Node::RequiresCapabilities(_)
                | Node::CompoundUnit(_)
                | Node::HandlePool(_)
                | Node::AopAdvice(_)
                | Node::DiBinding(_)
                | Node::ArchitectureRule(_)
                | Node::MockDecl(_)
                | Node::LiteralFunction(_)
                | Node::LeanBlock(_)
                | Node::ClassAlias(_)
                | Node::FunctionAlias(_)
                | Node::Pass(_)
                | Node::Skip(_)
                | Node::Guard(_)
                | Node::Defer(_)
                | Node::InlineAsm(_)
                | Node::Newtype(_)
                | Node::Extend(_) => {}
            }
        }

        // Pre-register method return types (before lowering bodies)
        for item in &ast_module.items {
            match item {
                Node::Function(f) => {
                    let ret_ty = self.resolve_type_opt(&f.return_type).unwrap_or(TypeId::ANY);
                    self.method_return_types.insert(f.name.clone(), ret_ty);
                }
                Node::Class(c) => {
                    for method in &c.methods {
                        let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                        let qualified = format!("{}.{}", c.name, method.name);
                        self.method_return_types.insert(qualified, ret_ty);
                    }
                }
                Node::Struct(s) => {
                    for method in &s.methods {
                        let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                        let qualified = format!("{}.{}", s.name, method.name);
                        self.method_return_types.insert(qualified, ret_ty);
                    }
                }
                Node::Impl(impl_block) => {
                    let type_name = match &impl_block.target_type {
                        simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                        simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                        _ => None,
                    };
                    if let Some(type_name) = type_name {
                        for method in &impl_block.methods {
                            let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                            let qualified = format!("{}.{}", type_name, method.name);
                            self.method_return_types.insert(qualified, ret_ty);
                        }
                    }
                }
                _ => {}
            }
        }

        // Second pass: lower function bodies and class/struct methods
        for item in &ast_module.items {
            match item {
                Node::Function(f) => {
                    let hir_func = self.lower_function(f, None)?;
                    self.module.functions.push(hir_func);
                }
                Node::Class(c) => {
                    // Lower class methods with type invariant injection
                    for method in &c.methods {
                        let hir_func = self.lower_function(method, Some(&c.name))?;
                        self.module.functions.push(hir_func);
                    }

                    // Lower mixin methods applied to this class
                    for mixin_ref in &c.mixins {
                        if let Some(mixin_decl) = ast_module.items.iter().find_map(|item| {
                            if let Node::Mixin(m) = item {
                                if m.name == mixin_ref.name {
                                    Some(m)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }) {
                            // Lower mixin methods for this class
                            for method in &mixin_decl.methods {
                                let hir_func = self.lower_function(method, Some(&c.name))?;
                                self.module.functions.push(hir_func);
                            }
                        }
                    }
                }
                Node::Struct(s) => {
                    // Lower struct methods with type invariant injection
                    for method in &s.methods {
                        let hir_func = self.lower_function(method, Some(&s.name))?;
                        self.module.functions.push(hir_func);
                    }
                }
                Node::Impl(impl_block) => {
                    // Lower impl block methods
                    // Extract the type name from the impl block's target
                    let type_name = match &impl_block.target_type {
                        simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                        simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                        _ => None,
                    };

                    if let Some(type_name) = type_name {
                        for method in &impl_block.methods {
                            let hir_func = self.lower_function(method, Some(&type_name))?;
                            self.module.functions.push(hir_func);
                        }
                    }
                }
                _ => {}
            }
        }

        // Copy global variables from HashMap to module's globals Vec
        for (name, ty) in &self.globals {
            self.module.globals.push((name.clone(), *ty));
        }

        // Copy extern function names to HirModule for codegen
        self.module.extern_fn_names = self.extern_fn_names.clone();

        // Third pass: lower AOP constructs (#1000-1050)
        self.lower_aop_constructs(ast_module)?;

        // New pass: collect Lean 4 blocks for verification
        self.lower_lean_blocks(ast_module);

        // Fourth pass: lower import statements for dependency tracking AND load types
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                let import = self.lower_import(&use_stmt.path, &use_stmt.target, use_stmt.is_type_only, use_stmt.is_lazy);
                self.module.imports.push(import);

                // NEW: Load types from imported module into globals symbol table
                // This enables compile-time type checking for imports
                // Errors are silently ignored for backward compatibility
                let _ = self.load_imported_types(&use_stmt.path, &use_stmt.target);
            }
        }

        // Fifth pass: validate sync→async calls (async validation design decision #3)
        self.validate_sync_async_calls()?;

        // Sixth pass: apply Promise auto-wrapping for async functions (design decision #2)
        let mut type_checker = crate::type_check::TypeChecker::new();
        type_checker.apply_promise_wrapping(&mut self.module)?;

        // Seventh pass: check for lifetime violations (E2001-E2006)
        if self.lifetime_context.has_violations() {
            let violations = self.lifetime_context.violations().to_vec();
            if violations.len() == 1 {
                return Err(LowerError::LifetimeViolation(violations.into_iter().next().unwrap()));
            } else {
                return Err(LowerError::LifetimeViolations(violations));
            }
        }

        // Eighth pass: in strict mode (Rust-level safety), memory warnings become errors
        if self.memory_warnings.is_strict() && self.memory_warnings.has_warnings() {
            let first_warning = self.memory_warnings.warnings().first().unwrap();
            return Err(LowerError::MemorySafetyViolation {
                code: first_warning.code,
                message: format!(
                    "{}{}{}",
                    first_warning.code.description(),
                    first_warning
                        .name
                        .as_ref()
                        .map(|n| format!(" ({})", n))
                        .unwrap_or_default(),
                    first_warning
                        .context
                        .as_ref()
                        .map(|c| format!(": {}", c))
                        .unwrap_or_default()
                ),
                span: first_warning.span,
                all_warnings: std::mem::take(&mut self.memory_warnings),
            });
        }

        Ok(self.module)
    }

    /// Lower an AST module to HIR and return warnings along with the module
    pub fn lower_module_with_warnings(mut self, ast_module: &Module) -> LowerResult<super::super::LoweringOutput> {
        // Perform all lowering passes
        self.module.name = ast_module.name.clone();

        // First pass: collect type and function declarations
        for item in &ast_module.items {
            self.register_declarations_from_node(item)?;
        }

        // Second pass: lower function bodies
        for item in &ast_module.items {
            match item {
                Node::Function(f) => {
                    let hir_func = self.lower_function(f, None)?;
                    self.module.functions.push(hir_func);
                }
                Node::Class(c) => {
                    for method in &c.methods {
                        let hir_func = self.lower_function(method, Some(&c.name))?;
                        self.module.functions.push(hir_func);
                    }
                    for mixin_ref in &c.mixins {
                        if let Some(mixin_decl) = ast_module.items.iter().find_map(|item| {
                            if let Node::Mixin(m) = item {
                                if m.name == mixin_ref.name {
                                    Some(m)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }) {
                            for method in &mixin_decl.methods {
                                let hir_func = self.lower_function(method, Some(&c.name))?;
                                self.module.functions.push(hir_func);
                            }
                        }
                    }
                }
                Node::Struct(s) => {
                    for method in &s.methods {
                        let hir_func = self.lower_function(method, Some(&s.name))?;
                        self.module.functions.push(hir_func);
                    }
                }
                Node::Impl(impl_block) => {
                    // Lower impl block methods (second pass)
                    let type_name = match &impl_block.target_type {
                        simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                        simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                        _ => None,
                    };

                    if let Some(type_name) = type_name {
                        for method in &impl_block.methods {
                            let hir_func = self.lower_function(method, Some(&type_name))?;
                            self.module.functions.push(hir_func);
                        }
                    }
                }
                _ => {}
            }
        }

        // Third pass: lower AOP constructs
        self.lower_aop_constructs(ast_module)?;

        // Lean pass: collect Lean 4 blocks for verification
        self.lower_lean_blocks(ast_module);

        // Fourth pass: lower imports
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                let import = self.lower_import(&use_stmt.path, &use_stmt.target, use_stmt.is_type_only, use_stmt.is_lazy);
                self.module.imports.push(import);
                let _ = self.load_imported_types(&use_stmt.path, &use_stmt.target);
            }
        }

        // Fifth pass: validate sync→async calls
        self.validate_sync_async_calls()?;

        // Sixth pass: apply Promise auto-wrapping
        let mut type_checker = crate::type_check::TypeChecker::new();
        type_checker.apply_promise_wrapping(&mut self.module)?;

        // Seventh pass: capture lifetime information for Lean 4 verification
        let lifetime_lean4 = self.lifetime_context.generate_lean4();
        let lifetime_violations = self.lifetime_context.violations().to_vec();

        // Check for lifetime violations (E2001-E2006)
        if !lifetime_violations.is_empty() {
            // Return error with lifetime violations
            if lifetime_violations.len() == 1 {
                return Err(LowerError::LifetimeViolation(
                    lifetime_violations.into_iter().next().unwrap(),
                ));
            } else {
                return Err(LowerError::LifetimeViolations(lifetime_violations));
            }
        }

        // Copy extern function names to HirModule for codegen
        self.module.extern_fn_names = self.extern_fn_names.clone();

        // Take warnings before consuming self
        let warnings = std::mem::take(&mut self.memory_warnings);
        let module = self.module;

        // CRITICAL: In strict mode (Rust-level safety), memory warnings become errors
        if warnings.is_strict() && warnings.has_warnings() {
            // Convert most severe warning to error
            let first_warning = warnings.warnings().first().unwrap();
            return Err(LowerError::MemorySafetyViolation {
                code: first_warning.code,
                message: format!(
                    "{}{}{}",
                    first_warning.code.description(),
                    first_warning
                        .name
                        .as_ref()
                        .map(|n| format!(" ({})", n))
                        .unwrap_or_default(),
                    first_warning
                        .context
                        .as_ref()
                        .map(|c| format!(": {}", c))
                        .unwrap_or_default()
                ),
                span: first_warning.span,
                all_warnings: warnings,
            });
        }

        Ok(super::super::LoweringOutput::with_lifetime(
            module,
            warnings,
            lifetime_lean4,
            lifetime_violations,
        ))
    }
}

/// Extract the variable name from a pattern, handling Pattern::Typed wrapper.
fn extract_pattern_name(pattern: &simple_parser::Pattern) -> Option<String> {
    use simple_parser::Pattern;
    match pattern {
        Pattern::Identifier(n) => Some(n.clone()),
        Pattern::MutIdentifier(n) => Some(n.clone()),
        Pattern::Typed { pattern: inner, .. } => extract_pattern_name(inner),
        _ => None,
    }
}
