use simple_parser::{self as ast, Module, Node};

use super::super::types::*;
use super::context::{ContractLoweringContext, FunctionContext};
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;

impl Lowerer {
    pub fn lower_module(mut self, ast_module: &Module) -> LowerResult<HirModule> {
        self.module.name = ast_module.name.clone();

        // First pass: collect type and function declarations
        for item in &ast_module.items {
            match item {
                Node::Struct(s) => {
                    self.register_struct(s)?;
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
                    self.register_class(c)?;
                }
                Node::Enum(e) => {
                    let variants = e
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
                    self.module.types.register_named(
                        e.name.clone(),
                        HirType::Enum {
                            name: e.name.clone(),
                            variants,
                        },
                    );
                }
                Node::Mixin(m) => {
                    self.register_mixin(m)?;
                }
                Node::TypeAlias(ta) => {
                    self.register_type_alias(ta)?;
                }
                Node::Trait(t) => {
                    // Register trait with vtable slot information for static polymorphism
                    self.register_trait(t)?;
                }
                Node::Actor(_)
                | Node::Impl(_)
                | Node::Extern(_)
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
                | Node::Context(_)
                | Node::With(_)
                | Node::Expression(_) => {}
                Node::ModDecl(_)
                | Node::UseStmt(_)
                | Node::CommonUseStmt(_)
                | Node::ExportUseStmt(_)
                | Node::AutoImportStmt(_)
                | Node::RequiresCapabilities(_)
                | Node::CompoundUnit(_)
                | Node::HandlePool(_)
                | Node::AopAdvice(_)
                | Node::DiBinding(_)
                | Node::ArchitectureRule(_)
                | Node::MockDecl(_) => {}
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
                _ => {}
            }
        }

        // Third pass: lower AOP constructs (#1000-1050)
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
                        priority: 0, // Architecture rules don't have priority in AST
                    });
                }
                Node::MockDecl(mock) => {
                    // Convert MockExpectation to string representation for HIR
                    // TODO: [compiler][P1] Update HIR to handle structured expectations
                    let expectations = mock
                        .expectations
                        .iter()
                        .map(|exp| {
                            format!(
                                "expect {}(...) -> {:?}",
                                exp.method_name,
                                exp.return_type
                                    .as_ref()
                                    .map(|t| format!("{:?}", t))
                                    .unwrap_or_else(|| "()".to_string())
                            )
                        })
                        .collect();

                    self.module.mock_decls.push(HirMockDecl {
                        name: mock.name.clone(),
                        trait_name: mock.trait_name.clone(),
                        expectations,
                    });
                }
                _ => {}
            }
        }

        // Fourth pass: lower import statements for dependency tracking AND load types
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                let import =
                    self.lower_import(&use_stmt.path, &use_stmt.target, use_stmt.is_type_only);
                self.module.imports.push(import);

                // NEW: Load types from imported module into globals symbol table
                // This enables compile-time type checking for imports
                // Errors are silently ignored for backward compatibility
                let _ = self.load_imported_types(&use_stmt.path, &use_stmt.target);
            }
        }

        Ok(self.module)
    }

    /// Convert a PredicateExpr AST node back to its string representation.
    /// This preserves the predicate text for later evaluation by the weaving engine.
    ///
    /// Note: The AST parser uses a placeholder that stores the entire predicate string
    /// in the selector name field (with empty args). We detect this and return the
    /// name as-is, rather than adding extra parentheses.
    fn predicate_to_string(&self, pred: &ast::PredicateExpr) -> String {
        match &pred.kind {
            ast::PredicateKind::Selector { name, args } => {
                if args.is_empty() {
                    // Check if this is a placeholder from the AST parser
                    // (entire predicate stored in name, like "import(*, crate.test.*)")
                    // If the name already contains parentheses, it's the full predicate
                    if name.contains('(') && name.contains(')') {
                        name.clone()
                    } else {
                        // Otherwise it's a simple selector without args
                        format!("{}()", name)
                    }
                } else {
                    format!("{}({})", name, args.join(", "))
                }
            }
            ast::PredicateKind::Not(inner) => {
                format!("!{}", self.predicate_to_string(inner))
            }
            ast::PredicateKind::And(left, right) => {
                format!(
                    "({} & {})",
                    self.predicate_to_string(left),
                    self.predicate_to_string(right)
                )
            }
            ast::PredicateKind::Or(left, right) => {
                format!(
                    "({} | {})",
                    self.predicate_to_string(left),
                    self.predicate_to_string(right)
                )
            }
        }
    }

    /// Convert an import statement to HIR representation.
    fn lower_import(
        &self,
        path: &ast::ModulePath,
        target: &ast::ImportTarget,
        is_type_only: bool,
    ) -> crate::hir::HirImport {
        let from_path = path.segments.clone();
        let (items, is_glob) = self.flatten_import_target(target);

        crate::hir::HirImport {
            from_path,
            items,
            is_glob,
            is_type_only,
        }
    }

    /// Flatten an ImportTarget into a list of (name, alias) pairs.
    fn flatten_import_target(
        &self,
        target: &ast::ImportTarget,
    ) -> (Vec<(String, Option<String>)>, bool) {
        match target {
            ast::ImportTarget::Single(name) => (vec![(name.clone(), None)], false),
            ast::ImportTarget::Aliased { name, alias } => {
                (vec![(name.clone(), Some(alias.clone()))], false)
            }
            ast::ImportTarget::Group(targets) => {
                let mut items = Vec::new();
                for t in targets {
                    let (mut nested_items, _) = self.flatten_import_target(t);
                    items.append(&mut nested_items);
                }
                (items, false)
            }
            ast::ImportTarget::Glob => (Vec::new(), true),
        }
    }

    /// Parse concurrency mode from function attributes
    /// Returns Actor mode (default) if no attribute is found
    fn parse_concurrency_mode(attrs: &[ast::Attribute]) -> ConcurrencyMode {
        for attr in attrs {
            if attr.name == "concurrency_mode" {
                // #[concurrency_mode(lock_base)]
                if let Some(args) = &attr.args {
                    if let Some(ast::Expr::Identifier(mode)) = args.first() {
                        if let Some(cm) = ConcurrencyMode::from_attr_arg(mode) {
                            return cm;
                        }
                    }
                }
            }
        }
        ConcurrencyMode::Actor // Default
    }

    /// Detect if a function is a constructor
    /// Constructors should always check class invariants, even if private
    ///
    /// A function is considered a constructor if:
    /// - It's a method of a class/struct (owner_type is Some)
    /// - It returns an instance of the owner type
    /// - It doesn't take `self` as first parameter (static factory method)
    fn is_constructor(
        &self,
        f: &ast::FunctionDef,
        owner_type: Option<&str>,
        return_type: TypeId,
    ) -> bool {
        // Must be a method of a class/struct
        let Some(type_name) = owner_type else {
            return false;
        };

        // Must not take self (static method)
        let takes_self = f.params.first().map(|p| p.name == "self").unwrap_or(false);
        if takes_self {
            return false;
        }

        // Must return the owner type
        if let Some(owner_type_id) = self.module.types.lookup(type_name) {
            if return_type == owner_type_id {
                return true;
            }
        }

        // Also check common constructor names as a heuristic
        matches!(f.name.as_str(), "new" | "create" | "default" | "init")
            || f.name.starts_with("from_")
            || f.name.starts_with("with_")
    }

    /// Extract layout hint from #[layout(...)] attributes.
    ///
    /// Supports:
    /// - `#[layout(phase="startup")]` - layout phase annotation
    /// - `#[layout(phase="first_frame")]`
    /// - `#[layout(phase="steady")]`
    /// - `#[layout(phase="cold")]`
    /// - `#[layout(anchor="event_loop")]` - anchor annotation
    /// - `#[layout(pin)]` - pinning flag
    fn extract_layout_hint(&self, attributes: &[ast::Attribute]) -> Option<FunctionLayoutHint> {
        for attr in attributes {
            if attr.name != "layout" {
                continue;
            }

            let mut hint = FunctionLayoutHint::default();
            let mut found_layout = false;

            // Parse attribute arguments like #[layout(phase="startup", pin)]
            if let Some(args) = &attr.args {
                for arg in args {
                    match arg {
                        // Handle named arguments like phase="startup"
                        ast::Expr::Binary {
                            op: ast::BinOp::Eq,
                            left,
                            right,
                        } => {
                            if let ast::Expr::Identifier(key) = left.as_ref() {
                                if let ast::Expr::String(value) = right.as_ref() {
                                    match key.as_str() {
                                        "phase" => {
                                            if let Some(phase) = LayoutPhase::from_str(value) {
                                                hint.phase = phase;
                                                found_layout = true;
                                            }
                                        }
                                        "anchor" => {
                                            if let Some(anchor) = LayoutAnchor::from_str(value) {
                                                hint.anchor = Some(anchor);
                                                found_layout = true;
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                        }
                        // Handle flag like pin
                        ast::Expr::Identifier(name) if name == "pin" => {
                            hint.pinned = true;
                            found_layout = true;
                        }
                        _ => {}
                    }
                }
            }

            // Also support #[layout = "phase_name"] shorthand
            if let Some(ast::Expr::String(value)) = &attr.value {
                if let Some(phase) = LayoutPhase::from_str(value) {
                    hint.phase = phase;
                    found_layout = true;
                }
            }

            if found_layout {
                return Some(hint);
            }
        }
        None
    }

    /// Lower a function, optionally injecting type invariants for methods
    /// `owner_type`: If this function is a method, the name of the owning type
    fn lower_function(
        &mut self,
        f: &ast::FunctionDef,
        owner_type: Option<&str>,
    ) -> LowerResult<HirFunction> {
        // Set current class type for Self resolution
        let previous_class_type = self.current_class_type;
        if let Some(type_name) = owner_type {
            self.current_class_type = self.module.types.lookup(type_name);
        }

        let inject = f.decorators.iter().any(|dec| {
            if let ast::Expr::Identifier(name) = &dec.name {
                name == "inject" || name == "sys_inject"
            } else {
                false
            }
        });

        // Parse concurrency mode from attributes
        let concurrency_mode = Self::parse_concurrency_mode(&f.attributes);

        let return_type = self.resolve_type_opt(&f.return_type)?;
        let mut ctx = FunctionContext::new(return_type);

        // Add parameters as locals and check capability compatibility with mode
        for param in &f.params {
            let ty = if let Some(t) = &param.ty {
                // Check if parameter has a capability that's incompatible with the mode
                if let ast::Type::Capability { capability, .. } = t {
                    use super::super::capability::CapabilityEnv;
                    CapabilityEnv::check_mode_compatibility(*capability, concurrency_mode, &f.name)
                        .map_err(LowerError::Capability)?;
                }
                self.resolve_type(t)?
            } else {
                return Err(LowerError::MissingParameterType(param.name.clone()));
            };
            ctx.add_local_with_inject(param.name.clone(), ty, param.mutability, param.inject);
        }

        let params: Vec<LocalVar> = ctx.locals.clone();
        let params_len = params.len();

        let body = self.lower_block(&f.body, &mut ctx)?;

        // Lower contract if present, or create one for type invariants
        let mut contract = if let Some(ref ast_contract) = f.contract {
            Some(self.lower_contract(ast_contract, &mut ctx)?)
        } else {
            None
        };

        // Inject type invariants for public methods and constructors (CTR-011)
        // Constructors always check invariants (they establish the invariant)
        // Public methods check invariants (they maintain the invariant)
        // Private methods skip invariants (they're internal helpers)
        let is_ctor = self.is_constructor(f, owner_type, return_type);
        if let Some(type_name) = owner_type {
            if is_ctor || f.visibility.is_public() {
                if let Some(type_invariant) = self.module.type_invariants.get(type_name).cloned() {
                    // Add type invariants to function invariants
                    let contract = contract.get_or_insert_with(HirContract::default);
                    for clause in type_invariant.conditions {
                        contract.invariants.push(clause);
                    }
                }
            }
        }

        // CTR-012: Module boundary checking for public functions
        // Check type invariants for parameters and return values that cross module boundaries
        if f.visibility.is_public() && owner_type.is_none() {
            // Check parameter types for invariants (add as preconditions)
            for (param_idx, param) in params.iter().enumerate() {
                if let Some(type_name) = self.module.types.get_type_name(param.ty) {
                    if let Some(type_invariant) =
                        self.module.type_invariants.get(type_name).cloned()
                    {
                        let contract = contract.get_or_insert_with(HirContract::default);
                        for clause in &type_invariant.conditions {
                            // Substitute self (local 0) with the parameter index
                            let substituted_condition =
                                clause.condition.substitute_local(0, param_idx);
                            contract.preconditions.push(HirContractClause {
                                condition: substituted_condition,
                                message: clause.message.clone().or_else(|| {
                                    Some(format!("Type invariant for parameter '{}'", param.name))
                                }),
                            });
                        }
                    }
                }
            }

            // Check return type for invariants (add as postconditions)
            if let Some(type_name) = self.module.types.get_type_name(return_type) {
                if let Some(type_invariant) = self.module.type_invariants.get(type_name).cloned() {
                    let contract = contract.get_or_insert_with(HirContract::default);
                    for clause in &type_invariant.conditions {
                        // Substitute self (local 0) with ContractResult
                        let substituted_condition = clause.condition.substitute_self_with_result();
                        contract.postconditions.push(HirContractClause {
                            condition: substituted_condition,
                            message: clause
                                .message
                                .clone()
                                .or_else(|| Some("Type invariant for return value".to_string())),
                        });
                    }
                }
            }
        }

        // Extract attributes for AOP predicate matching
        let attributes: Vec<String> = f.attributes.iter().map(|attr| attr.name.clone()).collect();

        // Extract layout hint from #[layout(...)] attribute
        let layout_hint = self.extract_layout_hint(&f.attributes);

        // Extract effects from decorators for AOP effect() selector
        let effects: Vec<String> = f
            .decorators
            .iter()
            .filter_map(|dec| {
                // Extract identifier from decorator expression
                if let ast::Expr::Identifier(name) = &dec.name {
                    // Check if it's an effect decorator
                    if ast::Effect::from_decorator_name(name).is_some() {
                        Some(name.clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        // Get module path (currently use module name, will be enhanced later)
        let module_path = self.module.name.clone().unwrap_or_default();

        // Restore previous class type
        self.current_class_type = previous_class_type;

        // Use qualified name for methods (ClassName.method) for DI compatibility
        let name = if let Some(owner) = owner_type {
            format!("{}.{}", owner, f.name)
        } else {
            f.name.clone()
        };

        // Determine verification mode from effects
        let verification_mode = crate::hir::VerificationMode::from_effects(&f.effects);

        Ok(HirFunction {
            name,
            params,
            locals: ctx.locals[params_len..].to_vec(),
            return_type,
            body,
            visibility: f.visibility,
            contract,
            is_pure: f.is_pure(),
            inject,
            concurrency_mode,
            module_path,
            attributes,
            effects,
            layout_hint,
            verification_mode,
            is_ghost: f.is_ghost(),
        })
    }

    fn lower_contract(
        &mut self,
        contract: &ast::ContractBlock,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirContract> {
        let mut hir_contract = HirContract::default();

        // Set contract context BEFORE lowering any expressions (CTR-030-032)
        // This enables purity checking for all contract expressions
        ctx.contract_ctx = Some(ContractLoweringContext {
            postcondition_binding: contract.postcondition_binding.clone(),
            error_binding: contract.error_binding.clone(),
        });

        // Lower preconditions (purity checked via contract_ctx)
        for clause in &contract.preconditions {
            let condition = self.lower_expr(&clause.condition, ctx)?;
            hir_contract.preconditions.push(HirContractClause {
                condition,
                message: clause.message.clone(),
            });
        }

        // Lower invariants (purity checked via contract_ctx)
        for clause in &contract.invariants {
            let condition = self.lower_expr(&clause.condition, ctx)?;
            hir_contract.invariants.push(HirContractClause {
                condition,
                message: clause.message.clone(),
            });
        }

        // Lower postconditions with contract context for binding names
        if let Some(ref binding) = contract.postcondition_binding {
            hir_contract.postcondition_binding = Some(binding.clone());
        }
        if let Some(ref binding) = contract.error_binding {
            hir_contract.error_binding = Some(binding.clone());
        }

        // Lower postconditions (binding names are converted to ContractResult)
        for clause in &contract.postconditions {
            let condition = self.lower_expr(&clause.condition, ctx)?;
            hir_contract.postconditions.push(HirContractClause {
                condition,
                message: clause.message.clone(),
            });
        }

        // Lower error postconditions
        for clause in &contract.error_postconditions {
            let condition = self.lower_expr(&clause.condition, ctx)?;
            hir_contract.error_postconditions.push(HirContractClause {
                condition,
                message: clause.message.clone(),
            });
        }

        // Lower decreases clause (for Lean termination_by generation)
        // Note: This is NOT checked at runtime, only used for Lean output
        if let Some(ref clause) = contract.decreases {
            let condition = self.lower_expr(&clause.condition, ctx)?;
            hir_contract.decreases = Some(HirContractClause {
                condition,
                message: clause.message.clone(),
            });
        }

        // Clear contract context
        ctx.contract_ctx = None;

        Ok(hir_contract)
    }
}
