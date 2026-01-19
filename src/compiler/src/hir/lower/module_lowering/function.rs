use simple_parser as ast;

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{
    ConcurrencyMode, FunctionLayoutHint, HirContract, HirFunction, LayoutAnchor, LayoutPhase, LocalVar, TypeId,
};

impl Lowerer {
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
    fn is_constructor(&self, f: &ast::FunctionDef, owner_type: Option<&str>, return_type: TypeId) -> bool {
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
    pub(super) fn lower_function(
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
                    use crate::hir::capability::CapabilityEnv;
                    CapabilityEnv::check_mode_compatibility(*capability, concurrency_mode, &f.name)
                        .map_err(LowerError::Capability)?;
                }
                self.resolve_type(t)?
            } else if param.name == "self" && owner_type.is_some() {
                // Special case: implicit self parameter in methods
                // The parser adds an implicit self parameter with ty: None
                // We infer it as the class type
                self.current_class_type.unwrap_or(TypeId::VOID)
            } else {
                return Err(LowerError::MissingParameterType(param.name.clone()));
            };
            ctx.add_local_with_inject(param.name.clone(), ty, param.mutability, param.inject);
        }

        let params: Vec<LocalVar> = ctx.locals.clone();
        let params_len = params.len();

        let body = self.lower_block(&f.body, &mut ctx)?;

        // Detect suspension operators in function body for async/sync validation
        let has_suspension = simple_parser::effect_inference::has_suspension_in_body(&f.body);

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
                    if let Some(type_invariant) = self.module.type_invariants.get(type_name).cloned() {
                        let contract = contract.get_or_insert_with(HirContract::default);
                        for clause in &type_invariant.conditions {
                            // Substitute self (local 0) with the parameter index
                            let substituted_condition = clause.condition.substitute_local(0, param_idx);
                            contract.preconditions.push(crate::hir::types::HirContractClause {
                                condition: substituted_condition,
                                message: clause
                                    .message
                                    .clone()
                                    .or_else(|| Some(format!("Type invariant for parameter '{}'", param.name))),
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
                        contract.postconditions.push(crate::hir::types::HirContractClause {
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
            span: Some(f.span),
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
            is_sync: f.is_sync,
            has_suspension,
        })
    }
}
