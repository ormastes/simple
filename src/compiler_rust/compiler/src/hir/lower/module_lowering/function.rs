use simple_parser as ast;

use crate::hir::lifetime::{ReferenceOrigin, ScopeKind};
use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{
    ConcurrencyMode, FunctionLayoutHint, HirContract, HirFunction, LayoutAnchor, LayoutPhase, LocalVar, TypeId,
};

/// Returns true when a Block represents a stub body that auto-synthesis may replace.
///
/// A body is a stub when it is:
/// - Empty (zero statements), OR
/// - A single `pass` statement (`Node::Pass`), OR
/// - A single bare `pass_todo` / `pass_do_nothing` / `pass_dn` identifier expression, OR
/// - A single `pass_todo(...)` / `pass_do_nothing(...)` / `pass_dn(...)` call expression.
///
/// Any real statement (val binding, return, assignment, …) disqualifies the body
/// so that hand-written registrations are never silently overwritten.
fn is_stub_body(body: &ast::Block) -> bool {
    match body.statements.len() {
        0 => true,
        1 => {
            match &body.statements[0] {
                // `pass` keyword as a statement
                ast::Node::Pass(_) => true,
                ast::Node::Expression(expr) => match expr {
                    // pass_todo("…") / pass_do_nothing() / pass_dn() — call form
                    ast::Expr::Call { callee, .. } => {
                        if let ast::Expr::Identifier(name) = callee.as_ref() {
                            matches!(
                                name.as_str(),
                                "pass_todo" | "pass_do_nothing" | "pass_dn" | "todo"
                            )
                        } else {
                            false
                        }
                    }
                    // bare `pass_todo` / `pass_do_nothing` / `pass_dn` with no parens
                    ast::Expr::Identifier(name) => matches!(
                        name.as_str(),
                        "pass_todo" | "pass_do_nothing" | "pass_dn" | "todo"
                    ),
                    _ => false,
                },
                _ => false,
            }
        }
        _ => false,
    }
}

/// Extract the `ops=<expr>` named argument from a `@driver(...)` attribute.
///
/// Returns `Some(expr)` when the attribute is named `"driver"` and has an
/// `ops` key in its `named_args`. Returns `None` otherwise.
fn driver_ops_arg(attrs: &[ast::Attribute]) -> Option<ast::Expr> {
    for attr in attrs {
        if attr.name != "driver" {
            continue;
        }
        if let Some(named) = &attr.named_args {
            for (key, val) in named {
                if key == "ops" {
                    return Some(val.clone());
                }
            }
        }
    }
    None
}

/// Build the synthesized registration body for a `@driver(ops=X)` function.
///
/// The generated body is semantically equivalent to the hand-written pattern:
///
/// ```spl
/// val m = DriverManifest.for_driver(<name>, <version>, <class>, <vendor>, <device_ids>)
/// val ops = <ops_expr>
/// return register_static_driver(m, ops)
/// ```
///
/// `fn_name` is used verbatim as the manifest name (the function name, not stripped).
/// Future work: add a `name=` named arg to `@driver(...)` so callers can supply an
/// explicit manifest name instead of having it derived from the registration function.
///
/// The manifest args are lifted directly from the `@driver(...)` attribute's
/// `named_args` list, falling back to positional `args` in declaration order:
///   positional[0] = class, [1] = vendor, [2] = device_ids, [3] = version
/// The same order is used by the existing Rust-seed text scanner in `compile.rs`.
fn synthesize_driver_registration_body(
    fn_name: &str,
    attrs: &[ast::Attribute],
    ops_expr: ast::Expr,
    span: ast::Span,
) -> ast::Block {
    // Helper: build a zero-span Argument (positional).
    let pos_arg = |value: ast::Expr| ast::Argument {
        name: None,
        value,
        span,
        label: None,
    };

    // Helper: look up a named arg value from the attribute, then fall back to
    // the positional args list at `fallback_idx`.
    let find_arg = |attr: &ast::Attribute, key: &str, fallback_idx: usize| -> Option<ast::Expr> {
        if let Some(named) = &attr.named_args {
            for (k, v) in named {
                if k == key {
                    return Some(v.clone());
                }
            }
        }
        attr.args.as_ref()?.get(fallback_idx).cloned()
    };

    // Locate the @driver attribute (guaranteed present — caller already checked).
    let driver_attr = attrs.iter().find(|a| a.name == "driver").unwrap();

    // --- Recover manifest args ---
    // class: positional[0] or named `class`/`dclass`
    let class_expr = find_arg(driver_attr, "class", 0)
        .or_else(|| find_arg(driver_attr, "dclass", 0))
        .unwrap_or(ast::Expr::Integer(0));

    // vendor: positional[1] or named `vendor`
    let vendor_expr = find_arg(driver_attr, "vendor", 1).unwrap_or(ast::Expr::Integer(0));

    // device_ids: positional[2] or named `device`/`devices`
    let device_expr = find_arg(driver_attr, "device", 2)
        .or_else(|| find_arg(driver_attr, "devices", 2))
        .unwrap_or_else(|| ast::Expr::Array(vec![]));

    // version: positional[3] or named `version`
    let version_expr = find_arg(driver_attr, "version", 3)
        .unwrap_or_else(|| ast::Expr::String("0.1".to_string()));

    // --- Build: val m = DriverManifest.for_driver(fn_name, version, class, vendor, device_ids) ---
    let manifest_call = ast::Expr::MethodCall {
        receiver: Box::new(ast::Expr::Identifier("DriverManifest".to_string())),
        method: "for_driver".to_string(),
        args: vec![
            pos_arg(ast::Expr::String(fn_name.to_string())),
            pos_arg(version_expr),
            pos_arg(class_expr),
            pos_arg(vendor_expr),
            pos_arg(device_expr),
        ],
        generic_args: vec![],
    };
    let let_m = ast::Node::Let(ast::LetStmt {
        span,
        pattern: ast::Pattern::Identifier("m".to_string()),
        ty: None,
        value: Some(manifest_call),
        mutability: ast::Mutability::Immutable,
        storage_class: ast::StorageClass::Auto,
        is_ghost: false,
        is_suspend: false,
    });

    // --- Build: val ops = <ops_expr> ---
    let let_ops = ast::Node::Let(ast::LetStmt {
        span,
        pattern: ast::Pattern::Identifier("ops".to_string()),
        ty: None,
        value: Some(ops_expr),
        mutability: ast::Mutability::Immutable,
        storage_class: ast::StorageClass::Auto,
        is_ghost: false,
        is_suspend: false,
    });

    // --- Build: return register_static_driver(m, ops) ---
    let register_call = ast::Expr::Call {
        callee: Box::new(ast::Expr::Identifier("register_static_driver".to_string())),
        args: vec![
            pos_arg(ast::Expr::Identifier("m".to_string())),
            pos_arg(ast::Expr::Identifier("ops".to_string())),
        ],
    };
    let return_stmt = ast::Node::Return(ast::ReturnStmt {
        span,
        value: Some(register_call),
    });

    ast::Block {
        span,
        statements: vec![let_m, let_ops, return_stmt],
    }
}

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

        // Set function name for lifetime error messages
        let func_name = if let Some(owner) = owner_type {
            format!("{}.{}", owner, f.name)
        } else {
            f.name.clone()
        };
        self.lifetime_context.set_function(&func_name);

        // Enter function scope for lifetime tracking
        self.lifetime_context.enter_scope(ScopeKind::Function, Some(f.span));

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

        // Determine if this is a method (has self parameter)
        let has_self = f.params.first().map(|p| p.name == "self").unwrap_or(false);

        // Create appropriate function context based on whether this is a method
        let mut ctx = if has_self {
            FunctionContext::new_method(return_type, f.is_me_method)
        } else {
            FunctionContext::new(return_type)
        };

        // Add parameters as locals and check capability compatibility with mode
        for (param_idx, param) in f.params.iter().enumerate() {
            // Register parameter with lifetime context
            let origin = ReferenceOrigin::Parameter {
                name: param.name.clone(),
                index: param_idx,
            };
            self.lifetime_context.register_variable(&param.name, origin);
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
            } else if self.lenient_types {
                TypeId::ANY
            } else {
                return Err(LowerError::MissingParameterType(param.name.clone()));
            };
            ctx.add_local_with_inject(param.name.clone(), ty, param.mutability, param.inject);
        }

        let params: Vec<LocalVar> = ctx.locals.clone();
        let params_len = params.len();

        // FR-DRIVER-0001: auto-synthesize the registration body when
        //   1. the function has a @driver(..., ops=X) attribute, AND
        //   2. the existing body is a stub (empty or single pass_todo/pass_dn call).
        // This lets drivers declare their registration with just:
        //   @driver(class=DriverClass.Block, vendor=0, device=[0], version="0.1", ops=my_ops)
        //   fn register_my_driver() -> Result<i32, DriverError>:
        //     pass_todo("auto-synthesized")
        // Any real body is left untouched so hand-written registrations keep working.
        let driver_synthesized: Option<ast::Block> =
            if is_stub_body(&f.body) {
                driver_ops_arg(&f.attributes).map(|ops_expr| {
                    synthesize_driver_registration_body(
                        &f.name,
                        &f.attributes,
                        ops_expr,
                        f.span,
                    )
                })
            } else {
                None
            };
        let effective_body: &ast::Block = driver_synthesized.as_ref().unwrap_or(&f.body);

        let body = self.lower_block(effective_body, &mut ctx)?;

        // Detect suspension operators in function body for async/sync validation.
        // Synthesized bodies (from @driver ops= auto-synthesis) never contain
        // suspension operators, so using the original body is correct in all cases.
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

        // VER-011: Handle return constraint for dependent function types
        // Convert `fn f(x: T) -> U where result.len() == x.len():` to a postcondition
        if let Some(ref constraint_expr) = f.return_constraint {
            let constraint_hir = self.lower_expr(constraint_expr, &mut ctx)?;
            let contract = contract.get_or_insert_with(HirContract::default);
            contract.postconditions.push(crate::hir::types::HirContractClause {
                condition: constraint_hir,
                message: Some("Return constraint".to_string()),
            });
        }

        // Extract attributes for AOP predicate matching.
        // Include both #[attr] attributes and @decorator decorators (that aren't effects).
        let mut attributes: Vec<String> = f.attributes.iter().map(|attr| attr.name.clone()).collect();
        for dec in &f.decorators {
            if let ast::Expr::Identifier(name) = &dec.name {
                if ast::Effect::from_decorator_name(name).is_none() && !attributes.contains(name) {
                    attributes.push(name.clone());
                }
            }
        }

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

        // Exit function scope for lifetime tracking
        self.lifetime_context.exit_scope();

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
