use simple_parser::{self as ast, Module, Node};

use super::context::{ContractLoweringContext, FunctionContext};
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use super::super::types::*;

impl Lowerer {
    pub fn lower_module(mut self, ast_module: &Module) -> LowerResult<HirModule> {
        self.module.name = ast_module.name.clone();

        // Pass 0: Pre-register all struct/class/enum names as I64 placeholders.
        // This allows forward references in field types (e.g., Dict<K, HirFunction>
        // where HirFunction is defined after the type that references it).
        for item in &ast_module.items {
            match item {
                Node::Struct(s) => {
                    if self.module.types.lookup(&s.name).is_none() {
                        self.module.types.register_named(
                            s.name.clone(),
                            HirType::Struct {
                                name: s.name.clone(),
                                fields: vec![],
                                has_snapshot: false,
                            },
                        );
                    }
                }
                Node::Class(c) => {
                    if self.module.types.lookup(&c.name).is_none() {
                        self.module.types.register_named(
                            c.name.clone(),
                            HirType::Struct {
                                name: c.name.clone(),
                                fields: vec![],
                                has_snapshot: false,
                            },
                        );
                    }
                }
                Node::Enum(e) => {
                    if self.module.types.lookup(&e.name).is_none() {
                        self.module.types.register_named(
                            e.name.clone(),
                            HirType::Enum {
                                name: e.name.clone(),
                                variants: vec![],
                            },
                        );
                    }
                }
                _ => {}
            }
        }

        // First pass: collect type and function declarations (re-registers with full field info)
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
                            let fields = v.fields.as_ref().map(|types| {
                                types
                                    .iter()
                                    .map(|t| self.resolve_type(t).unwrap_or(TypeId::VOID))
                                    .collect()
                            });
                            (v.name.clone(), fields)
                        })
                        .collect();
                    let hir_type = HirType::Enum {
                        name: e.name.clone(),
                        variants,
                    };
                    // If already pre-registered (pass 0), update existing
                    if let Some(existing_id) = self.module.types.lookup(&e.name) {
                        self.module.types.update_type(existing_id, hir_type);
                    } else {
                        self.module.types.register_named(e.name.clone(), hir_type);
                    }
                }
                Node::TypeAlias(ta) => {
                    self.register_type_alias(ta)?;
                }
                Node::Impl(impl_block) => {
                    // Register impl methods in the first pass so they can be resolved.
                    // Use both unqualified and qualified names so method calls on
                    // typed receivers resolve to the correct return type.
                    for method in &impl_block.methods {
                        let ret_ty = self.resolve_type_opt(&method.return_type)?;
                        // Extract the type name from the Type enum
                        let target_name = match &impl_block.target_type {
                            ast::Type::Simple(name) => name.clone(),
                            ast::Type::Generic { name, .. } => name.clone(),
                            other => format!("{:?}", other),
                        };
                        // Qualified name (e.g., "MirLowering::lower_module")
                        let qualified = format!("{}::{}", target_name, method.name);
                        self.globals.insert(qualified, ret_ty);
                        // Unqualified name — only insert if not already registered,
                        // to avoid overwriting a different impl's return type
                        self.globals.entry(method.name.clone()).or_insert(ret_ty);
                    }
                }
                Node::Trait(_)
                | Node::Actor(_)
                | Node::Extern(_)
                | Node::Macro(_)
                | Node::Unit(_)
                | Node::UnitFamily(_) => {}
                Node::Let(l) => {
                    // Module-level variable declaration (val or var)
                    // Extract name from pattern, handling Typed wrapper
                    let name = extract_pattern_name(&l.pattern);
                    if let Some(name) = name {
                        let ty = extract_pattern_type(&l.pattern)
                            .and_then(|t| self.resolve_type(t).ok())
                            .or_else(|| l.ty.as_ref().and_then(|t| self.resolve_type(t).ok()))
                            .unwrap_or(TypeId::I64);
                        self.globals.insert(name.clone(), ty);
                        self.module.globals.push((name.clone(), ty));
                    }
                }
                Node::Const(_)
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
                | Node::AutoImportStmt(_) => {}
            }
        }

        // Second pass: lower function bodies, class/struct methods, and module init
        let mut init_body: Vec<HirStmt> = Vec::new();
        let mut init_ctx = FunctionContext::new(TypeId::VOID);
        let mut has_init = false;

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
                }
                Node::Struct(s) => {
                    // Lower struct methods with type invariant injection
                    for method in &s.methods {
                        let hir_func = self.lower_function(method, Some(&s.name))?;
                        self.module.functions.push(hir_func);
                    }
                }
                Node::Let(l) => {
                    // Module-level variable with initializer → add to __module_init
                    if let Some(ref value) = l.value {
                        let name = extract_pattern_name(&l.pattern);
                        if let Some(name) = name {
                            let init_expr = self.lower_expr(value, &mut init_ctx)?;
                            init_body.push(HirStmt::Assign {
                                target: HirExpr {
                                    kind: HirExprKind::Global(name),
                                    ty: init_expr.ty,
                                },
                                value: init_expr,
                            });
                            has_init = true;
                        }
                    }
                }
                Node::Expression(e) => {
                    // Module-level expression → add to __module_init
                    if let Ok(expr) = self.lower_expr(e, &mut init_ctx) {
                        init_body.push(HirStmt::Expr(expr));
                        has_init = true;
                    }
                }
                Node::Impl(impl_block) => {
                    // Lower impl block methods with the target type as owner
                    let owner_name = match &impl_block.target_type {
                        simple_parser::Type::Simple(name) => Some(name.as_str()),
                        _ => None,
                    };
                    for method in &impl_block.methods {
                        let hir_func = self.lower_function(method, owner_name)?;
                        self.module.functions.push(hir_func);
                    }
                }
                _ => {}
            }
        }

        // Emit __module_init function if there are module-level initializers
        if has_init {
            self.module.functions.push(HirFunction {
                name: "__module_init".to_string(),
                params: Vec::new(),
                locals: init_ctx.locals,
                return_type: TypeId::VOID,
                body: init_body,
                visibility: simple_parser::ast::Visibility::Public,
                contract: None,
                is_pure: false,
            });
        }

        Ok(self.module)
    }

    /// Register a class type and its invariant
    fn register_class(&mut self, c: &ast::ClassDef) -> LowerResult<TypeId> {
        let fields: Vec<_> = c
            .fields
            .iter()
            .map(|f| {
                (
                    f.name.clone(),
                    self.resolve_type(&f.ty).unwrap_or(TypeId::VOID),
                )
            })
            .collect();

        let hir_type = HirType::Struct {
            name: c.name.clone(),
            fields,
            has_snapshot: c.is_snapshot(),
        };
        // If already pre-registered (pass 0), update the existing type
        let type_id = if let Some(existing_id) = self.module.types.lookup(&c.name) {
            self.module.types.update_type(existing_id, hir_type);
            existing_id
        } else {
            self.module.types.register_named(c.name.clone(), hir_type)
        };

        // Register class invariant if present
        if let Some(ref invariant) = c.invariant {
            let mut ctx = FunctionContext::new(TypeId::VOID);
            let mut hir_invariant = HirTypeInvariant::default();

            for clause in &invariant.conditions {
                let condition = self.lower_expr(&clause.condition, &mut ctx)?;
                hir_invariant.conditions.push(HirContractClause {
                    condition,
                    message: clause.message.clone(),
                });
            }

            self.module
                .type_invariants
                .insert(c.name.clone(), hir_invariant);
        }

        Ok(type_id)
    }

    fn register_struct(&mut self, s: &ast::StructDef) -> LowerResult<TypeId> {
        let mut fields = Vec::new();
        for field in &s.fields {
            let ty = self.resolve_type(&field.ty)?;
            fields.push((field.name.clone(), ty));
        }

        let hir_type = HirType::Struct {
            name: s.name.clone(),
            fields,
            has_snapshot: s.is_snapshot(),
        };

        // If already pre-registered (pass 0), update the existing type rather than creating new
        let type_id = if let Some(existing_id) = self.module.types.lookup(&s.name) {
            self.module.types.update_type(existing_id, hir_type);
            existing_id
        } else {
            self.module.types.register_named(s.name.clone(), hir_type)
        };

        // Register struct invariant if present
        if let Some(ref invariant) = s.invariant {
            let mut ctx = FunctionContext::new(TypeId::VOID);
            let mut hir_invariant = HirTypeInvariant::default();

            for clause in &invariant.conditions {
                let condition = self.lower_expr(&clause.condition, &mut ctx)?;
                hir_invariant.conditions.push(HirContractClause {
                    condition,
                    message: clause.message.clone(),
                });
            }

            self.module
                .type_invariants
                .insert(s.name.clone(), hir_invariant);
        }

        Ok(type_id)
    }

    /// Register a type alias, with optional refinement predicate (CTR-020)
    fn register_type_alias(&mut self, ta: &ast::TypeAliasDef) -> LowerResult<TypeId> {
        let base_type = self.resolve_type(&ta.ty)?;

        // Register the type alias name as an alias to the base type
        // For now, we just use the base type ID directly
        // The refinement predicate is stored separately for runtime checks

        if let Some(ref where_clause) = ta.where_clause {
            // This is a refined type: `type PosI64 = i64 where self > 0`
            // Lower the predicate with a synthetic 'self' binding
            let mut ctx = FunctionContext::new(base_type);
            // Add 'self' as a local variable for the predicate
            ctx.add_local("self".to_string(), base_type, simple_parser::Mutability::Immutable);

            let predicate = self.lower_expr(where_clause, &mut ctx)?;

            let refined_type = super::super::types::HirRefinedType {
                name: ta.name.clone(),
                base_type,
                predicate,
            };

            self.module.refined_types.insert(ta.name.clone(), refined_type);
        }

        // Register the type alias name to map to the base type
        self.module.types.register_alias(ta.name.clone(), base_type);

        Ok(base_type)
    }

    /// Lower a function, optionally injecting type invariants for methods
    /// `owner_type`: If this function is a method, the name of the owning type
    fn lower_function(
        &mut self,
        f: &ast::FunctionDef,
        owner_type: Option<&str>,
    ) -> LowerResult<HirFunction> {
        let return_type = self.resolve_type_opt(&f.return_type)?;
        let mut ctx = FunctionContext::new(return_type);

        // For `fn` methods inside a class/struct, the parser doesn't add
        // an implicit `self` param (only `me` methods get it). We ALWAYS
        // add one for methods so the C function signature matches call
        // sites where the receiver is passed as first arg.
        let has_explicit_self = f.params.iter().any(|p| p.name == "self" || p.name == "me");
        if owner_type.is_some() && !has_explicit_self && body_references_self(&f.body) {
            let owner_ty = owner_type
                .and_then(|o| self.module.types.lookup(o))
                .unwrap_or(TypeId::I64);
            ctx.add_local("self".to_string(), owner_ty, simple_parser::Mutability::Immutable);
        }

        // Add parameters as locals
        for param in &f.params {
            let ty = if param.name == "self" || param.name == "me" {
                // Method self/me parameter: use the owner struct/class type
                // so field accesses compute correct byte offsets.
                if let Some(owner) = owner_type {
                    self.module.types.lookup(owner).unwrap_or(TypeId::I64)
                } else {
                    TypeId::I64
                }
            } else if let Some(t) = &param.ty {
                self.resolve_type(t)?
            } else {
                // Bootstrap: untyped params default to I64
                TypeId::I64
            };
            ctx.add_local(param.name.clone(), ty, param.mutability);
        }

        let params: Vec<LocalVar> = ctx.locals.clone();
        let params_len = params.len();

        let mut body = self.lower_block(&f.body, &mut ctx)?;

        // Implicit return: if the function has a non-void return type and the
        // last statement is an expression (not already a Return), convert it
        // to a Return statement. This handles Simple's "last expression is
        // the return value" semantics (e.g. `fn main() -> i64: 42`).
        if return_type != TypeId::VOID {
            let last_is_expr = matches!(body.last(), Some(HirStmt::Expr(_)));
            if last_is_expr {
                if let Some(HirStmt::Expr(expr)) = body.pop() {
                    body.push(HirStmt::Return(Some(expr)));
                }
            }
        }

        // Lower contract if present, or create one for type invariants
        let mut contract = if let Some(ref ast_contract) = f.contract {
            Some(self.lower_contract(ast_contract, &mut ctx)?)
        } else {
            None
        };

        // Inject type invariants for public methods (CTR-011)
        if let Some(type_name) = owner_type {
            if f.visibility.is_public() {
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
                            message: clause.message.clone().or_else(|| {
                                Some("Type invariant for return value".to_string())
                            }),
                        });
                    }
                }
            }
        }

        // Qualify method names with owner class for unique C function names.
        let func_name = if let Some(owner) = owner_type {
            format!("{}::{}", owner, f.name)
        } else {
            f.name.clone()
        };

        Ok(HirFunction {
            name: func_name,
            params,
            locals: ctx.locals[params_len..].to_vec(),
            return_type,
            body,
            visibility: f.visibility,
            contract,
            is_pure: f.is_pure(),
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

        // Clear contract context
        ctx.contract_ctx = None;

        Ok(hir_contract)
    }
}

/// Extract variable name from a pattern, handling Typed wrapper.
fn extract_pattern_name(pattern: &simple_parser::Pattern) -> Option<String> {
    match pattern {
        simple_parser::Pattern::Identifier(n) => Some(n.clone()),
        simple_parser::Pattern::MutIdentifier(n) => Some(n.clone()),
        simple_parser::Pattern::Typed { pattern, .. } => extract_pattern_name(pattern),
        _ => None,
    }
}

/// Extract type from a Typed pattern wrapper.
fn extract_pattern_type(pattern: &simple_parser::Pattern) -> Option<&simple_parser::ast::Type> {
    match pattern {
        simple_parser::Pattern::Typed { ty, .. } => Some(ty),
        _ => None,
    }
}

/// Check if a function body references `self` or `me` as an identifier.
/// Used to determine if an `fn` method needs an implicit `self` parameter.
fn body_references_self(block: &simple_parser::Block) -> bool {
    use simple_parser::Expr;
    for node in &block.statements {
        if node_references_self(node) {
            return true;
        }
    }
    false
}

fn expr_references_self(expr: &simple_parser::Expr) -> bool {
    use simple_parser::Expr;
    match expr {
        Expr::Identifier(name) if name == "self" || name == "me" => true,
        Expr::FieldAccess { receiver, .. } => expr_references_self(receiver),
        Expr::MethodCall { receiver, args, .. } => {
            expr_references_self(receiver)
                || args.iter().any(|a| expr_references_self(&a.value))
        }
        Expr::Call { callee, args } => {
            expr_references_self(callee)
                || args.iter().any(|a| expr_references_self(&a.value))
        }
        Expr::Binary { left, right, .. } => {
            expr_references_self(left) || expr_references_self(right)
        }
        Expr::Unary { operand, .. } => expr_references_self(operand),
        Expr::If { condition, then_branch, else_branch } => {
            expr_references_self(condition)
                || expr_references_self(then_branch)
                || else_branch.as_ref().map_or(false, |e| expr_references_self(e))
        }
        Expr::Index { receiver, index } => {
            expr_references_self(receiver) || expr_references_self(index)
        }
        // FString: "{self.field}" contains self references in interpolated parts
        Expr::FString(parts) => {
            parts.iter().any(|part| match part {
                simple_parser::FStringPart::Expr(e) => expr_references_self(e),
                _ => false,
            })
        }
        Expr::TupleIndex { receiver, .. } => expr_references_self(receiver),
        Expr::Lambda { body, .. } => expr_references_self(body),
        Expr::Tuple(elems) | Expr::Array(elems) => {
            elems.iter().any(|e| expr_references_self(e))
        }
        Expr::Dict(pairs) => {
            pairs.iter().any(|(k, v)| expr_references_self(k) || expr_references_self(v))
        }
        Expr::StructInit { fields, .. } => {
            fields.iter().any(|(_, v)| expr_references_self(v))
        }
        Expr::Slice { receiver, start, end, step } => {
            expr_references_self(receiver)
                || start.as_ref().map_or(false, |e| expr_references_self(e))
                || end.as_ref().map_or(false, |e| expr_references_self(e))
                || step.as_ref().map_or(false, |e| expr_references_self(e))
        }
        Expr::NullCoalesce { expr: e, default } => {
            expr_references_self(e) || expr_references_self(default)
        }
        Expr::Try(e) | Expr::Spread(e) | Expr::DictSpread(e)
        | Expr::OptionalCheck(e) | Expr::Spawn(e) | Expr::Await(e)
        | Expr::ContractOld(e) | Expr::New { expr: e, .. }
        | Expr::TypeCast { expr: e, .. } => expr_references_self(e),
        Expr::Yield(opt) => opt.as_ref().map_or(false, |e| expr_references_self(e)),
        Expr::DoBlock(nodes) => nodes.iter().any(|n| node_references_self(n)),
        Expr::Match { subject, arms } => {
            expr_references_self(subject)
                || arms.iter().any(|arm| {
                    arm.body.statements.iter().any(|n| node_references_self(n))
                        || arm.guard.as_ref().map_or(false, |e| expr_references_self(e))
                })
        }
        Expr::ListComprehension { expr: e, iterable, condition, .. } => {
            expr_references_self(e)
                || expr_references_self(iterable)
                || condition.as_ref().map_or(false, |c| expr_references_self(c))
        }
        Expr::DictComprehension { key, value, iterable, condition, .. } => {
            expr_references_self(key)
                || expr_references_self(value)
                || expr_references_self(iterable)
                || condition.as_ref().map_or(false, |c| expr_references_self(c))
        }
        Expr::Range { start, end, .. } => {
            start.as_ref().map_or(false, |e| expr_references_self(e))
                || end.as_ref().map_or(false, |e| expr_references_self(e))
        }
        Expr::FunctionalUpdate { target, args, .. } => {
            expr_references_self(target)
                || args.iter().any(|a| expr_references_self(&a.value))
        }
        Expr::LetBinding { value, .. } => expr_references_self(value),
        // Literals and identifiers that can't contain self
        _ => false,
    }
}

fn node_references_self(node: &simple_parser::Node) -> bool {
    use simple_parser::Node;
    match node {
        Node::Expression(e) => expr_references_self(e),
        Node::Let(l) => {
            l.value.as_ref().map_or(false, |v| expr_references_self(v))
        }
        Node::Assignment(a) => {
            expr_references_self(&a.target) || expr_references_self(&a.value)
        }
        Node::Return(r) => {
            r.value.as_ref().map_or(false, |v| expr_references_self(v))
        }
        Node::If(i) => {
            expr_references_self(&i.condition)
                || i.then_block.statements.iter().any(|n| node_references_self(n))
                || i.else_block.as_ref().map_or(false, |b| {
                    b.statements.iter().any(|n| node_references_self(n))
                })
        }
        Node::While(w) => {
            expr_references_self(&w.condition)
                || w.body.statements.iter().any(|n| node_references_self(n))
        }
        Node::For(f) => {
            expr_references_self(&f.iterable)
                || f.body.statements.iter().any(|n| node_references_self(n))
        }
        Node::Match(m) => {
            expr_references_self(&m.subject)
                || m.arms.iter().any(|arm| {
                    arm.body.statements.iter().any(|n| node_references_self(n))
                })
        }
        _ => false,
    }
}
