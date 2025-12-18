use simple_parser::{self as ast, Module, Node};

use super::context::{ContractLoweringContext, FunctionContext};
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use super::super::types::*;

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
                            let fields = v.fields.as_ref().map(|types| {
                                types
                                    .iter()
                                    .map(|t| self.resolve_type(t).unwrap_or(TypeId::VOID))
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
                Node::TypeAlias(ta) => {
                    self.register_type_alias(ta)?;
                }
                Node::Trait(_)
                | Node::Actor(_)
                | Node::Impl(_)
                | Node::Extern(_)
                | Node::Macro(_)
                | Node::Unit(_)
                | Node::UnitFamily(_)
                | Node::Bitfield(_) => {}
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
                | Node::HandlePool(_) => {}
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

        let type_id = self.module.types.register_named(
            c.name.clone(),
            HirType::Struct {
                name: c.name.clone(),
                fields,
                has_snapshot: c.is_snapshot(),
            },
        );

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

        let type_id = self.module.types.register_named(s.name.clone(), hir_type);

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

        // Add parameters as locals
        for param in &f.params {
            let ty = if let Some(t) = &param.ty {
                self.resolve_type(t)?
            } else {
                return Err(LowerError::MissingParameterType(param.name.clone()));
            };
            ctx.add_local(param.name.clone(), ty, param.mutability);
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

        Ok(HirFunction {
            name: f.name.clone(),
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
