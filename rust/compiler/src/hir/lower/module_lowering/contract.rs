use simple_parser as ast;

use crate::hir::lower::context::{ContractLoweringContext, FunctionContext};
use crate::hir::lower::error::LowerResult;
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{HirContract, HirContractClause, HirExpr, HirExprKind};

/// Collect all old() expressions from an HIR expression tree.
/// Returns a vector of the inner expressions (what's inside old()).
fn collect_old_expressions(expr: &HirExpr, results: &mut Vec<HirExpr>) {
    match &expr.kind {
        HirExprKind::ContractOld(inner) => {
            // Found an old() expression - add the inner expression
            results.push(inner.as_ref().clone());
            // Also recursively check inside (shouldn't have nested old() but be safe)
            collect_old_expressions(inner, results);
        }
        // Binary operations
        HirExprKind::Binary { left, right, .. } => {
            collect_old_expressions(left, results);
            collect_old_expressions(right, results);
        }
        // Unary operations
        HirExprKind::Unary { operand, .. } => {
            collect_old_expressions(operand, results);
        }
        // Function/method calls
        HirExprKind::Call { func, args } => {
            collect_old_expressions(func, results);
            for arg in args {
                collect_old_expressions(arg, results);
            }
        }
        HirExprKind::MethodCall { receiver, args, .. } => {
            collect_old_expressions(receiver, results);
            for arg in args {
                collect_old_expressions(arg, results);
            }
        }
        // Field/index access
        HirExprKind::FieldAccess { receiver, .. } => {
            collect_old_expressions(receiver, results);
        }
        HirExprKind::Index { receiver, index } => {
            collect_old_expressions(receiver, results);
            collect_old_expressions(index, results);
        }
        // Conditionals
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_old_expressions(condition, results);
            collect_old_expressions(then_branch, results);
            if let Some(else_expr) = else_branch {
                collect_old_expressions(else_expr, results);
            }
        }
        // Tuple/Array literals
        HirExprKind::Tuple(elements) | HirExprKind::Array(elements) | HirExprKind::VecLiteral(elements) => {
            for elem in elements {
                collect_old_expressions(elem, results);
            }
        }
        // Array repeat
        HirExprKind::ArrayRepeat { value, count } => {
            collect_old_expressions(value, results);
            collect_old_expressions(count, results);
        }
        // Struct init
        HirExprKind::StructInit { fields, .. } => {
            for field_expr in fields {
                collect_old_expressions(field_expr, results);
            }
        }
        // Lambda
        HirExprKind::Lambda { body, .. } => {
            collect_old_expressions(body, results);
        }
        // Cast
        HirExprKind::Cast { expr: inner, .. } => {
            collect_old_expressions(inner, results);
        }
        // Memory operations
        HirExprKind::Ref(inner) | HirExprKind::Deref(inner) => {
            collect_old_expressions(inner, results);
        }
        HirExprKind::PointerNew { value, .. } => {
            collect_old_expressions(value, results);
        }
        // Async/generator operations
        HirExprKind::Yield(inner)
        | HirExprKind::Await(inner)
        | HirExprKind::GeneratorCreate { body: inner }
        | HirExprKind::FutureCreate { body: inner }
        | HirExprKind::ActorSpawn { body: inner } => {
            collect_old_expressions(inner, results);
        }
        // Builtin calls
        HirExprKind::BuiltinCall { args, .. } => {
            for arg in args {
                collect_old_expressions(arg, results);
            }
        }
        // GPU intrinsics
        HirExprKind::GpuIntrinsic { args, .. } => {
            for arg in args {
                collect_old_expressions(arg, results);
            }
        }
        // Neighbor access
        HirExprKind::NeighborAccess { array, .. } => {
            collect_old_expressions(array, results);
        }
        // Dict literals
        HirExprKind::Dict(entries) => {
            for (key, value) in entries {
                collect_old_expressions(key, results);
                collect_old_expressions(value, results);
            }
        }
        // Literals and simple expressions - no recursion needed
        HirExprKind::Integer(_)
        | HirExprKind::Float(_)
        | HirExprKind::Bool(_)
        | HirExprKind::String(_)
        | HirExprKind::Local(_)
        | HirExprKind::Global(_)
        | HirExprKind::Nil
        | HirExprKind::ContractResult => {}
        // Let-in expressions
        HirExprKind::LetIn { value, body, .. } => {
            collect_old_expressions(value, results);
            collect_old_expressions(body, results);
        }
    }
}

impl Lowerer {
    pub(super) fn lower_contract(
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

        // Collect all old() expressions from postconditions and invariants
        // These need to be captured at function entry for use in exit checks
        let mut old_exprs: Vec<HirExpr> = Vec::new();
        for clause in &hir_contract.postconditions {
            collect_old_expressions(&clause.condition, &mut old_exprs);
        }
        for clause in &hir_contract.error_postconditions {
            collect_old_expressions(&clause.condition, &mut old_exprs);
        }
        // Invariants may also use old() for comparing entry/exit state
        for clause in &hir_contract.invariants {
            collect_old_expressions(&clause.condition, &mut old_exprs);
        }

        // Deduplicate old() expressions and assign indices
        // We use structural equality to avoid capturing the same expression twice
        let mut seen: Vec<HirExpr> = Vec::new();
        for expr in old_exprs {
            if !seen.iter().any(|e| e == &expr) {
                seen.push(expr);
            }
        }

        // Store old values with their indices
        for (idx, expr) in seen.into_iter().enumerate() {
            hir_contract.old_values.push((idx, expr));
        }

        // Clear contract context
        ctx.contract_ctx = None;

        Ok(hir_contract)
    }
}
