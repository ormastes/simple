use simple_parser as ast;

use crate::hir::lower::context::{ContractLoweringContext, FunctionContext};
use crate::hir::lower::error::LowerResult;
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{HirContract, HirContractClause};

impl Lowerer {
    pub(super) fn lower_contract(&mut self, contract: &ast::ContractBlock, ctx: &mut FunctionContext) -> LowerResult<HirContract> {
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
