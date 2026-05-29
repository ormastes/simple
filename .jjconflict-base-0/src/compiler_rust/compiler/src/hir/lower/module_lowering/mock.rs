use simple_parser as ast;

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{HirMockExpectation, LocalVar};

fn type_name_hint(ty: &ast::Type) -> Option<String> {
    match ty {
        ast::Type::Simple(name) => Some(name.clone()),
        ast::Type::Generic { name, .. } => Some(name.clone()),
        ast::Type::Capability { inner, .. } => type_name_hint(inner),
        _ => None,
    }
}

impl Lowerer {
    pub(super) fn lower_mock_expectation(&mut self, exp: &ast::MockExpectation) -> LowerResult<HirMockExpectation> {
        // Lower parameters
        let mut params = Vec::new();
        for param in &exp.params {
            let ty = if let Some(t) = &param.ty {
                self.resolve_type(t)?
            } else {
                return Err(LowerError::MissingParameterType(param.name.clone()));
            };
            params.push(LocalVar {
                name: param.name.clone(),
                ty,
                type_name_hint: param.ty.as_ref().and_then(type_name_hint),
                mutability: param.mutability,
                inject: param.inject,
                is_ghost: false,
            });
        }

        // Lower return type
        let return_type = self.resolve_type_opt(&exp.return_type)?;

        // Lower body statements
        let mut ctx = FunctionContext::new(return_type);
        for param in &params {
            ctx.add_local(param.name.clone(), param.ty, param.mutability);
        }
        // Create a Block from the body statements
        let block = ast::Block {
            span: exp.span,
            statements: exp.body.clone(),
        };
        let body = self.lower_block(&block, &mut ctx)?;

        Ok(HirMockExpectation {
            method_name: exp.method_name.clone(),
            params,
            return_type,
            body,
        })
    }
}
