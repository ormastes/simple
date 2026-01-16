//! Control flow expression lowering
//!
//! This module contains expression lowering logic for control flow:
//! if expressions, lambda expressions, and yield expressions.

use simple_parser::{self as ast, Expr};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::LowerResult;
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower an if expression to HIR
    ///
    /// Result type is taken from the then branch.
    /// Else branch is optional.
    pub(super) fn lower_if(
        &mut self,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let cond_hir = Box::new(self.lower_expr(condition, ctx)?);
        let then_hir = Box::new(self.lower_expr(then_branch, ctx)?);
        let else_hir = if let Some(eb) = else_branch {
            Some(Box::new(self.lower_expr(eb, ctx)?))
        } else {
            None
        };

        let ty = then_hir.ty;

        Ok(HirExpr {
            kind: HirExprKind::If {
                condition: cond_hir,
                then_branch: then_hir,
                else_branch: else_hir,
            },
            ty,
        })
    }

    /// Lower a lambda expression to HIR
    ///
    /// Captures all variables from the outer scope.
    /// Parameters default to I64 type if not explicitly typed.
    /// Result type is taken from the lambda body.
    pub(super) fn lower_lambda(
        &mut self,
        params: &[ast::LambdaParam],
        body: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Track captured variables from outer scope
        let captures: Vec<usize> = ctx.locals.iter().enumerate().map(|(i, _)| i).collect();

        // Collect parameter names and types
        let param_info: Vec<(String, TypeId)> = params
            .iter()
            .map(|p| (p.name.clone(), TypeId::I64)) // Default to I64 for untyped params
            .collect();

        // Lower the lambda body
        let body_hir = Box::new(self.lower_expr(body, ctx)?);
        let body_ty = body_hir.ty;

        Ok(HirExpr {
            kind: HirExprKind::Lambda {
                params: param_info,
                body: body_hir,
                captures,
            },
            ty: body_ty,
        })
    }

    /// Lower a yield expression to HIR
    ///
    /// Used in generator functions.
    /// If no value is provided, yields Nil.
    pub(super) fn lower_yield(&mut self, value: Option<&Expr>, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let value_hir = if let Some(v) = value {
            Box::new(self.lower_expr(v, ctx)?)
        } else {
            Box::new(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            })
        };
        let ty = value_hir.ty;
        Ok(HirExpr {
            kind: HirExprKind::Yield(value_hir),
            ty,
        })
    }

    /// Lower a spawn expression to HIR
    ///
    /// `spawn expr` lowers to ActorSpawn
    pub(super) fn lower_spawn(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let body_hir = Box::new(self.lower_expr(expr, ctx)?);
        Ok(HirExpr {
            kind: HirExprKind::ActorSpawn { body: body_hir },
            ty: TypeId::I64, // Returns thread handle
        })
    }

    /// Lower a go expression to HIR
    ///
    /// `go(args) \params: body` or `go |captures| \: body`
    /// Both forms lower to spawn_isolated with a lambda
    pub(super) fn lower_go(
        &mut self,
        args: &[Expr],
        params: &[String],
        is_capture_form: bool,
        body: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // For go expressions, we create a lambda and spawn it
        // go(x, y) \a, b: expr  =>  spawn_isolated(\a, b: expr)(x, y)
        // go |x, y| \: expr     =>  spawn_isolated(\: expr using captured x, y)

        if is_capture_form {
            // Capture form: go |x, y| \: body
            // The args are identifiers that should be captured
            // We create a lambda with no parameters that uses the captures
            let lambda_params: Vec<ast::LambdaParam> = Vec::new();
            let lambda_hir = self.lower_lambda(&lambda_params, body, ctx)?;

            // Spawn the lambda
            Ok(HirExpr {
                kind: HirExprKind::ActorSpawn {
                    body: Box::new(lambda_hir),
                },
                ty: TypeId::I64, // Returns thread handle
            })
        } else {
            // Args form: go(x, y) \a, b: body
            // Create a lambda with the parameters
            let lambda_params: Vec<ast::LambdaParam> = params
                .iter()
                .map(|name| ast::LambdaParam {
                    name: name.clone(),
                    ty: None,
                })
                .collect();

            let lambda_hir = self.lower_lambda(&lambda_params, body, ctx)?;

            // Lower the arguments
            let mut arg_hirs = Vec::new();
            for arg in args {
                arg_hirs.push(self.lower_expr(arg, ctx)?);
            }

            // Create a call to the lambda with the arguments
            // This is effectively: (lambda)(args...)
            let call_hir = HirExpr {
                kind: HirExprKind::Call {
                    func: Box::new(lambda_hir),
                    args: arg_hirs,
                },
                ty: TypeId::I64, // The result type of the body
            };

            // Spawn the call
            Ok(HirExpr {
                kind: HirExprKind::ActorSpawn {
                    body: Box::new(call_hir),
                },
                ty: TypeId::I64, // Returns thread handle
            })
        }
    }
}
