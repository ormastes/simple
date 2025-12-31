//! Function call expression lowering
//!
//! This module contains expression lowering logic for function calls,
//! including special builtins (async, I/O, math/conversion) and spawn.

use simple_parser::{self as ast, Expr};

use crate::value::BUILTIN_SPAWN;
use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower a function call expression to HIR
    ///
    /// Handles:
    /// - Async/generator builtins (generator, future, await)
    /// - I/O builtins (print, println, eprint, eprintln)
    /// - Math/conversion builtins (abs, min, max, sqrt, etc.)
    /// - Actor spawn
    /// - Regular function calls
    ///
    /// Also enforces purity constraints in contract expressions.
    pub(super) fn lower_call(
        &mut self,
        callee: &Expr,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Check for special builtins: generator, future, spawn, await, print, etc.
        if let Expr::Identifier(name) = callee {
            // Handle special async/generator builtins
            if let Some(result) = self.lower_async_builtin(name, args, ctx)? {
                return Ok(result);
            }

            // Handle I/O builtins
            if let Some(result) = self.lower_io_builtin(name, args, ctx)? {
                return Ok(result);
            }

            // Handle math/conversion builtins
            if let Some(result) = self.lower_utility_builtin(name, args, ctx)? {
                return Ok(result);
            }

            // Check for spawn
            if name == BUILTIN_SPAWN && args.len() == 1 {
                let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                return Ok(HirExpr {
                    kind: HirExprKind::ActorSpawn { body: body_hir },
                    ty: TypeId::I64,
                });
            }

            // CTR-030-032: Check for impure function calls in contract expressions
            if ctx.contract_ctx.is_some() {
                self.check_contract_purity(name)?;
            }
        }

        // Regular function call
        let func_hir = Box::new(self.lower_expr(callee, ctx)?);
        let mut args_hir = Vec::new();
        for arg in args {
            args_hir.push(self.lower_expr(&arg.value, ctx)?);
        }

        // Return type comes from function type
        let ret_ty = func_hir.ty; // Simplified - would need function type lookup

        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: func_hir,
                args: args_hir,
            },
            ty: ret_ty,
        })
    }

    /// Handle async/generator builtins: generator, future, await
    ///
    /// Returns Some(HirExpr) if the name matches a builtin, None otherwise.
    fn lower_async_builtin(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        match name {
            "generator" => {
                if args.len() != 1 {
                    return Err(LowerError::Unsupported(
                        "generator expects exactly one argument (a lambda)".to_string(),
                    ));
                }
                let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                Ok(Some(HirExpr {
                    kind: HirExprKind::GeneratorCreate { body: body_hir },
                    ty: TypeId::I64,
                }))
            }
            "future" => {
                if args.len() != 1 {
                    return Err(LowerError::Unsupported(
                        "future expects exactly one argument".to_string(),
                    ));
                }
                let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                Ok(Some(HirExpr {
                    kind: HirExprKind::FutureCreate { body: body_hir },
                    ty: TypeId::I64,
                }))
            }
            "await" => {
                if args.len() != 1 {
                    return Err(LowerError::Unsupported(
                        "await expects exactly one argument".to_string(),
                    ));
                }
                let future_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                Ok(Some(HirExpr {
                    kind: HirExprKind::Await(future_hir),
                    ty: TypeId::I64,
                }))
            }
            _ => Ok(None),
        }
    }

    /// Handle I/O builtins: print, println, eprint, eprintln
    ///
    /// Returns Some(HirExpr) if the name matches a builtin, None otherwise.
    fn lower_io_builtin(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        if matches!(name, "print" | "println" | "eprint" | "eprintln") {
            Ok(Some(self.lower_builtin_call(name, args, TypeId::NIL, ctx)?))
        } else {
            Ok(None)
        }
    }

    /// Handle math/conversion builtins
    ///
    /// Includes: abs, min, max, sqrt, floor, ceil, pow, to_string, to_int
    /// Returns Some(HirExpr) if the name matches a builtin, None otherwise.
    fn lower_utility_builtin(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        match name {
            "abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow" => {
                Ok(Some(self.lower_builtin_call(name, args, TypeId::I64, ctx)?))
            }
            "to_string" => {
                Ok(Some(self.lower_builtin_call(name, args, TypeId::STRING, ctx)?))
            }
            "to_int" => {
                Ok(Some(self.lower_builtin_call(name, args, TypeId::I64, ctx)?))
            }
            _ => Ok(None),
        }
    }

    /// Check if a function can be called in contract expressions
    ///
    /// Contract expressions (in:, out:, invariant:) must only call pure functions.
    /// Some functions are implicitly pure (math builtins, accessors, converters).
    /// Other functions must be explicitly marked as pure.
    fn check_contract_purity(&self, name: &str) -> LowerResult<()> {
        let is_implicitly_pure = matches!(name,
            "abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow" |
            "len" | "is_empty" | "contains" | "to_string" | "to_int"
        );
        if !is_implicitly_pure && !self.is_pure_function(name) {
            return Err(LowerError::ImpureFunctionInContract {
                func_name: name.to_string(),
            });
        }
        Ok(())
    }
}
