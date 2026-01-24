//! Function call expression lowering
//!
//! This module contains expression lowering logic for function calls,
//! including special builtins (async, I/O, math/conversion) and spawn.

use simple_parser::{self as ast, Expr, Span};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::deprecation_warning::DeprecationWarning;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;
use crate::value::{BUILTIN_JOIN, BUILTIN_REPLY, BUILTIN_SPAWN};

impl Lowerer {
    /// Lower a function call expression to HIR
    ///
    /// Handles:
    /// - Class/struct construction: ClassName(args) - Python-style constructors
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
            // Check if this is a class/struct constructor call: ClassName(args)
            // Python-style construction: Service() calls the class constructor
            if let Some(struct_ty) = self.module.types.lookup(name) {
                // Lower arguments as positional field initializers
                let mut fields_hir = Vec::new();
                for arg in args {
                    let field_hir = self.lower_expr(&arg.value, ctx)?;
                    fields_hir.push(field_hir);
                }
                return Ok(HirExpr {
                    kind: HirExprKind::StructInit {
                        ty: struct_ty,
                        fields: fields_hir,
                    },
                    ty: struct_ty,
                });
            }

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

            // Check for join
            if name == BUILTIN_JOIN && args.len() == 1 {
                let actor_hir = self.lower_expr(&args[0].value, ctx)?;
                return Ok(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "join".to_string(),
                        args: vec![actor_hir],
                    },
                    ty: TypeId::I64,
                });
            }

            // Check for reply
            if name == BUILTIN_REPLY && args.len() == 1 {
                let message_hir = self.lower_expr(&args[0].value, ctx)?;
                return Ok(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "reply".to_string(),
                        args: vec![message_hir],
                    },
                    ty: TypeId::NIL,
                });
            }

            // CTR-030-032: Check for impure function calls in contract expressions
            if ctx.contract_ctx.is_some() {
                self.check_contract_purity(name)?;
            }

            // Check for deprecated function usage
            if self.is_deprecated(name) {
                let message = self.deprecation_message(name).map(|s| s.to_string());
                let suggestion = self.find_non_deprecated_function_alternative(name);
                let span = if let Expr::Identifier(_) = callee {
                    // Use a dummy span for now - in a real implementation we'd get the actual span
                    Span::new(0, 0, 1, 1)
                } else {
                    Span::new(0, 0, 1, 1)
                };
                self.deprecation_warnings.add(DeprecationWarning::function(
                    span,
                    name.clone(),
                    message,
                    suggestion,
                ));
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

    /// Handle I/O builtins: print, print_raw, eprint, eprint_raw, dprint
    ///
    /// Note: println and eprintln are deprecated (show runtime errors)
    /// Returns Some(HirExpr) if the name matches a builtin, None otherwise.
    fn lower_io_builtin(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        if matches!(
            name,
            "print" | "print_raw" | "eprint" | "eprint_raw" | "dprint" | "println" | "eprintln"
        ) {
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
            "to_string" => Ok(Some(self.lower_builtin_call(name, args, TypeId::STRING, ctx)?)),
            "to_int" => Ok(Some(self.lower_builtin_call(name, args, TypeId::I64, ctx)?)),
            _ => Ok(None),
        }
    }

    /// Check if a function can be called in contract expressions
    ///
    /// Contract expressions (in:, out:, invariant:) must only call pure functions.
    /// Some functions are implicitly pure (math builtins, accessors, converters).
    /// Other functions must be explicitly marked as pure.
    fn check_contract_purity(&self, name: &str) -> LowerResult<()> {
        let is_implicitly_pure = matches!(
            name,
            "abs"
                | "min"
                | "max"
                | "sqrt"
                | "floor"
                | "ceil"
                | "pow"
                | "len"
                | "is_empty"
                | "contains"
                | "to_string"
                | "to_int"
        );
        if !is_implicitly_pure && !self.is_pure_function(name) {
            return Err(LowerError::ImpureFunctionInContract {
                func_name: name.to_string(),
            });
        }
        Ok(())
    }
}
