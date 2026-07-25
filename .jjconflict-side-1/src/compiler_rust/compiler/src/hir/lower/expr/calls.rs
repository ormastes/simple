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
            if let Some((type_name, "new")) = name.rsplit_once('.') {
                if let Some(type_id) = self.module.types.lookup(type_name) {
                    if matches!(self.module.types.get(type_id), Some(HirType::Bitfield { .. })) {
                        return self.lower_bitfield_constructor(type_id, args, ctx);
                    }
                }
            }

            if let Some((type_name, member)) = name.split_once("::").or_else(|| name.split_once('.')) {
                if let Some(type_id) = self.static_enum_variant_type(type_name, member) {
                    return self.lower_static_enum_variant_call(type_name, member, type_id, args, ctx);
                }
            }

            // Short enum-constructor grammar: Some(x), None(), Ok(x), Err(x).
            // Lower these as regular calls to the bare constructor symbol so MIR
            // can canonicalize them into Option*/Result* instructions.
            match (name.as_str(), args.len()) {
                ("Some", 1) | ("Ok", 1) | ("Err", 1) | ("None", 0) => {
                    let func_hir = Box::new(HirExpr {
                        kind: HirExprKind::Global(name.clone()),
                        ty: TypeId::ANY,
                    });
                    let args_hir = self.lower_call_args(args, ctx)?;
                    return Ok(HirExpr {
                        kind: HirExprKind::Call {
                            func: func_hir,
                            args: args_hir,
                        },
                        ty: TypeId::ANY,
                    });
                }
                _ => {}
            }

            // Check if this is a class/struct constructor call: ClassName(args)
            // Python-style construction: Service() calls the class constructor
            //
            // Primitive type names (str, text, int, bool, ...) are registered
            // in the type registry too, but a call on them is a CAST, not a
            // constructor. Building a StructInit for e.g. `str(5)` produced a
            // bogus one-field struct typed STRING which rt_string_concat
            // rejected (len=-1 → NIL), dropping `"x=" + str(5)` to empty (#66).
            // Skip primitives here so lower_utility_builtin lowers them as Cast.
            let ctor_ty = self.module.types.lookup(name).filter(|ty_id| {
                !matches!(
                    self.module.types.get(*ty_id),
                    Some(
                        HirType::Void
                            | HirType::Bool
                            | HirType::Any
                            | HirType::Char
                            | HirType::Int { .. }
                            | HirType::Float { .. }
                            | HirType::String
                            | HirType::Nil
                    )
                )
            });
            if let Some(struct_ty) = ctor_ty {
                if matches!(self.module.types.get(struct_ty), Some(HirType::Bitfield { .. })) {
                    return self.lower_bitfield_constructor(struct_ty, args, ctx);
                }
                // ROOT FIX (bug simpleos_native_build_field_defaults_and_boxed_trait_dispatch,
                // 2026-07-16): this used to be `lower_call_args`, which
                // "lowers arguments as positional field initializers" —
                // dropping `arg.name` entirely and lowering values in
                // literal-source order regardless of the struct's declared
                // field order. See `lower_struct_init_fields` in
                // collections.rs for the full root-cause writeup; it
                // reorders named args to their declared slot and fills any
                // field the call site omits (relying on a class-level
                // default) with `nil` instead of leaving it unset.
                let provided: Vec<(Option<&str>, &Expr)> =
                    args.iter().map(|a| (a.name.as_deref(), &a.value)).collect();
                let fields_hir = self.lower_struct_init_fields(name, struct_ty, &provided, ctx)?;
                return Ok(HirExpr {
                    kind: HirExprKind::StructInit {
                        ty: struct_ty,
                        fields: fields_hir,
                    },
                    ty: struct_ty,
                });
            } else if self.lenient_types
                && name.starts_with(|c: char| c.is_ascii_uppercase())
                && args.iter().any(|a| a.name.is_some())
            {
                // In lenient mode, uppercase identifier with named arguments is likely
                // a struct construction even if the type isn't in the registry.
                // Use TypeId::ANY since we don't have the actual type info.
                // Struct type is unresolved (ANY) here, so
                // lower_struct_init_fields falls back to source-order lowering
                // (its "unresolvable struct" branch) — same effective
                // behavior as before, just centralized through one helper.
                let provided: Vec<(Option<&str>, &Expr)> =
                    args.iter().map(|a| (a.name.as_deref(), &a.value)).collect();
                let fields_hir = self.lower_struct_init_fields(name, TypeId::ANY, &provided, ctx)?;
                return Ok(HirExpr {
                    kind: HirExprKind::StructInit {
                        ty: TypeId::ANY,
                        fields: fields_hir,
                    },
                    ty: TypeId::ANY,
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

            // GPU intrinsics: gpu_global_id_x, gpu_local_id_x, gpu_syncthreads, etc.
            if let Some(gpu_result) = self.lower_gpu_function_intrinsic(name, args, ctx)? {
                return Ok(gpu_result);
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
                self.deprecation_warnings
                    .add(DeprecationWarning::function(span, name.clone(), message, suggestion));
            }
        }

        // Handle static method calls: ClassName.method(args)
        // This handles Expr::Path with 2 segments like Container.with_profile()
        if let Expr::Path(segments) = callee {
            if segments.len() == 2 {
                if let Some(type_id) = self.module.types.lookup(&segments[0]) {
                    if matches!(self.module.types.get(type_id), Some(HirType::Bitfield { .. })) && segments[1] == "new"
                    {
                        return self.lower_bitfield_constructor(type_id, args, ctx);
                    }
                }
                return self.lower_static_member_call_with_sugar(&segments[0], &segments[1], args, ctx);
            }
        }

        // Regular function call
        let func_hir = Box::new(self.lower_expr(callee, ctx)?);
        let mut args_hir = self.lower_call_args(args, ctx)?;

        // M12 3b: fill omitted trailing arguments from the callee's parameter
        // defaults. Restricted to a directly-named free function called purely
        // positionally, and to constant default exprs (which cannot reference
        // caller-scope locals or sibling parameters); anything else is left
        // unfilled, preserving prior behavior. Method/Path-callee defaults are a
        // separate follow-up.
        if let Expr::Identifier(name) = callee {
            if args.iter().all(|a| a.name.is_none()) {
                let to_fill: Vec<Expr> = match self.fn_param_defaults.get(name) {
                    Some(params) if params.len() > args_hir.len() => {
                        let mut pending = Vec::new();
                        for slot in &params[args_hir.len()..] {
                            match slot {
                                Some(expr) if Self::is_constant_default(expr) => {
                                    pending.push(expr.clone());
                                }
                                // Positional fill must be contiguous: stop at the
                                // first trailing param lacking a constant default.
                                _ => break,
                            }
                        }
                        pending
                    }
                    _ => Vec::new(),
                };
                for default_expr in to_fill {
                    let lowered = self.lower_expr(&default_expr, ctx)?;
                    args_hir.push(lowered);
                }
            }
        }

        // Prefer the declared return type for the named callee when we know it.
        // This keeps local variables initialized from imported/helper calls on a
        // concrete type path instead of degrading to ANY at the next field access.
        let ret_ty = self.call_return_type(callee, func_hir.ty);

        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: func_hir,
                args: args_hir,
            },
            ty: ret_ty,
        })
    }

    /// True for default-value expressions that are self-contained constants —
    /// safe to lower at a call site because they cannot reference caller-scope
    /// locals or sibling parameters. Conservative: anything not provably
    /// constant (identifiers, calls, field access, …) returns false and is left
    /// unfilled rather than risk a silent miscompile.
    fn is_constant_default(expr: &Expr) -> bool {
        match expr {
            Expr::Integer(_)
            | Expr::Float(_)
            | Expr::String(_)
            | Expr::Bool(_)
            | Expr::Nil
            | Expr::Symbol(_)
            | Expr::Atom(_) => true,
            Expr::Unary { operand, .. } => Self::is_constant_default(operand),
            Expr::Binary { left, right, .. } => Self::is_constant_default(left) && Self::is_constant_default(right),
            _ => false,
        }
    }

    pub(super) fn lower_bitfield_constructor(
        &mut self,
        bitfield_ty: TypeId,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        if args.len() != 1 || args[0].name.is_some() {
            return Err(LowerError::Unsupported(
                "bitfield constructors currently accept exactly one positional raw value".to_string(),
            ));
        }

        let value_hir = self.lower_expr(&args[0].value, ctx)?;
        Ok(HirExpr {
            kind: HirExprKind::Cast {
                expr: Box::new(value_hir),
                target: bitfield_ty,
            },
            ty: bitfield_ty,
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
                if args.len() == 1 {
                    let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                    return Ok(Some(HirExpr {
                        kind: HirExprKind::GeneratorCreate { body: body_hir },
                        ty: TypeId::I64,
                    }));
                }
                // 2+ args → not a builtin, fall through to regular call
                Ok(None)
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
    /// Includes: abs, min, max, sqrt, floor, ceil, pow, to_string, to_int,
    /// and cast-style calls: int(x), text(x), bool(x), char(x), i8(x)..u64(x), f32(x), f64(x).
    /// Returns Some(HirExpr) if the name matches a builtin, None otherwise.
    fn lower_utility_builtin(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        if args.len() == 1 {
            let cast_target = match name {
                "i8" => Some(TypeId::I8),
                "i16" => Some(TypeId::I16),
                "i32" => Some(TypeId::I32),
                "i64" | "int" => Some(TypeId::I64),
                "u8" => Some(TypeId::U8),
                "u16" => Some(TypeId::U16),
                "u32" => Some(TypeId::U32),
                "u64" => Some(TypeId::U64),
                "f32" => Some(TypeId::F32),
                "f64" | "float" => Some(TypeId::F64),
                "bool" => Some(TypeId::BOOL),
                "text" | "str" | "String" => Some(TypeId::STRING),
                "char" => Some(TypeId::CHAR),
                _ => None,
            };
            if let Some(target) = cast_target {
                let inner = self.lower_expr(&args[0].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::Cast {
                        expr: Box::new(inner),
                        target,
                    },
                    ty: target,
                }));
            }
        }

        match name {
            "abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow" => {
                Ok(Some(self.lower_builtin_call(name, args, TypeId::I64, ctx)?))
            }
            "to_string" => Ok(Some(self.lower_builtin_call(name, args, TypeId::STRING, ctx)?)),
            "to_int" => Ok(Some(self.lower_builtin_call(name, args, TypeId::I64, ctx)?)),
            // Option/Result constructors (needed for stdlib)
            "Some" | "Ok" => {
                // Wrap value in Some/Ok variant - return ANY since it's a generic wrapper
                Ok(Some(self.lower_builtin_call(name, args, TypeId::ANY, ctx)?))
            }
            "None" | "Err" => {
                // None/Err variants - no argument needed for None
                Ok(Some(self.lower_builtin_call(name, args, TypeId::ANY, ctx)?))
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
                | "old"     // Contract expression: captures value at function entry
                | "result" // Contract expression: accesses return value in postcondition
        );
        if !is_implicitly_pure && !self.is_pure_function(name) {
            return Err(LowerError::ImpureFunctionInContract {
                func_name: name.to_string(),
            });
        }
        Ok(())
    }

    /// Recognize gpu_*_x/y/z function calls as GPU intrinsics.
    fn lower_gpu_function_intrinsic(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        let (kind, dim) = match name {
            "gpu_global_id_x" => (GpuIntrinsicKind::GlobalId, 0u8),
            "gpu_global_id_y" => (GpuIntrinsicKind::GlobalId, 1),
            "gpu_global_id_z" => (GpuIntrinsicKind::GlobalId, 2),
            "gpu_thread_id_x" => (GpuIntrinsicKind::LocalId, 0),
            "gpu_thread_id_y" => (GpuIntrinsicKind::LocalId, 1),
            "gpu_thread_id_z" => (GpuIntrinsicKind::LocalId, 2),
            "gpu_local_id_x" => (GpuIntrinsicKind::LocalId, 0),
            "gpu_local_id_y" => (GpuIntrinsicKind::LocalId, 1),
            "gpu_local_id_z" => (GpuIntrinsicKind::LocalId, 2),
            "gpu_block_id_x" => (GpuIntrinsicKind::GroupId, 0),
            "gpu_block_id_y" => (GpuIntrinsicKind::GroupId, 1),
            "gpu_block_id_z" => (GpuIntrinsicKind::GroupId, 2),
            "gpu_block_dim_x" => (GpuIntrinsicKind::LocalSize, 0),
            "gpu_block_dim_y" => (GpuIntrinsicKind::LocalSize, 1),
            "gpu_block_dim_z" => (GpuIntrinsicKind::LocalSize, 2),
            "gpu_grid_dim_x" => (GpuIntrinsicKind::NumGroups, 0),
            "gpu_grid_dim_y" => (GpuIntrinsicKind::NumGroups, 1),
            "gpu_grid_dim_z" => (GpuIntrinsicKind::NumGroups, 2),
            "gpu_syncthreads" => {
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::Barrier,
                        args: vec![],
                    },
                    ty: TypeId::NIL,
                }));
            }
            // GPU memory load/store intrinsics with arguments
            "gpu_load_f64" => {
                let ptr_arg = self.lower_expr(&args[0].value, ctx)?;
                let index_arg = self.lower_expr(&args[1].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::GpuLoadF64,
                        args: vec![ptr_arg, index_arg],
                    },
                    ty: TypeId::F64,
                }));
            }
            "gpu_store_f64" => {
                let ptr_arg = self.lower_expr(&args[0].value, ctx)?;
                let index_arg = self.lower_expr(&args[1].value, ctx)?;
                let value_arg = self.lower_expr(&args[2].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::GpuStoreF64,
                        args: vec![ptr_arg, index_arg, value_arg],
                    },
                    ty: TypeId::NIL,
                }));
            }
            "gpu_load_i64" => {
                let ptr_arg = self.lower_expr(&args[0].value, ctx)?;
                let index_arg = self.lower_expr(&args[1].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::GpuLoadI64,
                        args: vec![ptr_arg, index_arg],
                    },
                    ty: TypeId::I64,
                }));
            }
            "gpu_store_i64" => {
                let ptr_arg = self.lower_expr(&args[0].value, ctx)?;
                let index_arg = self.lower_expr(&args[1].value, ctx)?;
                let value_arg = self.lower_expr(&args[2].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::GpuStoreI64,
                        args: vec![ptr_arg, index_arg, value_arg],
                    },
                    ty: TypeId::NIL,
                }));
            }
            _ => return Ok(None),
        };

        // Create a constant dimension argument
        let dim_arg = HirExpr {
            kind: HirExprKind::Integer(dim as i64),
            ty: TypeId::I64,
        };
        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic: kind,
                args: vec![dim_arg],
            },
            ty: TypeId::I64,
        }))
    }
}
