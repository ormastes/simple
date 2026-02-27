mod access;
mod calls;
mod collections;
mod contracts;
mod control;
mod helpers;
mod inference;
mod literals;
mod memory;
mod operators;
mod simd;
mod tensor;

use simple_parser::{self as ast, ast::ReferenceCapability, Expr};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;
use crate::value::BUILTIN_SPAWN;

impl Lowerer {
    /// Main expression lowering dispatcher
    ///
    /// This method delegates to specialized helper methods for each expression type,
    /// keeping the dispatch logic clean and maintainable.
    pub(in crate::hir::lower) fn lower_expr(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        match expr {
            Expr::Integer(_) | Expr::Float(_) | Expr::String(_) | Expr::Bool(_) | Expr::Nil => self.lower_literal(expr),
            Expr::FString { parts, type_meta } => self.lower_fstring(parts, type_meta, ctx),
            Expr::I18nString { name, default_text } => self.lower_i18n_string(name, default_text),
            Expr::I18nTemplate { name, parts, args } => self.lower_i18n_template(name, parts, args),
            Expr::I18nRef(name) => self.lower_i18n_ref(name),
            Expr::Identifier(name) => self.lower_identifier(name, ctx),
            Expr::Binary { op, left, right } => self.lower_binary(op, left, right, ctx),
            Expr::Unary { op, operand } => self.lower_unary(op, operand, ctx),
            Expr::Call { callee, args } => self.lower_call(callee, args, ctx),
            Expr::FieldAccess { receiver, field } => self.lower_field_access(receiver, field, ctx),
            Expr::Index { receiver, index } => self.lower_index(receiver, index, ctx),
            Expr::Slice {
                receiver,
                start,
                end,
                step,
            } => self.lower_slice(receiver, start.as_deref(), end.as_deref(), step.as_deref(), ctx),
            Expr::Tuple(exprs) => self.lower_tuple(exprs, ctx),
            Expr::Array(exprs) => self.lower_array(exprs, ctx),
            Expr::Dict(pairs) => self.lower_dict(pairs, ctx),
            Expr::ArrayRepeat { value, count } => self.lower_array_repeat(value, count, ctx),
            Expr::VecLiteral(exprs) => self.lower_vec_literal(exprs, ctx),
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => self.lower_if(condition, then_branch, else_branch.as_deref(), ctx),
            Expr::Lambda {
                params,
                body,
                capture_all,
                ..
            } => self.lower_lambda(params, body, *capture_all, ctx),
            Expr::Yield(value) => self.lower_yield(value.as_deref(), ctx),
            Expr::ContractResult => self.lower_contract_result(ctx),
            Expr::ContractOld(inner) => self.lower_contract_old(inner, ctx),
            Expr::New { kind, expr } => self.lower_new(kind, expr, ctx),
            Expr::MethodCall { receiver, method, args } => self.lower_method_call(receiver, method, args, ctx),
            Expr::StructInit { name, fields } => self.lower_struct_init(name, fields, ctx),
            // Simple Math: Grid and Tensor literals (#1920-#1929)
            Expr::GridLiteral { rows, device } => self.lower_grid_literal(rows, device, ctx),
            Expr::TensorLiteral {
                dtype,
                dims,
                mode,
                device,
            } => self.lower_tensor_literal(dtype, dims, mode, device, ctx),
            // Type cast expression: expr as Type
            Expr::Cast { expr, target_type } => self.lower_cast(expr, target_type, ctx),
            // Spawn expression: spawn expr
            Expr::Spawn(expr) => self.lower_spawn(expr, ctx),
            // Go expression: go(...) \params: or go \*:
            Expr::Go { args, params, body } => self.lower_go(args, params, body, ctx),
            // Path expression: Type.method - provide helpful error for .new()
            Expr::Path(segments) => self.lower_path(segments, ctx),
            // Match expression: match subject: case pattern: body
            Expr::Match { subject, arms } => self.lower_match(subject, arms, ctx),
            // Do block: do: statements... (block as expression)
            Expr::DoBlock(statements) => self.lower_do_block(statements, ctx),
            // Null coalescing: expr ?? default
            Expr::Coalesce { expr, default } => self.lower_coalesce(expr, default, ctx),
            // Existence check: expr.? (is present/non-empty)
            Expr::ExistsCheck(inner) => self.lower_exists_check(inner, ctx),
            // Await expression: await expr
            Expr::Await(inner) => {
                let future_hir = Box::new(self.lower_expr(inner, ctx)?);
                Ok(HirExpr {
                    kind: HirExprKind::Await(future_hir),
                    ty: TypeId::I64,
                })
            }
            // Try expression: expr? - unwrap Result or propagate error
            Expr::Try(inner) => self.lower_try(inner, ctx),
            // Range expression: start..end or start..=end
            Expr::Range { start, end, bound } => self.lower_range(start.as_deref(), end.as_deref(), *bound, ctx),
            _ => {
                if self.lenient_types {
                    Ok(HirExpr {
                        kind: HirExprKind::Nil,
                        ty: TypeId::ANY,
                    })
                } else {
                    Err(LowerError::Unsupported(format!("{:?}", expr)))
                }
            }
        }
    }

    // ============================================================================
    // Identifier expressions
    // ============================================================================

    fn lower_identifier(&self, name: &str, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        // Handle "None" as alias for nil (Python compatibility)
        if name == "None" {
            return Ok(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            });
        }

        // Check if this is a contract binding (ret, err, result in postconditions)
        if ctx.is_postcondition_binding(name) {
            return Ok(HirExpr {
                kind: HirExprKind::ContractResult,
                ty: ctx.return_type,
            });
        }
        if ctx.is_error_binding(name) {
            // Error binding also refers to the return value (the error part)
            return Ok(HirExpr {
                kind: HirExprKind::ContractResult,
                ty: ctx.return_type,
            });
        }

        // Handle FFI calls: @rt_function_name
        // The parser creates identifiers with @ prefix for FFI calls
        // Look up the extern function without the @ prefix
        if let Some(stripped_name) = name.strip_prefix('@') {
            if let Some(ty) = self.globals.get(stripped_name).copied() {
                // Found extern function - return as global reference
                // The @ prefix is preserved in the name for debugging/tooling
                return Ok(HirExpr {
                    kind: HirExprKind::Global(name.to_string()),
                    ty,
                });
            } else if self.lenient_types {
                return Ok(HirExpr {
                    kind: HirExprKind::Global(name.to_string()),
                    ty: TypeId::ANY,
                });
            } else {
                return Err(LowerError::UnknownVariable(format!(
                    "{} (FFI call to undefined extern function '{}')",
                    name, stripped_name
                )));
            }
        }

        if let Some(idx) = ctx.lookup(name) {
            let ty = ctx.locals[idx].ty;
            Ok(HirExpr {
                kind: HirExprKind::Local(idx),
                ty,
            })
        } else if let Some(ty) = self.globals.get(name).copied() {
            Ok(HirExpr {
                kind: HirExprKind::Global(name.to_string()),
                ty,
            })
        } else {
            // E1032 - Self in Static: Special case for 'self' not found
            if name == "self" && self.current_class_type.is_some() {
                if self.lenient_types {
                    // In lenient mode, treat self as a global with the class type
                    return Ok(HirExpr {
                        kind: HirExprKind::Global("self".to_string()),
                        ty: self.current_class_type.unwrap_or(TypeId::ANY),
                    });
                }
                // We're in a class method but self is not in scope = static method
                return Err(LowerError::SelfInStatic);
            }
            if self.lenient_types {
                // In lenient mode, treat unknown variables as globals with type ANY
                Ok(HirExpr {
                    kind: HirExprKind::Global(name.to_string()),
                    ty: TypeId::ANY,
                })
            } else {
                Err(LowerError::UnknownVariable(name.to_string()))
            }
        }
    }

    // ============================================================================
    // Method calls (largest section - GPU/SIMD intrinsics)
    // ============================================================================

    fn lower_method_call(
        &mut self,
        receiver: &Expr,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Check for intrinsic calls on special identifiers
        if let Expr::Identifier(recv_name) = receiver {
            // this.* intrinsics
            if recv_name == "this" {
                if let Some(result) = self.lower_this_method(method, args)? {
                    return Ok(result);
                }
            }
            // thread_group.* intrinsics
            else if recv_name == "thread_group" {
                if let Some(result) = self.lower_thread_group_method(method, args)? {
                    return Ok(result);
                }
            }
            // gpu.* intrinsics
            else if recv_name == "gpu" {
                if let Some(result) = self.lower_gpu_method(method, args, ctx)? {
                    return Ok(result);
                }
            }
            // SIMD type static methods: f32x4.load(), etc.
            else if matches!(recv_name.as_str(), "f32x4" | "f64x4" | "i32x4" | "i64x4") {
                if let Some(result) = self.lower_simd_static_method(recv_name, method, args, ctx)? {
                    return Ok(result);
                }
            }
            // Static method calls on classes/structs
            // Only treat as static method if the name is NOT a local variable
            // (e.g., `text` is both a type alias and could be a variable name)
            else if ctx.lookup(recv_name).is_none() && self.module.types.lookup(recv_name).is_some() {
                return self.lower_static_method_call(recv_name, method, args, ctx);
            }
        }

        // Check for SIMD vector instance methods
        let receiver_hir = self.lower_expr(receiver, ctx)?;
        if let Some(HirType::Simd { .. }) = self.module.types.get(receiver_hir.ty) {
            if let Some(result) = self.lower_simd_instance_method(&receiver_hir, method, args, ctx)? {
                return Ok(result);
            }
        }

        // Check for builtin collection/string methods
        if let Some(result) = self.lower_builtin_method_call(&receiver_hir, method, args, ctx)? {
            return Ok(result);
        }

        // Lower arguments for generic method call
        let mut hir_args = Vec::new();
        for arg in args {
            let expr = self.lower_expr(&arg.value, ctx)?;
            hir_args.push(expr);
        }

        // Look up return type from module functions
        let recv_ty = receiver_hir.ty;
        let return_ty = self.lookup_method_return_type(recv_ty, method);

        // Generate generic method call for user-defined methods
        // Uses dynamic dispatch since we don't know the concrete type at compile time
        Ok(HirExpr {
            kind: HirExprKind::MethodCall {
                receiver: Box::new(receiver_hir),
                method: method.to_string(),
                args: hir_args,
                dispatch: DispatchMode::Dynamic,
            },
            ty: return_ty,
        })
    }

    /// Look up the return type of a method from pre-registered signatures.
    fn lookup_method_return_type(&self, recv_ty: TypeId, method: &str) -> TypeId {
        // If receiver type is known, look up "TypeName.method"
        if recv_ty != TypeId::ANY && recv_ty != TypeId::VOID {
            if let Some(hir_ty) = self.module.types.get(recv_ty) {
                let type_name = match hir_ty {
                    HirType::Struct { name, .. } => Some(name.as_str()),
                    HirType::Enum { name, .. } => Some(name.as_str()),
                    _ => None,
                };
                if let Some(name) = type_name {
                    let qualified = format!("{}.{}", name, method);
                    if let Some(&ret_ty) = self.method_return_types.get(&qualified) {
                        return ret_ty;
                    }
                }
            }
        }
        // Search pre-registered methods for ".method" suffix
        let suffix = format!(".{}", method);
        for (name, &ret_ty) in &self.method_return_types {
            if name.ends_with(&suffix) {
                return ret_ty;
            }
        }
        TypeId::ANY
    }

    /// Handle this.index(), this.thread_index(), this.group_index()
    fn lower_this_method(&self, method: &str, args: &[ast::Argument]) -> LowerResult<Option<HirExpr>> {
        if !args.is_empty() {
            return Err(LowerError::Unsupported(format!("this.{}() takes no arguments", method)));
        }

        let intrinsic = match method {
            "index" => GpuIntrinsicKind::SimdIndex,
            "thread_index" => GpuIntrinsicKind::SimdThreadIndex,
            "group_index" => GpuIntrinsicKind::SimdGroupIndex,
            _ => return Ok(None),
        };

        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic,
                args: vec![],
            },
            ty: TypeId::I64,
        }))
    }

    /// Handle thread_group.barrier()
    fn lower_thread_group_method(&self, method: &str, args: &[ast::Argument]) -> LowerResult<Option<HirExpr>> {
        if method != "barrier" {
            return Err(LowerError::Unsupported(format!(
                "unknown thread_group method: {}",
                method
            )));
        }

        if !args.is_empty() {
            return Err(LowerError::Unsupported(
                "thread_group.barrier() takes no arguments".to_string(),
            ));
        }

        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic: GpuIntrinsicKind::Barrier,
                args: vec![],
            },
            ty: TypeId::VOID,
        }))
    }

    /// Handle builtin method calls on strings, arrays
    fn lower_builtin_method_call(
        &mut self,
        receiver: &HirExpr,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        // Get receiver type to determine which builtin methods are available
        let is_string = matches!(self.module.types.get(receiver.ty), Some(HirType::String));
        let is_array = matches!(self.module.types.get(receiver.ty), Some(HirType::Array { .. }));

        // Lower arguments
        let mut hir_args = Vec::new();
        for arg in args {
            let expr = self.lower_expr(&arg.value, ctx)?;
            hir_args.push(expr);
        }

        // String methods
        if is_string {
            let result_ty = match method {
                "len" => Some(TypeId::I64),
                "starts_with" | "ends_with" | "contains" => Some(TypeId::BOOL),
                "concat" => Some(TypeId::STRING),
                "slice" => Some(TypeId::STRING),
                _ => None,
            };

            if let Some(ty) = result_ty {
                return Ok(Some(HirExpr {
                    kind: HirExprKind::MethodCall {
                        receiver: Box::new(receiver.clone()),
                        method: method.to_string(),
                        args: hir_args,
                        dispatch: DispatchMode::Static,
                    },
                    ty,
                }));
            }
        }

        // Array methods
        if is_array {
            let result_ty = match method {
                "len" => Some(TypeId::I64),
                "push" => Some(receiver.ty), // Returns the new array (same type)
                "clear" => Some(TypeId::VOID),
                "pop" => {
                    // pop returns the element type
                    if let Some(HirType::Array { element, .. }) = self.module.types.get(receiver.ty) {
                        Some(*element)
                    } else {
                        Some(TypeId::ANY)
                    }
                }
                "contains" | "is_empty" => Some(TypeId::BOOL),
                "slice" | "filter" | "map" => Some(receiver.ty), // Returns same array type
                "first" | "last" | "get" => {
                    // Returns element type (or Option<element>)
                    if let Some(HirType::Array { element, .. }) = self.module.types.get(receiver.ty) {
                        Some(*element)
                    } else {
                        Some(TypeId::ANY)
                    }
                }
                _ => None,
            };

            if let Some(ty) = result_ty {
                return Ok(Some(HirExpr {
                    kind: HirExprKind::MethodCall {
                        receiver: Box::new(receiver.clone()),
                        method: method.to_string(),
                        args: hir_args,
                        dispatch: DispatchMode::Static,
                    },
                    ty,
                }));
            }
        }

        // Any type (Dict, generic containers) methods
        // These are dynamically typed at runtime
        let is_any =
            matches!(receiver.ty, TypeId::ANY) || matches!(self.module.types.get(receiver.ty), Some(HirType::Any));

        if is_any {
            let result_ty = match method {
                // Dict/Map operations
                "get" | "remove" => Some(TypeId::ANY), // Returns Any (dynamic value)
                "insert" | "set" | "put" | "clear" => Some(TypeId::VOID),
                "contains_key" | "has" | "contains" => Some(TypeId::BOOL),
                "len" | "size" => Some(TypeId::I64),
                "keys" | "values" | "items" | "entries" => Some(TypeId::ANY), // Returns iterator/list
                "is_empty" => Some(TypeId::BOOL),
                // Optional operations (for Option/Result types stored as Any)
                "is_some" | "is_none" | "is_ok" | "is_err" => Some(TypeId::BOOL),
                "unwrap" | "unwrap_or" | "expect" => Some(TypeId::ANY),
                "map" | "and_then" | "or_else" => Some(TypeId::ANY),
                // Type conversion
                "to_string" | "to_text" => Some(TypeId::STRING),
                "to_int" | "to_i64" => Some(TypeId::I64),
                "to_float" | "to_f64" => Some(TypeId::F64),
                "to_bool" => Some(TypeId::BOOL),
                _ => None,
            };

            if let Some(ty) = result_ty {
                return Ok(Some(HirExpr {
                    kind: HirExprKind::MethodCall {
                        receiver: Box::new(receiver.clone()),
                        method: method.to_string(),
                        args: hir_args,
                        dispatch: DispatchMode::Dynamic, // Dynamic dispatch for Any types
                    },
                    ty,
                }));
            }
        }

        Ok(None)
    }

    // ============================================================================
    // Path expressions (Type.method)
    // ============================================================================

    /// Lower a path expression like Type.method
    ///
    /// Provides helpful error messages for common mistakes:
    /// - `ClassName.new()` should be `ClassName()` (Python-style constructor)
    /// - Other static methods are not yet supported in native compilation
    fn lower_path(&self, segments: &[String], _ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        if segments.len() == 2 {
            let class_name = &segments[0];
            let method_name = &segments[1];

            // Special case: ClassName.new() should be ClassName()
            if method_name == "new" {
                if self.lenient_types {
                    return Ok(HirExpr {
                        kind: HirExprKind::Global(format!("{}.{}", class_name, method_name)),
                        ty: TypeId::ANY,
                    });
                }
                return Err(LowerError::UseConstructorNotNew {
                    class_name: class_name.clone(),
                });
            }

            // Static method reference — produce Global("ClassName.method")
            {
                let qualified = format!("{}.{}", class_name, method_name);
                let ty = self.method_return_types
                    .get(&qualified)
                    .copied()
                    .unwrap_or(TypeId::ANY);
                return Ok(HirExpr {
                    kind: HirExprKind::Global(qualified),
                    ty,
                });
            }
        }

        if self.lenient_types {
            return Ok(HirExpr {
                kind: HirExprKind::Global(segments.join(".")),
                ty: TypeId::ANY,
            });
        }

        // Generic path expression not supported
        Err(LowerError::Unsupported(format!("Path expression {:?}", segments)))
    }
}
