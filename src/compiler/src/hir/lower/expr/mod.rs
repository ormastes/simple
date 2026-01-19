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
            Expr::FString(parts) => self.lower_fstring(parts),
            Expr::I18nString { name, default_text } => self.lower_i18n_string(name, default_text),
            Expr::I18nTemplate { name, parts, args } => self.lower_i18n_template(name, parts, args),
            Expr::I18nRef(name) => self.lower_i18n_ref(name),
            Expr::Identifier(name) => self.lower_identifier(name, ctx),
            Expr::Binary { op, left, right } => self.lower_binary(op, left, right, ctx),
            Expr::Unary { op, operand } => self.lower_unary(op, operand, ctx),
            Expr::Call { callee, args } => self.lower_call(callee, args, ctx),
            Expr::FieldAccess { receiver, field } => self.lower_field_access(receiver, field, ctx),
            Expr::Index { receiver, index } => self.lower_index(receiver, index, ctx),
            Expr::Tuple(exprs) => self.lower_tuple(exprs, ctx),
            Expr::Array(exprs) => self.lower_array(exprs, ctx),
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
            _ => Err(LowerError::Unsupported(format!("{:?}", expr))),
        }
    }

    // ============================================================================
    // Identifier expressions
    // ============================================================================

    fn lower_identifier(&self, name: &str, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
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
                // We're in a class method but self is not in scope = static method
                return Err(LowerError::SelfInStatic);
            }
            Err(LowerError::UnknownVariable(name.to_string()))
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
            else if self.module.types.lookup(recv_name).is_some() {
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

        // For now, regular method calls are unsupported in native compilation
        Err(LowerError::Unsupported(format!(
            "Method call {:?}.{}() not supported in native compilation",
            receiver, method
        )))
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
}
