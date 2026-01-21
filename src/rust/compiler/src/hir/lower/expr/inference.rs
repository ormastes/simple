use simple_parser::{self as ast, Expr};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    pub(in crate::hir::lower) fn infer_type(&mut self, expr: &Expr, ctx: &FunctionContext) -> LowerResult<TypeId> {
        match expr {
            Expr::Integer(_) => Ok(TypeId::I64),
            Expr::Float(_) => Ok(TypeId::F64),
            Expr::String(_) => Ok(TypeId::STRING),
            Expr::Bool(_) => Ok(TypeId::BOOL),
            Expr::Nil => Ok(TypeId::NIL),
            Expr::Identifier(name) => {
                if let Some(idx) = ctx.lookup(name) {
                    Ok(ctx.locals[idx].ty)
                } else if let Some(ty) = self.globals.get(name) {
                    Ok(*ty)
                } else {
                    Err(LowerError::UnknownVariable(name.clone()))
                }
            }
            Expr::Binary { op, left, .. } => match op {
                ast::BinOp::Eq
                | ast::BinOp::NotEq
                | ast::BinOp::Lt
                | ast::BinOp::Gt
                | ast::BinOp::LtEq
                | ast::BinOp::GtEq => {
                    // For SIMD vectors, comparison returns a SIMD bool vector
                    let left_ty = self.infer_type(left, ctx)?;
                    if let Some(HirType::Simd { lanes, .. }) = self.module.types.get(left_ty) {
                        let lanes = *lanes;
                        Ok(self.module.types.register(HirType::Simd {
                            lanes,
                            element: TypeId::BOOL,
                        }))
                    } else {
                        Ok(TypeId::BOOL)
                    }
                }
                ast::BinOp::And | ast::BinOp::Or => Ok(TypeId::BOOL),
                _ => self.infer_type(left, ctx),
            },
            Expr::Unary { op, operand } => match op {
                ast::UnaryOp::Not => Ok(TypeId::BOOL),
                _ => self.infer_type(operand, ctx),
            },
            Expr::Call { callee, .. } => {
                // Return type of call is the type of the callee (function)
                self.infer_type(callee, ctx)
            }
            Expr::If { then_branch, .. } => {
                // Type of if-expression is the type of the then branch
                self.infer_type(then_branch, ctx)
            }
            Expr::Tuple(exprs) => {
                // Infer tuple type from elements
                if exprs.is_empty() {
                    Ok(TypeId::VOID)
                } else {
                    // Recursively infer element types
                    let mut types = Vec::new();
                    for e in exprs {
                        types.push(self.infer_type(e, ctx)?);
                    }
                    Ok(self.module.types.register(HirType::Tuple(types)))
                }
            }
            Expr::Array(exprs) => {
                if let Some(first) = exprs.first() {
                    // Infer array type from first element
                    let elem_ty = self.infer_type(first, ctx)?;
                    Ok(self.module.types.register(HirType::Array {
                        element: elem_ty,
                        size: Some(exprs.len()),
                    }))
                } else {
                    Ok(TypeId::VOID)
                }
            }
            Expr::VecLiteral(exprs) => {
                if let Some(first) = exprs.first() {
                    // Infer SIMD vector type from first element
                    let elem_ty = self.infer_type(first, ctx)?;
                    Ok(self.module.types.register(HirType::Simd {
                        lanes: exprs.len() as u32,
                        element: elem_ty,
                    }))
                } else {
                    Ok(TypeId::VOID)
                }
            }
            Expr::Index { receiver, .. } => {
                // Infer element type from array type
                let arr_ty = self.infer_type(receiver, ctx)?;
                self.get_index_element_type(arr_ty)
            }
            Expr::FieldAccess { receiver, field } => {
                // Handle thread_group.id and thread_group.size
                if let Expr::Identifier(recv_name) = receiver.as_ref() {
                    if recv_name == "thread_group" {
                        match field.as_str() {
                            "id" | "size" => return Ok(TypeId::I64),
                            _ => {}
                        }
                    }
                }
                // Infer field type from struct type
                let struct_ty = self.infer_type(receiver, ctx)?;
                let (_idx, field_ty) = self.get_field_info(struct_ty, field)?;
                Ok(field_ty)
            }
            Expr::MethodCall { receiver, method, .. } => {
                // Handle SIMD intrinsics: this.index(), this.thread_index(), this.group_index()
                // and thread_group.barrier(), gpu.* functions
                if let Expr::Identifier(recv_name) = receiver.as_ref() {
                    if recv_name == "this" {
                        match method.as_str() {
                            "index" | "thread_index" | "group_index" => return Ok(TypeId::I64),
                            _ => {}
                        }
                    } else if recv_name == "thread_group" {
                        match method.as_str() {
                            "barrier" => return Ok(TypeId::VOID),
                            _ => {}
                        }
                    } else if recv_name == "gpu" {
                        // gpu.* intrinsic functions
                        match method.as_str() {
                            // Size/index queries return i64
                            "global_id" | "local_id" | "group_id" | "global_size" | "local_size" | "num_groups" => {
                                return Ok(TypeId::I64);
                            }
                            // Synchronization returns void
                            "barrier" | "mem_fence" => return Ok(TypeId::VOID),
                            // Atomic operations return old value (i64)
                            "atomic_add"
                            | "atomic_sub"
                            | "atomic_min"
                            | "atomic_max"
                            | "atomic_and"
                            | "atomic_or"
                            | "atomic_xor"
                            | "atomic_exchange"
                            | "atomic_compare_exchange" => return Ok(TypeId::I64),
                            _ => {}
                        }
                    } else if recv_name == "f32x4"
                        || recv_name == "f64x4"
                        || recv_name == "i32x4"
                        || recv_name == "i64x4"
                    {
                        // SIMD type static methods: f32x4.load(), f32x4.gather()
                        match method.as_str() {
                            "load" | "gather" | "load_masked" => {
                                let simd_ty = self.register_simd_type(&recv_name);
                                return Ok(simd_ty);
                            }
                            _ => {}
                        }
                    }
                }
                // Check for SIMD vector reduction methods
                let recv_ty = self.infer_type(receiver, ctx)?;
                if let Some(HirType::Simd { element, .. }) = self.module.types.get(recv_ty) {
                    let element = *element;
                    match method.as_str() {
                        // Arithmetic reductions return element type
                        "sum" | "product" | "min" | "max" => return Ok(element),
                        // Boolean reductions return bool
                        "all" | "any" => return Ok(TypeId::BOOL),
                        _ => {}
                    }
                }
                // Cannot infer type for other method calls
                Err(LowerError::CannotInferTypeFor(format!("{:?}", expr)))
            }
            // Cannot infer type for complex expressions - require annotation
            _ => Err(LowerError::CannotInferTypeFor(format!("{:?}", expr))),
        }
    }
}
