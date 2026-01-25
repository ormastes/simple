//! Collection literal expression lowering
//!
//! This module contains expression lowering logic for collection literals:
//! tuples, arrays, vector literals, struct initialization, and slice expressions.

use simple_parser::Expr;

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::LowerResult;
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower a tuple literal to HIR
    ///
    /// Creates a tuple type from the types of all elements.
    pub(super) fn lower_tuple(&mut self, exprs: &[Expr], ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let mut hir_exprs = Vec::new();
        let mut types = Vec::new();
        for e in exprs {
            let hir = self.lower_expr(e, ctx)?;
            types.push(hir.ty);
            hir_exprs.push(hir);
        }

        let tuple_ty = self.module.types.register(HirType::Tuple(types));

        Ok(HirExpr {
            kind: HirExprKind::Tuple(hir_exprs),
            ty: tuple_ty,
        })
    }

    /// Lower an array literal to HIR
    ///
    /// Creates an array type with a fixed size.
    /// Empty arrays default to VOID element type (will fail if used without explicit type annotation).
    pub(super) fn lower_array(&mut self, exprs: &[Expr], ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let mut hir_exprs = Vec::new();
        let elem_ty = if let Some(first) = exprs.first() {
            self.infer_type(first, ctx)?
        } else {
            // Empty array needs explicit type annotation
            // For now, default to VOID to allow empty arrays (will fail later if used)
            TypeId::VOID
        };

        for e in exprs {
            hir_exprs.push(self.lower_expr(e, ctx)?);
        }

        let arr_ty = self.module.types.register(HirType::Array {
            element: elem_ty,
            size: Some(exprs.len()),
        });

        Ok(HirExpr {
            kind: HirExprKind::Array(hir_exprs),
            ty: arr_ty,
        })
    }

    /// Lower an array repeat expression to HIR: [value; count]
    ///
    /// Creates an array by repeating a value `count` times.
    /// The count must be a compile-time constant for static size inference.
    pub(super) fn lower_array_repeat(
        &mut self,
        value: &Expr,
        count: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Infer element type from the value
        let elem_ty = self.infer_type(value, ctx)?;
        let hir_value = self.lower_expr(value, ctx)?;

        // Try to evaluate count as a compile-time constant
        let size = match count {
            Expr::Integer(n) => Some(*n as usize),
            _ => None, // Dynamic size - will be runtime evaluated
        };

        let arr_ty = self.module.types.register(HirType::Array { element: elem_ty, size });

        // Generate array elements by repeating the value
        // For compile-time known sizes, expand to explicit array
        if let Some(n) = size {
            let hir_exprs: Vec<_> = std::iter::repeat(hir_value).take(n).collect();
            Ok(HirExpr {
                kind: HirExprKind::Array(hir_exprs),
                ty: arr_ty,
            })
        } else {
            // For dynamic sizes, lower count and use ArrayRepeat HIR node
            let hir_count = self.lower_expr(count, ctx)?;
            Ok(HirExpr {
                kind: HirExprKind::ArrayRepeat {
                    value: Box::new(hir_value),
                    count: Box::new(hir_count),
                },
                ty: arr_ty,
            })
        }
    }

    /// Lower a vector literal to HIR
    ///
    /// Creates a SIMD vector type with the number of lanes equal to the number of elements.
    /// Empty vectors default to VOID element type (will fail if used without explicit type annotation).
    pub(super) fn lower_vec_literal(&mut self, exprs: &[Expr], ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let mut hir_exprs = Vec::new();
        let elem_ty = if let Some(first) = exprs.first() {
            self.infer_type(first, ctx)?
        } else {
            // Empty vector needs explicit type annotation
            TypeId::VOID
        };

        for e in exprs {
            hir_exprs.push(self.lower_expr(e, ctx)?);
        }

        let vec_ty = self.module.types.register(HirType::Simd {
            lanes: exprs.len() as u32,
            element: elem_ty,
        });

        Ok(HirExpr {
            kind: HirExprKind::VecLiteral(hir_exprs),
            ty: vec_ty,
        })
    }

    /// Lower a struct initialization expression to HIR
    ///
    /// Creates a struct instance with field initializers.
    /// Supports "Self" keyword to refer to the current class/struct type.
    pub(super) fn lower_struct_init(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        use crate::hir::lower::error::LowerError;

        // Resolve struct type (handle "Self" keyword)
        let struct_ty = if name == "Self" {
            if let Some(class_ty) = self.current_class_type {
                class_ty
            } else {
                return Err(LowerError::UnknownType {
                    type_name: "Self".to_string(),
                    available_types: vec![],
                });
            }
        } else {
            self.module.types.lookup(name).ok_or_else(|| LowerError::UnknownType {
                type_name: name.to_string(),
                available_types: self.module.types.all_type_names(),
            })?
        };

        // Lower field initializers (in order)
        let mut fields_hir = Vec::new();
        for (_field_name, field_expr) in fields {
            let field_hir = self.lower_expr(field_expr, ctx)?;
            fields_hir.push(field_hir);
        }

        Ok(HirExpr {
            kind: HirExprKind::StructInit {
                ty: struct_ty,
                fields: fields_hir,
            },
            ty: struct_ty,
        })
    }

    /// Lower a slice expression to HIR: receiver[start:end:step]
    ///
    /// Converts to a call to rt_slice(collection, start, end, step).
    /// Handles defaults:
    /// - start: 0 if None
    /// - end: collection.len() if None (uses a large value as sentinel)
    /// - step: 1 if None
    pub(super) fn lower_slice(
        &mut self,
        receiver: &Expr,
        start: Option<&Expr>,
        end: Option<&Expr>,
        step: Option<&Expr>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Lower the receiver (the collection being sliced)
        let receiver_hir = self.lower_expr(receiver, ctx)?;
        let receiver_ty = receiver_hir.ty;

        // Determine result type (same as input for arrays/strings)
        let result_ty = receiver_ty;

        // Lower start (default: 0)
        let start_hir = if let Some(s) = start {
            self.lower_expr(s, ctx)?
        } else {
            HirExpr {
                kind: HirExprKind::Integer(0),
                ty: TypeId::I64,
            }
        };

        // Lower end (default: large sentinel value, runtime will clamp to len)
        // We use i64::MAX as a sentinel for "to the end"
        let end_hir = if let Some(e) = end {
            self.lower_expr(e, ctx)?
        } else {
            HirExpr {
                kind: HirExprKind::Integer(i64::MAX),
                ty: TypeId::I64,
            }
        };

        // Lower step (default: 1)
        let step_hir = if let Some(s) = step {
            self.lower_expr(s, ctx)?
        } else {
            HirExpr {
                kind: HirExprKind::Integer(1),
                ty: TypeId::I64,
            }
        };

        // Generate a builtin call to rt_slice
        Ok(HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_slice".to_string(),
                args: vec![receiver_hir, start_hir, end_hir, step_hir],
            },
            ty: result_ty,
        })
    }
}
