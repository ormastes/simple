//! Collection literal expression lowering
//!
//! This module contains expression lowering logic for collection literals:
//! tuples, arrays, vector literals, and struct initialization.

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
                return Err(LowerError::UnknownType(
                    "Self used outside of class/struct context".to_string()
                ));
            }
        } else {
            self.module
                .types
                .lookup(name)
                .ok_or_else(|| LowerError::UnknownType(name.to_string()))?
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
}
