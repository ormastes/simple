//! Binary and unary operator lowering
//!
//! This module contains expression lowering logic for binary operations
//! (arithmetic, comparison, logical) and unary operations (negation, not, ref, deref).

use simple_parser::{self as ast, ast::ReferenceCapability, Expr};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::LowerResult;
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower a binary operation to HIR
    ///
    /// Handles arithmetic, comparison, logical, and other binary operations.
    /// For SIMD vectors, comparison operations return SIMD bool vectors.
    pub(super) fn lower_binary(
        &mut self,
        op: &ast::BinOp,
        left: &Expr,
        right: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let left_hir = Box::new(self.lower_expr(left, ctx)?);
        let right_hir = Box::new(self.lower_expr(right, ctx)?);

        // Type is determined by operands
        // For SIMD vectors, comparison returns a SIMD bool vector
        let ty = match op {
            ast::BinOp::Eq
            | ast::BinOp::NotEq
            | ast::BinOp::Lt
            | ast::BinOp::Gt
            | ast::BinOp::LtEq
            | ast::BinOp::GtEq => {
                // For SIMD vectors, return a SIMD bool vector
                if let Some(HirType::Simd { lanes, .. }) = self.module.types.get(left_hir.ty) {
                    let lanes = *lanes;
                    self.module.types.register(HirType::Simd {
                        lanes,
                        element: TypeId::BOOL,
                    })
                } else {
                    TypeId::BOOL
                }
            }
            ast::BinOp::And | ast::BinOp::Or | ast::BinOp::Is | ast::BinOp::In => TypeId::BOOL,
            _ => left_hir.ty,
        };

        Ok(HirExpr {
            kind: HirExprKind::Binary {
                op: (*op).into(),
                left: left_hir,
                right: right_hir,
            },
            ty,
        })
    }

    /// Lower a unary operation to HIR
    ///
    /// Handles negation, not, reference, and dereference operations.
    /// References create pointer types with appropriate capabilities.
    pub(super) fn lower_unary(
        &mut self,
        op: &ast::UnaryOp,
        operand: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let operand_hir = Box::new(self.lower_expr(operand, ctx)?);
        let ty = match op {
            ast::UnaryOp::Not => TypeId::BOOL,
            ast::UnaryOp::Ref | ast::UnaryOp::RefMut => {
                let kind = if *op == ast::UnaryOp::RefMut {
                    PointerKind::BorrowMut
                } else {
                    PointerKind::Borrow
                };
                let ptr_type = HirType::Pointer {
                    kind,
                    capability: ReferenceCapability::Shared, // Default capability
                    inner: operand_hir.ty,
                };
                self.module.types.register(ptr_type)
            }
            ast::UnaryOp::Deref => {
                // Look up inner type from pointer type
                self.get_deref_type(operand_hir.ty)?
            }
            ast::UnaryOp::Move => {
                // Move operator preserves the operand's type
                operand_hir.ty
            }
            _ => operand_hir.ty,
        };

        match op {
            ast::UnaryOp::Ref | ast::UnaryOp::RefMut => Ok(HirExpr {
                kind: HirExprKind::Ref(operand_hir),
                ty,
            }),
            ast::UnaryOp::Deref => Ok(HirExpr {
                kind: HirExprKind::Deref(operand_hir),
                ty,
            }),
            ast::UnaryOp::Move => {
                // Move is a semantic marker - just return the operand
                // The semantic check happens in stmt_lowering
                Ok(*operand_hir)
            }
            _ => Ok(HirExpr {
                kind: HirExprKind::Unary {
                    op: (*op).into(),
                    operand: operand_hir,
                },
                ty,
            }),
        }
    }

    /// Lower a cast expression to HIR
    ///
    /// Handles type cast expressions like `expr as i64`.
    /// Supports casting between numeric types (int/float).
    pub(super) fn lower_cast(
        &mut self,
        expr: &Expr,
        target_type: &ast::Type,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let expr_hir = Box::new(self.lower_expr(expr, ctx)?);
        let target = self.resolve_type(target_type)?;

        Ok(HirExpr {
            kind: HirExprKind::Cast { expr: expr_hir, target },
            ty: target,
        })
    }
}
