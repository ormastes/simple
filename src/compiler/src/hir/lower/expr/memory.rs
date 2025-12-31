//! Memory allocation expression lowering
//!
//! This module contains expression lowering logic for pointer allocation (new expressions).

use simple_parser::{self as ast, ast::ReferenceCapability, Expr};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::LowerResult;
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower a `new` pointer allocation expression to HIR
    ///
    /// Creates a heap-allocated value and returns a pointer to it.
    /// Pointer kind can be: owned, borrowed, or mutable borrowed.
    /// Default capability is Shared.
    pub(super) fn lower_new(
        &mut self,
        kind: &ast::PointerKind,
        expr: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let value_hir = Box::new(self.lower_expr(expr, ctx)?);
        let inner_ty = value_hir.ty;
        let ptr_kind: PointerKind = (*kind).into();
        let ptr_type = HirType::Pointer {
            kind: ptr_kind,
            capability: ReferenceCapability::Shared, // Default capability
            inner: inner_ty,
        };
        let ptr_ty = self.module.types.register(ptr_type);
        Ok(HirExpr {
            kind: HirExprKind::PointerNew {
                kind: ptr_kind,
                value: value_hir,
            },
            ty: ptr_ty,
        })
    }
}
