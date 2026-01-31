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
    /// Capability is determined by pointer kind:
    /// - Unique (&T) → Isolated (sole owner, transferable)
    /// - Shared (*T) → Shared (reference counted)
    /// - BorrowMut (&mut T) → Exclusive (mutable borrow)
    pub(super) fn lower_new(
        &mut self,
        kind: &ast::PointerKind,
        expr: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let value_hir = Box::new(self.lower_expr(expr, ctx)?);
        let inner_ty = value_hir.ty;
        let ptr_kind: PointerKind = (*kind).into();
        // Determine capability based on pointer kind
        let capability = match ptr_kind {
            PointerKind::Unique => ReferenceCapability::Isolated, // Sole owner
            PointerKind::BorrowMut | PointerKind::RawMut => ReferenceCapability::Exclusive, // Mutable
            _ => ReferenceCapability::Shared,                     // Shared, Borrow, Weak, Handle, RawConst
        };
        let ptr_type = HirType::Pointer {
            kind: ptr_kind,
            capability,
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
