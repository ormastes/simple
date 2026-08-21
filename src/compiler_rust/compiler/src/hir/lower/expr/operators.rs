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
    fn is_float_scalar(ty: TypeId) -> bool {
        matches!(ty, TypeId::F32 | TypeId::F64)
    }

    fn is_int_scalar(ty: TypeId) -> bool {
        matches!(
            ty,
            TypeId::I8
                | TypeId::I16
                | TypeId::I32
                | TypeId::I64
                | TypeId::U8
                | TypeId::U16
                | TypeId::U32
                | TypeId::U64
        )
    }

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
            // `NotIn` belongs here with `In`: leaving it out fell through to
            // `left_hir.ty`, so `"zzz" not in hay` was typed TEXT and printing
            // it decoded the raw 0/1 as a heap handle ("nil"/"0"). Branching
            // still worked, which is why this hid behind `if x not in y`.
            ast::BinOp::And | ast::BinOp::Or | ast::BinOp::Is | ast::BinOp::In | ast::BinOp::NotIn => TypeId::BOOL,
            // An arithmetic/bit op with an ANY operand has an ANY RESULT, because
            // `mir/lower/lowering_expr_ops.rs` deliberately RE-BOXES that result
            // (a consumer of an ANY value always decodes the tag-boxed form; see
            // seed_mir_any_binop_result_unboxed_2026-08-15.md). Typing the
            // expression from `left_hir.ty` alone lost that whenever the ANY
            // operand was on the RIGHT: `unbox_scalar_for_raw_slot` gates on this
            // very TypeId, so `return 1 + a.get(0)` in a `-> i64` fn saw `i64`,
            // skipped the unbox, and returned `v << 3`. Measured 2026-08-17:
            // `a.get(0)+1` -> 11 correct but `1+a.get(0)` -> 88 == 11<<3, and
            // likewise 100-a.get(0) -> 720, 2*a.get(0) -> 160, 100/a.get(0) -> 80.
            // ANY-on-the-left and ANY-on-both already yielded ANY here and were
            // correct, which is exactly the asymmetry this closes.
            //
            // Mirrors the MIR guard precisely: that band-aid only unboxes/re-boxes
            // when the concrete side is a numeric scalar, so `"s" + any_value`
            // (string concat) is NOT covered there and must NOT be retyped here.
            _ if left_hir.ty != TypeId::ANY
                && right_hir.ty == TypeId::ANY
                && matches!(
                    left_hir.ty,
                    TypeId::I8
                        | TypeId::I16
                        | TypeId::I32
                        | TypeId::I64
                        | TypeId::U8
                        | TypeId::U16
                        | TypeId::U32
                        | TypeId::U64
                        | TypeId::F32
                        | TypeId::F64
                ) =>
            {
                TypeId::ANY
            }
            // NUMERIC PROMOTION. Falling through to `left_hir.ty` typed
            // `x * 1.5` as I64 whenever `x` was an integer — including every
            // untyped lambda parameter, which `lower_lambda` defaults to I64.
            // Codegen's binary arm already coerces a mixed int/float pair to
            // FLOAT (see the float-vs-nil note in
            // `mir/lower/lowering_expr_ops.rs`), so the HIR type was a plain
            // lie about the machine value: the expression computes an f64 and
            // claimed i64. That lie is what made the JIT closure ABI
            // unimplementable — no value encoding at an indirect-call boundary
            // can be correct when the declared result type disagrees with the
            // register class actually produced. See
            // `doc/08_tracking/bug/seed_jit_coverage_self_hosted_compiler_2026-08-21.md`.
            //
            // Scoped deliberately: only when BOTH sides are numeric scalars and
            // exactly one is a float, so string concat (`"s" + n`), ANY operands
            // (handled above) and non-scalar operands are untouched.
            _ if Self::is_float_scalar(right_hir.ty) && Self::is_int_scalar(left_hir.ty) => right_hir.ty,
            _ if Self::is_float_scalar(left_hir.ty) && Self::is_int_scalar(right_hir.ty) => left_hir.ty,
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
                // RefMut (&mut) requires Exclusive capability, Ref (&) uses Shared
                let capability = if *op == ast::UnaryOp::RefMut {
                    ReferenceCapability::Exclusive
                } else {
                    ReferenceCapability::Shared
                };
                let ptr_type = HirType::Pointer {
                    kind,
                    capability,
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
            ast::UnaryOp::Ref | ast::UnaryOp::RefMut => {
                // Check aliasing rules for exclusive/isolated capabilities
                if *op == ast::UnaryOp::RefMut {
                    if let Some(id) = self.get_expr_ref_id(&operand_hir) {
                        // Check if we can acquire exclusive capability
                        self.capability_env.can_acquire(id, ReferenceCapability::Exclusive)?;
                        // Acquire the capability to track it
                        self.capability_env.acquire(id, ReferenceCapability::Exclusive);
                    }
                }
                Ok(HirExpr {
                    kind: HirExprKind::Ref(operand_hir),
                    ty,
                })
            }
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
