//! Field access and index expression lowering
//!
//! This module contains expression lowering logic for field access
//! (struct fields, thread_group, SIMD swizzle, neighbor access) and indexing.

use simple_parser::Expr;

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower a field access expression to HIR
    ///
    /// Handles:
    /// - thread_group.id and thread_group.size (GPU intrinsics)
    /// - SIMD neighbor access (.left_neighbor, .right_neighbor)
    /// - SIMD swizzle patterns (.xyzw, .rgba, etc.)
    /// - Regular struct field access
    pub(super) fn lower_field_access(
        &mut self,
        receiver: &Expr,
        field: &str,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Check for thread_group.id and thread_group.size before lowering receiver
        if let Expr::Identifier(recv_name) = receiver {
            if recv_name == "thread_group" {
                return self.lower_thread_group_field(field);
            }
        }

        let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);

        // Check for SIMD neighbor access
        if field == "left_neighbor" || field == "right_neighbor" {
            if let Some(result) = self.lower_neighbor_access(&recv_hir, field)? {
                return Ok(result);
            }
        }

        // Check for SIMD swizzle
        if let Some(result) = self.lower_simd_swizzle(&recv_hir, field)? {
            return Ok(result);
        }

        // Regular struct field access
        let (field_index, field_ty) = self.get_field_info(recv_hir.ty, field)?;
        Ok(HirExpr {
            kind: HirExprKind::FieldAccess {
                receiver: recv_hir,
                field_index,
            },
            ty: field_ty,
        })
    }

    /// Lower thread_group field access to GPU intrinsics
    ///
    /// - thread_group.id → GroupId intrinsic
    /// - thread_group.size → LocalSize intrinsic
    fn lower_thread_group_field(&self, field: &str) -> LowerResult<HirExpr> {
        match field {
            "id" => {
                // thread_group.id → GroupId intrinsic
                Ok(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::GroupId,
                        args: vec![],
                    },
                    ty: TypeId::I64,
                })
            }
            "size" => {
                // thread_group.size → LocalSize intrinsic
                Ok(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::LocalSize,
                        args: vec![],
                    },
                    ty: TypeId::I64,
                })
            }
            _ => Err(LowerError::Unsupported(format!(
                "unknown thread_group property: {}",
                field
            ))),
        }
    }

    /// Lower SIMD neighbor access (.left_neighbor, .right_neighbor)
    ///
    /// Returns Some(HirExpr) if the receiver is an array/SIMD type, None otherwise.
    fn lower_neighbor_access(&mut self, recv_hir: &HirExpr, field: &str) -> LowerResult<Option<HirExpr>> {
        if let Some(element_ty) = self.module.types.get_array_element(recv_hir.ty) {
            let direction = if field == "left_neighbor" {
                NeighborDirection::Left
            } else {
                NeighborDirection::Right
            };
            Ok(Some(HirExpr {
                kind: HirExprKind::NeighborAccess {
                    array: Box::new(recv_hir.clone()),
                    direction,
                },
                ty: element_ty,
            }))
        } else {
            Ok(None)
        }
    }

    /// Lower SIMD swizzle patterns (.xyzw, .rgba, etc.)
    ///
    /// Returns Some(HirExpr) if the receiver is a SIMD type and field is a valid swizzle, None otherwise.
    fn lower_simd_swizzle(&mut self, recv_hir: &HirExpr, field: &str) -> LowerResult<Option<HirExpr>> {
        if let Some(HirType::Simd { lanes, element }) = self.module.types.get(recv_hir.ty) {
            let lanes = *lanes;
            let element = *element;
            if let Some(indices) = self.parse_swizzle_pattern(field, lanes) {
                // Create indices array literal
                let indices_hir: Vec<HirExpr> = indices
                    .iter()
                    .map(|&i| HirExpr {
                        kind: HirExprKind::Integer(i as i64),
                        ty: TypeId::I64,
                    })
                    .collect();
                let indices_len = indices_hir.len() as u32;
                let indices_array_ty = self.module.types.register(HirType::Array {
                    element: TypeId::I64,
                    size: Some(indices_len as usize),
                });
                let indices_expr = HirExpr {
                    kind: HirExprKind::Array(indices_hir),
                    ty: indices_array_ty,
                };
                // Result type: same element type, but with number of lanes from swizzle length
                let result_ty = self.module.types.register(HirType::Simd {
                    lanes: indices_len,
                    element,
                });
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdShuffle,
                        args: vec![recv_hir.clone(), indices_expr],
                    },
                    ty: result_ty,
                }));
            }
        }
        Ok(None)
    }

    /// Lower an index expression to HIR
    ///
    /// For SIMD types, uses SimdExtract intrinsic.
    /// For arrays/vectors, uses regular indexing.
    pub(super) fn lower_index(
        &mut self,
        receiver: &Expr,
        index: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);
        let idx_hir = Box::new(self.lower_expr(index, ctx)?);
        let elem_ty = self.get_index_element_type(recv_hir.ty)?;

        // Check if receiver is SIMD type - use SimdExtract intrinsic
        if let Some(HirType::Simd { .. }) = self.module.types.get(recv_hir.ty) {
            return Ok(HirExpr {
                kind: HirExprKind::GpuIntrinsic {
                    intrinsic: GpuIntrinsicKind::SimdExtract,
                    args: vec![*recv_hir, *idx_hir],
                },
                ty: elem_ty,
            });
        }

        Ok(HirExpr {
            kind: HirExprKind::Index {
                receiver: recv_hir,
                index: idx_hir,
            },
            ty: elem_ty,
        })
    }
}
