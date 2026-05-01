//! Field access and index expression lowering
//!
//! This module contains expression lowering logic for field access
//! (struct fields, thread_group, SIMD swizzle, neighbor access) and indexing.

use simple_parser::Expr;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use crate::hir::lifetime::ReferenceOrigin;
use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    fn index_type_must_be_integer(&self, ty: TypeId) -> bool {
        if ty == TypeId::STRING {
            return true;
        }

        match self.module.types.get(ty) {
            Some(
                HirType::Array { .. }
                | HirType::Simd { .. }
                | HirType::Tuple(_)
                | HirType::LabeledTuple(_)
                | HirType::String,
            ) => true,
            Some(HirType::Pointer { inner, .. }) => self.index_type_must_be_integer(*inner),
            _ => false,
        }
    }

    fn is_integer_type(&self, ty: TypeId) -> bool {
        // Dynamic language: allow any type as index — runtime handles coercion.
        true
    }

    pub(super) fn require_integer_index_operand(&self, receiver_ty: TypeId, index_ty: TypeId) -> LowerResult<()> {
        if self.index_type_must_be_integer(receiver_ty) && !self.is_integer_type(index_ty) {
            return Err(LowerError::TypeMismatch {
                expected: TypeId::I64,
                found: index_ty,
            });
        }
        Ok(())
    }

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

            // Check if receiver is an enum type - handle as enum variant access
            if let Some(type_id) = self.module.types.lookup(recv_name) {
                if let Some(HirType::Enum { name: _, variants, .. }) = self.module.types.get(type_id) {
                    // Check if field is a valid variant name
                    for (variant_name, variant_fields) in variants {
                        if variant_name == field {
                            // This is an enum variant with no payload (or with payload to be filled later)
                            if variant_fields.is_none() {
                                // Unit variant - return enum value
                                return Ok(HirExpr {
                                    kind: HirExprKind::Global(format!("{}::{}", recv_name, field)),
                                    ty: type_id,
                                });
                            } else {
                                // Variant with fields - return constructor reference
                                // This will be called later with arguments
                                return Ok(HirExpr {
                                    kind: HirExprKind::Global(format!("{}::{}", recv_name, field)),
                                    ty: type_id,
                                });
                            }
                        }
                    }
                    // Variant not found
                    if self.lenient_types {
                        return Ok(HirExpr {
                            kind: HirExprKind::Global(format!("{}::{}", recv_name, field)),
                            ty: type_id,
                        });
                    }
                    return Err(LowerError::Unsupported(format!(
                        "enum '{}' has no variant named '{}'",
                        recv_name, field
                    )));
                }
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

        // Try regular struct field access first
        match self.get_field_info(recv_hir.ty, field) {
            Ok((field_index, field_ty)) => {
                // Track field access lifetime if receiver is a local variable reference
                if let HirExprKind::Local(idx) = &recv_hir.kind {
                    if let Some(local) = ctx.get_local(*idx) {
                        // Get the base origin and create a field origin
                        if let Some(base_origin) = self.lifetime_context.get_variable_origin(&local.name).cloned() {
                            let field_origin = ReferenceOrigin::Field {
                                base: Box::new(base_origin),
                                field: field.to_string(),
                            };
                            // Register field access for tracking (using a synthetic name)
                            let field_name = format!("{}.{}", local.name, field);
                            self.lifetime_context.register_variable(&field_name, field_origin);
                        }
                    }
                }

                Ok(HirExpr {
                    kind: HirExprKind::FieldAccess {
                        receiver: recv_hir,
                        field_index,
                    },
                    ty: field_ty,
                })
            }
            Err(LowerError::CannotInferFieldType { struct_name, .. }) => {
                if let Some(projected) = self.try_lower_result_projection(&recv_hir, field) {
                    return Ok(projected);
                }
                let mut candidate_struct_names = Vec::new();
                if !Self::is_unspecific_field_struct_name(&struct_name) {
                    candidate_struct_names.push(struct_name.clone());
                }
                if let Some(inferred_struct_name) = self.try_resolve_receiver_struct_name_from_expr(receiver, ctx) {
                    if !candidate_struct_names.iter().any(|name| name == &inferred_struct_name) {
                        candidate_struct_names.push(inferred_struct_name);
                    }
                }
                // Try to resolve field type via struct name lookup before falling back.
                // This preserves the real TypeId for self.field.method() chains — without
                // this, the field node gets ty=ANY which causes MIR to mangle the wrong
                // method name and emit a recursive self-call (phase4 STOP marker).
                for candidate_struct_name in candidate_struct_names {
                    if let Some(field_ty) = self
                        .try_resolve_field_type_by_name(&candidate_struct_name, field)
                        .or_else(|| self.try_resolve_global_field_type_by_name(&candidate_struct_name, field))
                    {
                        let field_index = self
                            .get_field_info(recv_hir.ty, field)
                            .ok()
                            .map(|(field_index, _)| field_index)
                            .or_else(|| self.try_resolve_global_field_index_by_name(&candidate_struct_name, field))
                            .unwrap_or(0);
                        return Ok(HirExpr {
                            kind: HirExprKind::FieldAccess {
                                receiver: recv_hir,
                                field_index,
                            },
                            ty: field_ty,
                        });
                    }
                    if let Some(field_index) = self.try_resolve_global_field_index_by_name(&candidate_struct_name, field) {
                        return Ok(HirExpr {
                            kind: HirExprKind::FieldAccess {
                                receiver: recv_hir,
                                field_index,
                            },
                            ty: TypeId::ANY,
                        });
                    }
                }
                // Field not found - treat as no-paren method call
                // This handles cases like container.resolve where resolve is a method
                Ok(HirExpr {
                    kind: HirExprKind::MethodCall {
                        receiver: recv_hir,
                        method: field.to_string(),
                        args: vec![],
                        dispatch: DispatchMode::Dynamic,
                    },
                    ty: TypeId::ANY, // Method return type is unknown at this point
                })
            }
            Err(e) => Err(e),
        }
    }

    /// Resolve the TypeId of a named field on a named struct type.
    ///
    /// Used as a fallback in `lower_field_access` when `get_field_info` returns
    /// `CannotInferFieldType` because the receiver's TypeId is ANY (or otherwise
    /// unresolved) but we know the struct name from the error payload.  By looking
    /// up the struct in the type registry by name we can recover the field's real
    /// TypeId and avoid emitting `ty: TypeId::ANY` on the HIR FieldAccess node —
    /// which would cause MIR to mangle the wrong method name downstream.
    fn try_resolve_field_type_by_name(&self, struct_name: &str, field_name: &str) -> Option<TypeId> {
        // Walk the type registry looking for a Struct whose name matches.
        for (_, hir_ty) in self.module.types.iter() {
            if let HirType::Struct { name, fields, .. } = hir_ty {
                if name == struct_name {
                    for (fname, fty) in fields.iter() {
                        if fname == field_name {
                            return Some(*fty);
                        }
                    }
                    // Struct found but field not present — no point searching further.
                    return None;
                }
            }
        }
        None
    }

    fn try_resolve_global_field_type_by_name(&mut self, struct_name: &str, field_name: &str) -> Option<TypeId> {
        let field_type_name = {
            let global_defs = self.global_struct_defs.as_ref()?;
            let fields = global_defs.get(struct_name)?;
            fields
                .iter()
                .find_map(|(fname, ftype)| if fname == field_name { Some(ftype.clone()) } else { None })?
        };
        self.resolve_global_type_spec(&field_type_name)
    }

    fn try_resolve_global_field_index_by_name(&self, struct_name: &str, field_name: &str) -> Option<usize> {
        let global_defs = self.global_struct_defs.as_ref()?;
        let fields = global_defs.get(struct_name)?;
        fields
            .iter()
            .enumerate()
            .find_map(|(idx, (fname, _))| if fname == field_name { Some(idx) } else { None })
    }

    fn try_resolve_receiver_struct_name_from_expr(
        &mut self,
        receiver: &Expr,
        ctx: &FunctionContext,
    ) -> Option<String> {
        match receiver {
            Expr::Identifier(name) => {
                let ty = if let Some(idx) = ctx.lookup(name) {
                    ctx.locals.get(idx).map(|local| local.ty)
                } else {
                    self.globals.get(name).copied()
                }?;
                self.try_named_struct_name_for_type(ty)
            }
            Expr::FieldAccess { receiver: base, field } => {
                let base_struct_name = self.try_resolve_receiver_struct_name_from_expr(base, ctx)?;
                let field_ty = self
                    .try_resolve_field_type_by_name(&base_struct_name, field)
                    .or_else(|| self.try_resolve_global_field_type_by_name(&base_struct_name, field))?;
                self.try_named_struct_name_for_type(field_ty)
            }
            _ => self
                .infer_type(receiver, ctx)
                .ok()
                .and_then(|ty| self.try_named_struct_name_for_type(ty)),
        }
    }

    fn try_named_struct_name_for_type(&self, ty: TypeId) -> Option<String> {
        let mut current = ty;
        loop {
            match self.module.types.get(current)? {
                HirType::Struct { name, .. } => return Some(name.clone()),
                HirType::Pointer { inner, .. } => current = *inner,
                _ => return None,
            }
        }
    }

    fn is_unspecific_field_struct_name(struct_name: &str) -> bool {
        matches!(struct_name, "ANY" | "Any" | "wildcard") || struct_name.starts_with("TypeId(")
    }

    fn try_lower_result_projection(&self, recv_hir: &HirExpr, field: &str) -> Option<HirExpr> {
        let variant = match field {
            "ok" => "Ok",
            "err" => "Err",
            _ => return None,
        };
        let payload_ty = self.enum_variant_payload_type(recv_hir.ty, "Result", variant)?;
        let expected_disc = self.enum_variant_discriminant(variant);
        let subject_for_check = recv_hir.clone();
        let subject_for_payload = recv_hir.clone();
        Some(HirExpr {
            kind: HirExprKind::If {
                condition: Box::new(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_enum_check_discriminant".to_string(),
                        args: vec![
                            subject_for_check,
                            HirExpr {
                                kind: HirExprKind::Integer(expected_disc),
                                ty: TypeId::I64,
                            },
                        ],
                    },
                    ty: TypeId::BOOL,
                }),
                then_branch: Box::new(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_enum_payload".to_string(),
                        args: vec![subject_for_payload],
                    },
                    ty: payload_ty,
                }),
                else_branch: Some(Box::new(HirExpr {
                    kind: HirExprKind::Nil,
                    ty: TypeId::NIL,
                })),
            },
            ty: payload_ty,
        })
    }

    fn enum_variant_payload_type(&self, ty: TypeId, enum_name: &str, variant_name: &str) -> Option<TypeId> {
        match self.module.types.get(ty) {
            Some(HirType::Enum { name, variants, .. }) if name == enum_name => variants.iter().find_map(|(name, payload)| {
                if name == variant_name {
                    payload.as_ref().and_then(|fields| fields.first()).copied()
                } else {
                    None
                }
            }),
            Some(HirType::Pointer { inner, .. }) => self.enum_variant_payload_type(*inner, enum_name, variant_name),
            _ => None,
        }
    }

    fn enum_variant_discriminant(&self, variant: &str) -> i64 {
        let mut hasher = DefaultHasher::new();
        variant.hash(&mut hasher);
        (hasher.finish() & 0xFFFFFFFF) as i64
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

    /// Lower a tuple index expression (`tup.0`, `tup.1`) to HIR
    ///
    /// Converts the numeric field access into an `Index` expression with an
    /// integer literal so that MIR lowering will emit `rt_tuple_get`.
    pub(super) fn lower_tuple_index(
        &mut self,
        receiver: &Expr,
        index: usize,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);
        let elem_ty = self.get_index_element_type(recv_hir.ty).unwrap_or(TypeId::ANY);

        let idx_hir = Box::new(HirExpr {
            kind: HirExprKind::Integer(index as i64),
            ty: TypeId::I64,
        });

        Ok(HirExpr {
            kind: HirExprKind::Index {
                receiver: recv_hir,
                index: idx_hir,
            },
            ty: elem_ty,
        })
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
        self.require_integer_index_operand(recv_hir.ty, idx_hir.ty)?;
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
