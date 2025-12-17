use simple_parser::{Expr, Type};

use super::super::types::*;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;

impl Lowerer {
    pub(super) fn resolve_type(&mut self, ty: &Type) -> LowerResult<TypeId> {
        match ty {
            Type::Simple(name) => self
                .module
                .types
                .lookup(name)
                .ok_or_else(|| LowerError::UnknownType(name.clone())),
            Type::Pointer { kind, inner } => {
                let inner_id = self.resolve_type(inner)?;
                let ptr_type = HirType::Pointer {
                    kind: (*kind).into(),
                    inner: inner_id,
                };
                Ok(self.module.types.register(ptr_type))
            }
            Type::Tuple(types) => {
                let mut type_ids = Vec::new();
                for t in types {
                    type_ids.push(self.resolve_type(t)?);
                }
                Ok(self.module.types.register(HirType::Tuple(type_ids)))
            }
            Type::Array { element, size } => {
                let elem_id = self.resolve_type(element)?;
                let size_val = size.as_ref().and_then(|e| {
                    if let Expr::Integer(n) = e.as_ref() {
                        Some(*n as usize)
                    } else {
                        None
                    }
                });
                Ok(self.module.types.register(HirType::Array {
                    element: elem_id,
                    size: size_val,
                }))
            }
            Type::Simd { lanes, element } => {
                let elem_id = self.resolve_type(element)?;
                Ok(self.module.types.register(HirType::Simd {
                    lanes: *lanes,
                    element: elem_id,
                }))
            }
            Type::Function { params, ret } => {
                let mut param_ids = Vec::new();
                for p in params {
                    param_ids.push(self.resolve_type(p)?);
                }
                let ret_id = if let Some(r) = ret {
                    self.resolve_type(r)?
                } else {
                    TypeId::VOID
                };
                Ok(self.module.types.register(HirType::Function {
                    params: param_ids,
                    ret: ret_id,
                }))
            }
            Type::Optional(inner) => {
                let inner_id = self.resolve_type(inner)?;
                Ok(self.module.types.register(HirType::Pointer {
                    kind: PointerKind::Shared,
                    inner: inner_id,
                }))
            }
            _ => Err(LowerError::Unsupported(format!("{:?}", ty))),
        }
    }

    pub(super) fn resolve_type_opt(&mut self, ty: &Option<Type>) -> LowerResult<TypeId> {
        match ty {
            Some(t) => self.resolve_type(t),
            None => Ok(TypeId::VOID),
        }
    }

    pub(super) fn get_deref_type(&self, ptr_ty: TypeId) -> LowerResult<TypeId> {
        if let Some(hir_ty) = self.module.types.get(ptr_ty) {
            match hir_ty {
                HirType::Pointer { inner, .. } => Ok(*inner),
                _ => Err(LowerError::CannotInferDerefType(format!("{:?}", hir_ty))),
            }
        } else {
            Err(LowerError::CannotInferDerefType(format!(
                "TypeId({:?})",
                ptr_ty
            )))
        }
    }

    pub(super) fn get_field_info(&self, struct_ty: TypeId, field: &str) -> LowerResult<(usize, TypeId)> {
        if let Some(hir_ty) = self.module.types.get(struct_ty) {
            match hir_ty {
                HirType::Struct { name, fields, .. } => {
                    for (idx, (field_name, field_ty)) in fields.iter().enumerate() {
                        if field_name == field {
                            return Ok((idx, *field_ty));
                        }
                    }
                    Err(LowerError::CannotInferFieldType {
                        struct_name: name.clone(),
                        field: field.to_string(),
                    })
                }
                HirType::Pointer { inner, .. } => {
                    self.get_field_info(*inner, field)
                }
                _ => Err(LowerError::CannotInferFieldType {
                    struct_name: format!("{:?}", hir_ty),
                    field: field.to_string(),
                }),
            }
        } else {
            Err(LowerError::CannotInferFieldType {
                struct_name: format!("TypeId({:?})", struct_ty),
                field: field.to_string(),
            })
        }
    }

    pub(super) fn get_index_element_type(&self, arr_ty: TypeId) -> LowerResult<TypeId> {
        if let Some(hir_ty) = self.module.types.get(arr_ty) {
            match hir_ty {
                HirType::Array { element, .. } => Ok(*element),
                HirType::Tuple(types) => {
                    types
                        .first()
                        .copied()
                        .ok_or_else(|| LowerError::CannotInferIndexType("empty tuple".to_string()))
                }
                HirType::Pointer { inner, .. } => {
                    self.get_index_element_type(*inner)
                }
                _ => Err(LowerError::CannotInferIndexType(format!("{:?}", hir_ty))),
            }
        } else {
            Err(LowerError::CannotInferIndexType(format!(
                "TypeId({:?})",
                arr_ty
            )))
        }
    }
}
