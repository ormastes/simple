use simple_parser::{Expr, Type};

use super::super::types::*;
use super::error::LowerResult;
use super::lowerer::Lowerer;

impl Lowerer {
    pub(super) fn resolve_type(&mut self, ty: &Type) -> LowerResult<TypeId> {
        match ty {
            Type::Simple(name) => {
                // Bootstrap: all types are I64 tagged pointers at the C level.
                // Known primitives get their real type, everything else → I64.
                Ok(self.module.types.lookup(name).unwrap_or(TypeId::I64))
            }
            Type::Pointer { kind, inner } => {
                let inner_id = self.resolve_type(inner).unwrap_or(TypeId::I64);
                let ptr_type = HirType::Pointer {
                    kind: (*kind).into(),
                    inner: inner_id,
                };
                Ok(self.module.types.register(ptr_type))
            }
            Type::Tuple(types) => {
                let mut type_ids = Vec::new();
                for t in types {
                    type_ids.push(self.resolve_type(t).unwrap_or(TypeId::I64));
                }
                Ok(self.module.types.register(HirType::Tuple(type_ids)))
            }
            Type::Array { element, size } => {
                let elem_id = self.resolve_type(element).unwrap_or(TypeId::I64);
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
            Type::Function { params, ret } => {
                let mut param_ids = Vec::new();
                for p in params {
                    param_ids.push(self.resolve_type(p).unwrap_or(TypeId::I64));
                }
                let ret_id = if let Some(r) = ret {
                    self.resolve_type(r).unwrap_or(TypeId::VOID)
                } else {
                    TypeId::VOID
                };
                Ok(self.module.types.register(HirType::Function {
                    params: param_ids,
                    ret: ret_id,
                }))
            }
            Type::Optional(inner) => {
                let inner_id = self.resolve_type(inner).unwrap_or(TypeId::I64);
                Ok(self.module.types.register(HirType::Pointer {
                    kind: PointerKind::Shared,
                    inner: inner_id,
                }))
            }
            // Bootstrap: Generic types (Dict<K,V>, Result<T,E>, Option<T>, List<T>)
            // are all heap-allocated tagged pointers → I64
            Type::Generic { .. } => Ok(TypeId::I64),
            Type::Dict { .. } => Ok(TypeId::I64),
            Type::Union(_) => Ok(TypeId::I64),
            Type::DynTrait(_) => Ok(TypeId::I64),
            Type::Constructor { .. } => Ok(TypeId::I64),
            Type::Simd { .. } => Ok(TypeId::I64),
            // Catch-all: bootstrap treats everything as I64
            _ => Ok(TypeId::I64),
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
                // Bootstrap: deref on non-pointer → I64
                _ => Ok(TypeId::I64),
            }
        } else {
            Ok(TypeId::I64)
        }
    }

    pub(super) fn get_field_info(&self, struct_ty: TypeId, field: &str) -> LowerResult<(usize, TypeId)> {
        if let Some(hir_ty) = self.module.types.get(struct_ty) {
            match hir_ty {
                HirType::Struct { fields, .. } => {
                    for (idx, (field_name, field_ty)) in fields.iter().enumerate() {
                        if field_name == field {
                            return Ok((idx, *field_ty));
                        }
                    }
                    // Bootstrap: unknown field → (0, I64)
                    Ok((0, TypeId::I64))
                }
                HirType::Pointer { inner, .. } => {
                    self.get_field_info(*inner, field)
                }
                // Bootstrap: field access on non-struct → (0, I64)
                _ => Ok((0, TypeId::I64)),
            }
        } else {
            // Bootstrap: field access on unknown type → (0, I64)
            Ok((0, TypeId::I64))
        }
    }

    pub(super) fn get_index_element_type(&self, arr_ty: TypeId) -> LowerResult<TypeId> {
        if let Some(hir_ty) = self.module.types.get(arr_ty) {
            match hir_ty {
                HirType::Array { element, .. } => Ok(*element),
                HirType::Tuple(types) => {
                    Ok(types.first().copied().unwrap_or(TypeId::I64))
                }
                HirType::Pointer { inner, .. } => {
                    self.get_index_element_type(*inner)
                }
                // Bootstrap: index on non-array → I64
                _ => Ok(TypeId::I64),
            }
        } else {
            Ok(TypeId::I64)
        }
    }
}
