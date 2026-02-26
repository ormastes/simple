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
            // Bootstrap: Generic types — track Dict<K,V> and Option<T> for correct field access
            Type::Generic { name, args } => {
                if name == "Dict" && args.len() == 2 {
                    let key_id = self.resolve_type(&args[0]).unwrap_or(TypeId::I64);
                    let value_id = self.resolve_type(&args[1]).unwrap_or(TypeId::I64);
                    Ok(self.module.types.register(HirType::Dict {
                        key: key_id,
                        value: value_id,
                    }))
                } else if (name == "Option" || name == "Some") && args.len() == 1 {
                    // Option<T> / Some<T> → Pointer wrapping T, so unwrap() can return T
                    let inner_id = self.resolve_type(&args[0]).unwrap_or(TypeId::I64);
                    Ok(self.module.types.register(HirType::Pointer {
                        kind: PointerKind::Shared,
                        inner: inner_id,
                    }))
                } else if name == "Result" && args.len() >= 1 {
                    // Result<T, E> → track success type T via Pointer
                    let ok_id = self.resolve_type(&args[0]).unwrap_or(TypeId::I64);
                    Ok(self.module.types.register(HirType::Pointer {
                        kind: PointerKind::Shared,
                        inner: ok_id,
                    }))
                } else {
                    // Other generics (List<T>, etc.) → I64
                    Ok(TypeId::I64)
                }
            }
            // Dict<K, V> → track key/value types for correct field access on values
            Type::Dict { key, value } => {
                let key_id = self.resolve_type(key).unwrap_or(TypeId::I64);
                let value_id = self.resolve_type(value).unwrap_or(TypeId::I64);
                Ok(self.module.types.register(HirType::Dict {
                    key: key_id,
                    value: value_id,
                }))
            }
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
                HirType::Struct { fields, name, .. } => {
                    for (idx, (field_name, field_ty)) in fields.iter().enumerate() {
                        if field_name == field {
                            return Ok((idx, *field_ty));
                        }
                    }
                    if fields.is_empty() {
                        // Struct type registered but no fields — search ALL registered structs
                        // This handles cross-module structs where fields weren't propagated
                        eprintln!("[field-resolve] Struct '{}' has 0 fields, searching all types for field '{}'", name, field);
                        if let Some((idx, ty)) = self.search_all_structs_for_field(field) {
                            return Ok((idx, ty));
                        }
                    } else {
                        eprintln!("[field-resolve] Struct '{}' ({} fields) missing field '{}', fields: {:?}",
                            name, fields.len(), field,
                            fields.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>());
                    }
                    // Bootstrap: unknown field → (0, I64)
                    Ok((0, TypeId::I64))
                }
                HirType::Pointer { inner, .. } => {
                    self.get_field_info(*inner, field)
                }
                // Bootstrap: field access on non-struct type — search all structs
                _ => {
                    if let Some((idx, ty)) = self.search_all_structs_for_field(field) {
                        return Ok((idx, ty));
                    }
                    eprintln!("[field-resolve] Non-struct type {:?} field '{}' → fallback (0, I64)", struct_ty, field);
                    Ok((0, TypeId::I64))
                },
            }
        } else {
            // Unknown type — search all registered structs for this field name
            if let Some((idx, ty)) = self.search_all_structs_for_field(field) {
                return Ok((idx, ty));
            }
            eprintln!("[field-resolve] Unknown type {:?} field '{}' → fallback (0, I64)", struct_ty, field);
            Ok((0, TypeId::I64))
        }
    }

    /// Search all registered struct types for a field by name.
    /// When multiple structs have the same field, prefer the struct with the most fields
    /// (larger structs are more specific and less likely to be a false match).
    fn search_all_structs_for_field(&self, field: &str) -> Option<(usize, TypeId)> {
        let mut best_match: Option<(usize, TypeId, usize, &str)> = None; // (idx, ty, field_count, name)
        for hir_ty in self.module.types.all_types() {
            if let HirType::Struct { fields, name, .. } = hir_ty {
                if !fields.is_empty() {
                    for (idx, (field_name, field_ty)) in fields.iter().enumerate() {
                        if field_name == field {
                            let field_count = fields.len();
                            if let Some((_, _, best_count, _)) = &best_match {
                                if field_count > *best_count {
                                    best_match = Some((idx, *field_ty, field_count, name));
                                }
                            } else {
                                best_match = Some((idx, *field_ty, field_count, name));
                            }
                            break; // Found field in this struct, check next struct
                        }
                    }
                }
            }
        }
        if let Some((idx, ty, count, name)) = best_match {
            eprintln!("[field-resolve] search_all_structs: field '{}' → struct '{}' ({} fields) at index {}", field, name, count, idx);
            Some((idx, ty))
        } else {
            None
        }
    }

    /// Get key and value types for a Dict type, if it is one.
    pub(super) fn get_dict_kv_types(&self, ty: TypeId) -> Option<(TypeId, TypeId)> {
        if let Some(hir_ty) = self.module.types.get(ty) {
            match hir_ty {
                HirType::Dict { key, value } => Some((*key, *value)),
                HirType::Pointer { inner, .. } => self.get_dict_kv_types(*inner),
                _ => None,
            }
        } else {
            None
        }
    }

    pub(super) fn get_index_element_type(&self, arr_ty: TypeId) -> LowerResult<TypeId> {
        if let Some(hir_ty) = self.module.types.get(arr_ty) {
            match hir_ty {
                HirType::Array { element, .. } => Ok(*element),
                HirType::Dict { value, .. } => Ok(*value),
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
