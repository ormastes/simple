use simple_parser::{ast::ReferenceCapability, Expr, Type};

use super::super::types::*;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;

impl Lowerer {
    pub(super) fn resolve_type(&mut self, ty: &Type) -> LowerResult<TypeId> {
        match ty {
            Type::Simple(name) => {
                // Handle Self type in class/struct methods
                if name == "Self" {
                    if let Some(class_ty) = self.current_class_type {
                        return Ok(class_ty);
                    } else {
                        // Self used outside of class context - special case
                        return Err(LowerError::UnknownType {
                            type_name: "Self".to_string(),
                            available_types: vec![],
                        });
                    }
                }
                self.module.types.lookup(name).ok_or_else(|| {
                    // Gather available type names for suggestions
                    let available_types = self.module.types.all_type_names();
                    LowerError::UnknownType {
                        type_name: name.clone(),
                        available_types,
                    }
                })
            }
            Type::Pointer { kind, inner } => {
                let inner_id = self.resolve_type(inner)?;
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
                    capability: ReferenceCapability::Shared, // Default capability
                    inner: inner_id,
                }))
            }
            Type::Union(types) => {
                let mut variant_ids = Vec::new();
                for t in types {
                    variant_ids.push(self.resolve_type(t)?);
                }
                Ok(self.module.types.register(HirType::Union { variants: variant_ids }))
            }
            Type::UnitWithRepr {
                name,
                repr,
                constraints,
            } => {
                // Determine the underlying repr type
                let (bits, signedness, is_float, repr_id) = if let Some(r) = repr {
                    let signedness = if r.signed {
                        Signedness::Signed
                    } else {
                        Signedness::Unsigned
                    };
                    let repr_type = if r.is_float {
                        HirType::Float { bits: r.bits }
                    } else {
                        HirType::Int {
                            bits: r.bits,
                            signedness,
                        }
                    };
                    let repr_id = self.module.types.register(repr_type);
                    (r.bits, signedness, r.is_float, repr_id)
                } else {
                    // Default to i64 if no repr specified
                    (64, Signedness::Signed, false, TypeId::I64)
                };

                let hir_constraints = HirUnitConstraints {
                    range: constraints.range,
                    overflow: constraints.overflow.into(),
                };

                Ok(self.module.types.register(HirType::UnitType {
                    name: name.clone(),
                    repr: repr_id,
                    bits,
                    signedness,
                    is_float,
                    constraints: hir_constraints,
                }))
            }
            Type::Capability { capability, inner } => {
                // Resolve the inner type first
                let inner_id = self.resolve_type(inner)?;

                // Get the inner HIR type to check if it's already a pointer
                if let Some(inner_hir) = self.module.types.get(inner_id) {
                    match inner_hir {
                        HirType::Pointer {
                            kind,
                            capability: _,
                            inner: ptr_inner,
                        } => {
                            // Inner is already a pointer, update its capability
                            let ptr_type = HirType::Pointer {
                                kind: *kind,
                                capability: *capability,
                                inner: *ptr_inner,
                            };
                            Ok(self.module.types.register(ptr_type))
                        }
                        _ => {
                            // Inner is not a pointer, wrap it in a reference with the capability
                            // Use Borrow for shared, BorrowMut for exclusive/isolated
                            let kind = if capability.allows_mutation() {
                                PointerKind::BorrowMut
                            } else {
                                PointerKind::Borrow
                            };
                            let ptr_type = HirType::Pointer {
                                kind,
                                capability: *capability,
                                inner: inner_id,
                            };
                            Ok(self.module.types.register(ptr_type))
                        }
                    }
                } else {
                    // Cannot get inner type, error
                    Err(LowerError::UnknownType {
                        type_name: format!("capability inner type {:?}", inner),
                        available_types: self.module.types.all_type_names(),
                    })
                }
            }
            Type::Generic { name, args } => {
                // Handle common generic types used in stdlib
                match name.as_str() {
                    // Dict<K, V> - dictionary type, represented as Any at native level
                    "Dict" => Ok(TypeId::ANY),
                    // Option<T> - optional type
                    "Option" if args.len() == 1 => {
                        let inner = self.resolve_type(&args[0])?;
                        Ok(self.module.types.register(HirType::Pointer {
                            kind: PointerKind::Shared,
                            capability: ReferenceCapability::Shared,
                            inner,
                        }))
                    }
                    // Result<T, E> - result type, represented as Any at native level
                    "Result" => Ok(TypeId::ANY),
                    // List<T> - same as array
                    "List" if args.len() == 1 => {
                        let elem = self.resolve_type(&args[0])?;
                        Ok(self.module.types.register(HirType::Array {
                            element: elem,
                            size: None,
                        }))
                    }
                    // Set<T> - represented as Any at native level
                    "Set" => Ok(TypeId::ANY),
                    // Other generic types - treat as Any (dynamically typed)
                    _ => Ok(TypeId::ANY),
                }
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
            Err(LowerError::CannotInferDerefType(format!("TypeId({:?})", ptr_ty)))
        }
    }

    pub(super) fn get_field_info(&self, struct_ty: TypeId, field: &str) -> LowerResult<(usize, TypeId)> {
        // Handle built-in ANY type - search all known structs for the field
        // When ambiguous, prefer the struct with the most fields (best guess)
        if struct_ty == TypeId::ANY {
            let mut best: Option<(usize, TypeId, usize)> = None; // (idx, ty, field_count)
            for (_, hir_ty) in self.module.types.iter() {
                if let HirType::Struct { fields, .. } = hir_ty {
                    for (idx, (field_name, field_ty)) in fields.iter().enumerate() {
                        if field_name == field {
                            let count = fields.len();
                            if best.as_ref().map_or(true, |(_, _, c)| count > *c) {
                                best = Some((idx, *field_ty, count));
                            }
                        }
                    }
                }
            }
            if let Some((idx, ty, _)) = best {
                return Ok((idx, ty));
            }
            return Ok((0, TypeId::ANY)); // Fallback: dynamic field access
        }

        if let Some(hir_ty) = self.module.types.get(struct_ty) {
            match hir_ty {
                // Any type - search all known structs for the field
                // When ambiguous, prefer the struct with the most fields
                HirType::Any => {
                    let mut best: Option<(usize, TypeId, usize)> = None;
                    for (_, search_ty) in self.module.types.iter() {
                        if let HirType::Struct { fields, .. } = search_ty {
                            for (idx, (field_name, field_ty)) in fields.iter().enumerate() {
                                if field_name == field {
                                    let count = fields.len();
                                    if best.as_ref().map_or(true, |(_, _, c)| count > *c) {
                                        best = Some((idx, *field_ty, count));
                                    }
                                }
                            }
                        }
                    }
                    if let Some((idx, ty, _)) = best {
                        return Ok((idx, ty));
                    }
                    return Ok((0, TypeId::ANY));
                }
                HirType::Struct { name, fields, .. } => {
                    for (idx, (field_name, field_ty)) in fields.iter().enumerate() {
                        if field_name == field {
                            return Ok((idx, *field_ty));
                        }
                    }
                    // Collect available field names for suggestions
                    let available_fields = fields.iter().map(|(name, _)| name.clone()).collect();
                    Err(LowerError::CannotInferFieldType {
                        struct_name: name.clone(),
                        field: field.to_string(),
                        available_fields,
                    })
                }
                HirType::Pointer { inner, .. } => self.get_field_info(*inner, field),
                _ => Err(LowerError::CannotInferFieldType {
                    struct_name: format!("{:?}", hir_ty),
                    field: field.to_string(),
                    available_fields: vec![],
                }),
            }
        } else {
            Err(LowerError::CannotInferFieldType {
                struct_name: format!("TypeId({:?})", struct_ty),
                field: field.to_string(),
                available_fields: vec![],
            })
        }
    }

    pub(super) fn get_index_element_type(&self, arr_ty: TypeId) -> LowerResult<TypeId> {
        // Handle built-in ANY type directly
        if arr_ty == TypeId::ANY {
            return Ok(TypeId::ANY); // Indexing into Any returns Any
        }

        // Handle built-in String type (indexing into string returns string/char)
        if arr_ty == TypeId::STRING {
            return Ok(TypeId::STRING); // String indexing returns a single-char string
        }

        if let Some(hir_ty) = self.module.types.get(arr_ty) {
            match hir_ty {
                HirType::Array { element, .. } => Ok(*element),
                HirType::Simd { element, .. } => Ok(*element),
                HirType::Tuple(types) => types
                    .first()
                    .copied()
                    .ok_or_else(|| LowerError::CannotInferIndexType("empty tuple".to_string())),
                HirType::Pointer { inner, .. } => self.get_index_element_type(*inner),
                // String type - indexing returns a single-char string
                HirType::String => Ok(TypeId::STRING),
                // Any type (Dict, generic containers) - indexing returns Any
                HirType::Any => Ok(TypeId::ANY),
                // Struct type - dynamic indexing (like dict["key"]) returns Any
                HirType::Struct { .. } => Ok(TypeId::ANY),
                // Enum type - indexing is dynamic
                HirType::Enum { .. } => Ok(TypeId::ANY),
                _ => Err(LowerError::CannotInferIndexType(format!("{:?}", hir_ty))),
            }
        } else {
            Err(LowerError::CannotInferIndexType(format!("TypeId({:?})", arr_ty)))
        }
    }
}
