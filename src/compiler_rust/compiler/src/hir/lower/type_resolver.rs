use simple_parser::{ast::ReferenceCapability, Expr, Type};

use super::super::types::*;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;

impl Lowerer {
    fn instantiate_builtin_generic_enum(&mut self, family: &str, args: &[Type]) -> Option<LowerResult<TypeId>> {
        match (family, args.len()) {
            ("Option", 1) => {
                let inner = match self.resolve_type(&args[0]) {
                    Ok(inner) => inner,
                    Err(err) => return Some(Err(err)),
                };
                Some(Ok(self.module.types.register(HirType::Enum {
                    name: "Option".to_string(),
                    variants: vec![("Some".to_string(), Some(vec![inner])), ("None".to_string(), None)],
                    generic_params: vec!["T".to_string()],
                    is_generic_template: false,
                    type_bindings: std::collections::HashMap::from([("T".to_string(), inner)]),
                })))
            }
            ("Result", 2) => {
                let ok_ty = match self.resolve_type(&args[0]) {
                    Ok(ok_ty) => ok_ty,
                    Err(err) => return Some(Err(err)),
                };
                let err_ty = match self.resolve_type(&args[1]) {
                    Ok(err_ty) => err_ty,
                    Err(err) => return Some(Err(err)),
                };
                Some(Ok(self.module.types.register(HirType::Enum {
                    name: "Result".to_string(),
                    variants: vec![
                        ("Ok".to_string(), Some(vec![ok_ty])),
                        ("Err".to_string(), Some(vec![err_ty])),
                    ],
                    generic_params: vec!["T".to_string(), "E".to_string()],
                    is_generic_template: false,
                    type_bindings: std::collections::HashMap::from([
                        ("T".to_string(), ok_ty),
                        ("E".to_string(), err_ty),
                    ]),
                })))
            }
            _ => None,
        }
    }

    pub(super) fn resolve_type(&mut self, ty: &Type) -> LowerResult<TypeId> {
        match ty {
            Type::Simple(name) => {
                let name = self.resolve_type_alias(name).unwrap_or(name);
                // Handle "name?" pattern — some code paths produce Type::Simple("text?")
                // instead of Type::Optional(Type::Simple("text")). Normalize here.
                if let Some(base) = name.strip_suffix('?') {
                    if !base.is_empty() {
                        let inner = Type::Simple(base.to_string());
                        return self.resolve_type(&Type::Optional(Box::new(inner)));
                    }
                }
                // Handle Self type in class/struct methods
                if name == "Self" {
                    if let Some(class_ty) = self.current_class_type {
                        return Ok(class_ty);
                    } else if self.lenient_types {
                        return Ok(TypeId::ANY);
                    } else {
                        // Self used outside of class context - special case
                        return Err(LowerError::UnknownType {
                            type_name: "Self".to_string(),
                            available_types: vec![],
                        });
                    }
                }
                if let Some(id) = self.module.types.lookup(name) {
                    return Ok(id);
                }
                // Fall back to cross-module struct definitions. This handles
                // files that use a struct type by name (e.g. as a parameter
                // annotation) without an explicit `use` statement — common
                // when a module is split across sibling files that share a
                // single top-level main.spl. Registering the struct locally
                // turns ANY-typed receivers into proper struct types so
                // `entry.name` lowers to a FieldGet instead of a method call.
                if let Some(ref global_defs) = self.global_struct_defs.clone() {
                    if let Some(field_specs) = global_defs.get(name) {
                        let hir_fields: Vec<(String, TypeId)> = field_specs
                            .iter()
                            .map(|(fname, _ftype)| (fname.clone(), TypeId::ANY))
                            .collect();
                        let struct_ty = HirType::Struct {
                            name: name.to_string(),
                            fields: hir_fields,
                            has_snapshot: false,
                            generic_params: vec![],
                            is_generic_template: false,
                            type_bindings: std::collections::HashMap::new(),
                        };
                        let id = self.module.types.register_named(name.to_string(), struct_ty);
                        return Ok(id);
                    }
                }
                if self.lenient_types {
                    // In lenient mode, treat unknown types as ANY to allow compilation to proceed
                    return Ok(TypeId::ANY);
                }
                let available_types = self.module.types.all_type_names();
                Err(LowerError::UnknownType {
                    type_name: name.to_string(),
                    available_types,
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
            Type::LabeledTuple(fields) => {
                let mut hir_fields = Vec::new();
                for field in fields {
                    hir_fields.push((field.label.clone(), self.resolve_type(&field.ty)?));
                }
                Ok(self.module.types.register(HirType::LabeledTuple(hir_fields)))
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
                let family_name = self.resolve_type_alias(name).unwrap_or(name).to_string();
                if let Some(family_ty) = self.module.types.lookup(&family_name) {
                    let family_name = match self.module.types.get(family_ty) {
                        Some(HirType::Enum { name, .. }) => Some(name.clone()),
                        _ => None,
                    };
                    if let Some(family) = family_name {
                        if let Some(instantiated) = self.instantiate_builtin_generic_enum(&family, args) {
                            return instantiated;
                        }
                    }
                }
                // Handle common generic types used in stdlib
                match family_name.as_str() {
                    // Dict<K, V> - dictionary type, represented as Any at native level
                    "Dict" => Ok(TypeId::ANY),
                    // Option<T> - preserve enum identity so builtin methods and
                    // payload extraction stay on the Option family.
                    "Option" if args.len() == 1 => self
                        .instantiate_builtin_generic_enum("Option", args)
                        .expect("Option arity checked above"),
                    // Result<T, E> - preserve enum identity so `expr?` and
                    // result helpers do not fall through to unrelated unwrap families.
                    "Result" if args.len() == 2 => self
                        .instantiate_builtin_generic_enum("Result", args)
                        .expect("Result arity checked above"),
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
            _ => {
                if self.lenient_types {
                    Ok(TypeId::ANY)
                } else {
                    Err(LowerError::Unsupported(format!("{:?}", ty)))
                }
            }
        }
    }

    pub(super) fn resolve_type_opt(&mut self, ty: &Option<Type>) -> LowerResult<TypeId> {
        match ty {
            Some(t) => self.resolve_type(t),
            None => Ok(TypeId::VOID),
        }
    }

    pub(super) fn get_deref_type(&self, ptr_ty: TypeId) -> LowerResult<TypeId> {
        // Handle built-in ANY type
        if ptr_ty == TypeId::ANY {
            return Ok(TypeId::ANY);
        }
        if let Some(hir_ty) = self.module.types.get(ptr_ty) {
            match hir_ty {
                HirType::Pointer { inner, .. } => Ok(*inner),
                _ => {
                    if self.lenient_types {
                        Ok(TypeId::ANY)
                    } else {
                        Err(LowerError::CannotInferDerefType(format!("{:?}", hir_ty)))
                    }
                }
            }
        } else if self.lenient_types {
            Ok(TypeId::ANY)
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
                            if best.as_ref().is_none_or(|(_, _, c)| count > *c) {
                                best = Some((idx, *field_ty, count));
                            }
                        }
                    }
                }
            }
            if let Some((idx, ty, _)) = best {
                return Ok((idx, ty));
            }
            // Search global struct definitions from other compilation units.
            // Skip names that are known to be ambiguous across multiple
            // structs — those must fall back to method-call resolution so
            // we don't silently pick the wrong byte offset.
            if self.is_ambiguous_global_field(field) {
                return Err(LowerError::CannotInferFieldType {
                    struct_name: "ANY".to_string(),
                    field: field.to_string(),
                    available_fields: vec![],
                });
            }
            if let Some(ref global_defs) = self.global_struct_defs {
                let mut best_global: Option<(usize, usize, String)> = None;
                for (sname, fields) in global_defs.iter() {
                    for (idx, (fname, _)) in fields.iter().enumerate() {
                        if fname == field {
                            let count = fields.len();
                            if best_global.as_ref().is_none_or(|(_, c, _)| count > *c) {
                                best_global = Some((idx, count, sname.clone()));
                            }
                        }
                    }
                }
                if let Some((idx, count, sname)) = best_global {
                    if std::env::var("SIMPLE_TRACE_FIELD_GET").is_ok() {
                        let fpath = self
                            .current_file
                            .as_ref()
                            .and_then(|p| p.file_name())
                            .and_then(|n| n.to_str())
                            .unwrap_or("unknown");
                        eprintln!("[FIELD-TRACE] ANY/{field} -> global {sname}[{idx}] (count={count}) in {fpath}");
                    }
                    let _ = count;
                    let _ = sname;
                    return Ok((idx, TypeId::ANY));
                }
            }
            return Err(LowerError::CannotInferFieldType {
                struct_name: "ANY".to_string(),
                field: field.to_string(),
                available_fields: vec![],
            });
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
                                    if best.as_ref().is_none_or(|(_, _, c)| count > *c) {
                                        best = Some((idx, *field_ty, count));
                                    }
                                }
                            }
                        }
                    }
                    if let Some((idx, ty, _)) = best {
                        return Ok((idx, ty));
                    }
                    // No struct with this field found — return error to fall back to
                    // dynamic method dispatch instead of wrong FieldGet at offset 0
                    Err(LowerError::CannotInferFieldType {
                        struct_name: "Any".to_string(),
                        field: field.to_string(),
                        available_fields: vec![],
                    })
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
                HirType::Bitfield { name, fields, .. } => {
                    for (idx, field_info) in fields.iter().enumerate() {
                        if field_info.name == field {
                            return Ok((idx, field_info.ty));
                        }
                    }
                    let available_fields = fields.iter().map(|f| f.name.clone()).collect();
                    Err(LowerError::CannotInferFieldType {
                        struct_name: name.clone(),
                        field: field.to_string(),
                        available_fields,
                    })
                }
                HirType::Pointer { inner, .. } => self.get_field_info(*inner, field),
                // Enum types - field access returns ANY (dynamic variant access)
                HirType::Enum { .. } => Ok((0, TypeId::ANY)),
                // Tuple types — numeric field access (.0, .1, ...)
                HirType::Tuple(element_types) => {
                    if let Ok(idx) = field.parse::<usize>() {
                        let elem_ty = element_types.get(idx).copied().unwrap_or(TypeId::ANY);
                        Ok((idx, elem_ty))
                    } else if self.lenient_types {
                        Ok((0, TypeId::ANY))
                    } else {
                        Err(LowerError::CannotInferFieldType {
                            struct_name: "Tuple".to_string(),
                            field: field.to_string(),
                            available_fields: (0..element_types.len()).map(|i| i.to_string()).collect(),
                        })
                    }
                }
                HirType::LabeledTuple(fields) => {
                    if let Ok(idx) = field.parse::<usize>() {
                        let elem_ty = fields.get(idx).map(|(_, ty)| *ty).unwrap_or(TypeId::ANY);
                        Ok((idx, elem_ty))
                    } else if let Some((idx, (_, field_ty))) =
                        fields.iter().enumerate().find(|(_, (name, _))| name == field)
                    {
                        Ok((idx, *field_ty))
                    } else if self.lenient_types {
                        Ok((0, TypeId::ANY))
                    } else {
                        Err(LowerError::CannotInferFieldType {
                            struct_name: "Tuple".to_string(),
                            field: field.to_string(),
                            available_fields: fields.iter().map(|(name, _)| name.clone()).collect(),
                        })
                    }
                }
                _ => {
                    // For VOID, Pointer, or other non-struct types (often caused by
                    // cross-module imports where field types resolve to VOID because
                    // the dependency wasn't loaded yet), search known structs for
                    // a matching field name — same heuristic as the ANY case.
                    if self.lenient_types {
                        // First: search local type registry
                        let mut best: Option<(usize, TypeId, usize)> = None;
                        for (_, hty) in self.module.types.iter() {
                            match hty {
                                HirType::Struct { fields, .. } => {
                                    for (idx, (fname, fty)) in fields.iter().enumerate() {
                                        if fname == field {
                                            let count = fields.len();
                                            if best.as_ref().is_none_or(|(_, _, c)| count > *c) {
                                                best = Some((idx, *fty, count));
                                            }
                                        }
                                    }
                                }
                                HirType::Bitfield { fields, .. } => {
                                    for (idx, f) in fields.iter().enumerate() {
                                        if f.name == field {
                                            let count = fields.len();
                                            if best.as_ref().is_none_or(|(_, _, c)| count > *c) {
                                                best = Some((idx, f.ty, count));
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                        if let Some((idx, ty, _)) = best {
                            return Ok((idx, ty));
                        }
                        // Search global struct definitions from other modules.
                        // Skip ambiguous names — see the ANY branch above.
                        if self.is_ambiguous_global_field(field) {
                            return Err(LowerError::CannotInferFieldType {
                                struct_name: "wildcard".to_string(),
                                field: field.to_string(),
                                available_fields: vec![],
                            });
                        }
                        if let Some(ref global_defs) = self.global_struct_defs {
                            let mut best_global: Option<(usize, usize, String)> = None;
                            for (sname, fields) in global_defs.iter() {
                                for (idx, (fname, _)) in fields.iter().enumerate() {
                                    if fname == field {
                                        let count = fields.len();
                                        if best_global.as_ref().is_none_or(|(_, c, _)| count > *c) {
                                            best_global = Some((idx, count, sname.clone()));
                                        }
                                    }
                                }
                            }
                            if let Some((idx, count, sname)) = best_global {
                                if std::env::var("SIMPLE_TRACE_FIELD_GET").is_ok() {
                                    let fpath = self
                                        .current_file
                                        .as_ref()
                                        .and_then(|p| p.file_name())
                                        .and_then(|n| n.to_str())
                                        .unwrap_or("unknown");
                                    eprintln!(
                                        "[FIELD-TRACE] wildcard/{field} -> global {sname}[{idx}] (count={count}) in {fpath}"
                                    );
                                }
                                let _ = count;
                                let _ = sname;
                                return Ok((idx, TypeId::ANY));
                            }
                        }
                    }
                    Err(LowerError::CannotInferFieldType {
                        struct_name: format!("{:?}", hir_ty),
                        field: field.to_string(),
                        available_fields: vec![],
                    })
                }
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
                HirType::LabeledTuple(fields) => fields
                    .first()
                    .map(|(_, ty)| *ty)
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
                _ => {
                    if self.lenient_types {
                        Ok(TypeId::ANY)
                    } else {
                        Err(LowerError::CannotInferIndexType(format!("{:?}", hir_ty)))
                    }
                }
            }
        } else if self.lenient_types {
            Ok(TypeId::ANY)
        } else {
            Err(LowerError::CannotInferIndexType(format!("TypeId({:?})", arr_ty)))
        }
    }
}
