//! Partitioning of generic templates and specialized instances.
//!
//! This module separates a monomorphized module into:
//! - Generic templates (for later instantiation)
//! - Specialized instances (compiled to native code)
//!
//! Supports .smf template storage for deferred monomorphization.

use simple_parser::ast::{ClassDef, EnumDef, FunctionDef, Module, Node, StructDef, TraitDef};
use std::collections::HashMap;

use crate::monomorphize::metadata::{
    GenericEnumMeta, GenericFunctionMeta, GenericStructMeta, GenericTraitMeta,
    MonomorphizationMetadata, SpecializationEntry,
};
use crate::monomorphize::types::ConcreteType;

/// Complete set of generic templates extracted from a module.
#[derive(Debug, Clone)]
pub struct GenericTemplates {
    pub functions: Vec<FunctionDef>,
    pub structs: Vec<StructDef>,
    pub classes: Vec<ClassDef>,
    pub enums: Vec<EnumDef>,
    pub traits: Vec<TraitDef>,
}

impl GenericTemplates {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
            structs: Vec::new(),
            classes: Vec::new(),
            enums: Vec::new(),
            traits: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
            && self.structs.is_empty()
            && self.classes.is_empty()
            && self.enums.is_empty()
            && self.traits.is_empty()
    }
}

/// Complete set of specialized instances.
#[derive(Debug, Clone)]
pub struct SpecializedInstances {
    pub functions: Vec<FunctionDef>,
    pub structs: Vec<StructDef>,
    pub classes: Vec<ClassDef>,
    pub enums: Vec<EnumDef>,
    // Trait implementations are tracked in metadata, not as separate instances
}

impl SpecializedInstances {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
            structs: Vec::new(),
            classes: Vec::new(),
            enums: Vec::new(),
        }
    }
}

/// Partition a module into generic templates and specialized instances.
///
/// This is used during compilation to separate:
/// - Templates (stored in .smf for later instantiation)
/// - Specializations (compiled to native code)
///
/// Returns (templates, specialized_instances, metadata)
pub fn partition_generic_constructs(
    module: &Module,
) -> (GenericTemplates, SpecializedInstances, MonomorphizationMetadata) {
    let mut templates = GenericTemplates::new();
    let mut specialized = SpecializedInstances::new();
    let mut metadata = MonomorphizationMetadata::new();

    for item in &module.items {
        match item {
            Node::Function(f) => {
                if f.is_generic_template {
                    // Generic template
                    templates.functions.push(f.clone());

                    // Create metadata entry if not exists
                    if !metadata.functions.contains_key(&f.name) {
                        metadata.functions.insert(
                            f.name.clone(),
                            GenericFunctionMeta::new(f.name.clone(), f.generic_params.clone()),
                        );
                    }
                } else if let Some(base_name) = &f.specialization_of {
                    // Specialized instance
                    specialized.functions.push(f.clone());

                    // Add to metadata
                    let meta = metadata
                        .functions
                        .entry(base_name.clone())
                        .or_insert_with(|| GenericFunctionMeta::new(base_name.clone(), Vec::new()));

                    // Extract type args from bindings
                    let empty_bindings = HashMap::new();
                    let type_args: Vec<ConcreteType> = f
                        .type_bindings
                        .values()
                        .map(|ast_type| crate::monomorphize::util::ast_type_to_concrete(ast_type, &empty_bindings))
                        .collect();

                    meta.specializations.push(SpecializationEntry::new(
                        type_args,
                        f.name.clone(),
                        f.type_bindings
                            .iter()
                            .map(|(k, v)| (k.clone(), crate::monomorphize::util::ast_type_to_concrete(v, &empty_bindings)))
                            .collect(),
                    ));
                } else {
                    // Non-generic function
                    specialized.functions.push(f.clone());
                }
            }

            Node::Struct(s) => {
                if s.is_generic_template {
                    templates.structs.push(s.clone());

                    if !metadata.structs.contains_key(&s.name) {
                        metadata.structs.insert(
                            s.name.clone(),
                            GenericStructMeta::new(s.name.clone(), s.generic_params.clone()),
                        );
                    }
                } else if let Some(base_name) = &s.specialization_of {
                    specialized.structs.push(s.clone());

                    let meta = metadata
                        .structs
                        .entry(base_name.clone())
                        .or_insert_with(|| GenericStructMeta::new(base_name.clone(), Vec::new()));

                    let empty_bindings = HashMap::new();
                    let type_args: Vec<ConcreteType> = s
                        .type_bindings
                        .values()
                        .map(|ast_type| crate::monomorphize::util::ast_type_to_concrete(ast_type, &empty_bindings))
                        .collect();

                    meta.specializations.push(SpecializationEntry::new(
                        type_args,
                        s.name.clone(),
                        s.type_bindings
                            .iter()
                            .map(|(k, v)| (k.clone(), crate::monomorphize::util::ast_type_to_concrete(v, &empty_bindings)))
                            .collect(),
                    ));
                } else {
                    specialized.structs.push(s.clone());
                }
            }

            Node::Class(c) => {
                if c.is_generic_template {
                    templates.classes.push(c.clone());

                    // Classes tracked as structs in metadata
                    if !metadata.structs.contains_key(&c.name) {
                        metadata.structs.insert(
                            c.name.clone(),
                            GenericStructMeta::new(c.name.clone(), c.generic_params.clone()),
                        );
                    }
                } else if let Some(base_name) = &c.specialization_of {
                    specialized.classes.push(c.clone());

                    let meta = metadata
                        .structs
                        .entry(base_name.clone())
                        .or_insert_with(|| GenericStructMeta::new(base_name.clone(), Vec::new()));

                    let empty_bindings = HashMap::new();
                    let type_args: Vec<ConcreteType> = c
                        .type_bindings
                        .values()
                        .map(|ast_type| crate::monomorphize::util::ast_type_to_concrete(ast_type, &empty_bindings))
                        .collect();

                    meta.specializations.push(SpecializationEntry::new(
                        type_args,
                        c.name.clone(),
                        c.type_bindings
                            .iter()
                            .map(|(k, v)| (k.clone(), crate::monomorphize::util::ast_type_to_concrete(v, &empty_bindings)))
                            .collect(),
                    ));
                } else {
                    specialized.classes.push(c.clone());
                }
            }

            Node::Enum(e) => {
                if e.is_generic_template {
                    templates.enums.push(e.clone());

                    if !metadata.enums.contains_key(&e.name) {
                        metadata.enums.insert(
                            e.name.clone(),
                            GenericEnumMeta::new(e.name.clone(), e.generic_params.clone()),
                        );
                    }
                } else if let Some(base_name) = &e.specialization_of {
                    specialized.enums.push(e.clone());

                    let meta = metadata
                        .enums
                        .entry(base_name.clone())
                        .or_insert_with(|| GenericEnumMeta::new(base_name.clone(), Vec::new()));

                    let empty_bindings = HashMap::new();
                    let type_args: Vec<ConcreteType> = e
                        .type_bindings
                        .values()
                        .map(|ast_type| crate::monomorphize::util::ast_type_to_concrete(ast_type, &empty_bindings))
                        .collect();

                    meta.specializations.push(SpecializationEntry::new(
                        type_args,
                        e.name.clone(),
                        e.type_bindings
                            .iter()
                            .map(|(k, v)| (k.clone(), crate::monomorphize::util::ast_type_to_concrete(v, &empty_bindings)))
                            .collect(),
                    ));
                } else {
                    specialized.enums.push(e.clone());
                }
            }

            Node::Trait(t) => {
                if t.is_generic_template {
                    templates.traits.push(t.clone());

                    if !metadata.traits.contains_key(&t.name) {
                        metadata.traits.insert(
                            t.name.clone(),
                            GenericTraitMeta::new(t.name.clone(), t.generic_params.clone()),
                        );
                    }
                } else if t.specialization_of.is_some() {
                    // Trait implementations tracked in metadata only
                    // (not compiled as separate instances)
                } else {
                    // Non-generic trait - keep in templates
                    templates.traits.push(t.clone());
                }
            }

            _ => {
                // Other nodes (imports, constants, etc.) - ignore for partitioning
            }
        }
    }

    (templates, specialized, metadata)
}

/// Build monomorphization metadata from templates and specialized instances.
///
/// This is a convenience function that extracts metadata without doing
/// the full partitioning.
pub fn build_monomorphization_metadata(
    templates: &GenericTemplates,
    specialized: &SpecializedInstances,
) -> MonomorphizationMetadata {
    let mut metadata = MonomorphizationMetadata::new();

    // Add templates
    for func in &templates.functions {
        metadata.functions.insert(
            func.name.clone(),
            GenericFunctionMeta::new(func.name.clone(), func.generic_params.clone()),
        );
    }

    for struct_def in &templates.structs {
        metadata.structs.insert(
            struct_def.name.clone(),
            GenericStructMeta::new(struct_def.name.clone(), struct_def.generic_params.clone()),
        );
    }

    for class_def in &templates.classes {
        metadata.structs.insert(
            class_def.name.clone(),
            GenericStructMeta::new(class_def.name.clone(), class_def.generic_params.clone()),
        );
    }

    for enum_def in &templates.enums {
        metadata.enums.insert(
            enum_def.name.clone(),
            GenericEnumMeta::new(enum_def.name.clone(), enum_def.generic_params.clone()),
        );
    }

    for trait_def in &templates.traits {
        metadata.traits.insert(
            trait_def.name.clone(),
            GenericTraitMeta::new(trait_def.name.clone(), trait_def.generic_params.clone()),
        );
    }

    // Add specializations
    let empty_bindings = HashMap::new();
    for func in &specialized.functions {
        if let Some(base_name) = &func.specialization_of {
            if let Some(meta) = metadata.functions.get_mut(base_name) {
                let type_args: Vec<ConcreteType> = func
                    .type_bindings
                    .values()
                    .map(|ast_type| crate::monomorphize::util::ast_type_to_concrete(ast_type, &empty_bindings))
                    .collect();

                meta.specializations.push(SpecializationEntry::new(
                    type_args,
                    func.name.clone(),
                    func.type_bindings
                        .iter()
                        .map(|(k, v)| (k.clone(), crate::monomorphize::util::ast_type_to_concrete(v, &empty_bindings)))
                        .collect(),
                ));
            }
        }
    }

    // Similar for structs, classes, enums...
    for struct_def in &specialized.structs {
        if let Some(base_name) = &struct_def.specialization_of {
            if let Some(meta) = metadata.structs.get_mut(base_name) {
                let type_args: Vec<ConcreteType> = struct_def
                    .type_bindings
                    .values()
                    .map(|ast_type| crate::monomorphize::util::ast_type_to_concrete(ast_type, &empty_bindings))
                    .collect();

                meta.specializations.push(SpecializationEntry::new(
                    type_args,
                    struct_def.name.clone(),
                    struct_def.type_bindings
                        .iter()
                        .map(|(k, v)| (k.clone(), crate::monomorphize::util::ast_type_to_concrete(v, &empty_bindings)))
                        .collect(),
                ));
            }
        }
    }

    for class_def in &specialized.classes {
        if let Some(base_name) = &class_def.specialization_of {
            if let Some(meta) = metadata.structs.get_mut(base_name) {
                let type_args: Vec<ConcreteType> = class_def
                    .type_bindings
                    .values()
                    .map(|ast_type| crate::monomorphize::util::ast_type_to_concrete(ast_type, &empty_bindings))
                    .collect();

                meta.specializations.push(SpecializationEntry::new(
                    type_args,
                    class_def.name.clone(),
                    class_def.type_bindings
                        .iter()
                        .map(|(k, v)| (k.clone(), crate::monomorphize::util::ast_type_to_concrete(v, &empty_bindings)))
                        .collect(),
                ));
            }
        }
    }

    for enum_def in &specialized.enums {
        if let Some(base_name) = &enum_def.specialization_of {
            if let Some(meta) = metadata.enums.get_mut(base_name) {
                let type_args: Vec<ConcreteType> = enum_def
                    .type_bindings
                    .values()
                    .map(|ast_type| crate::monomorphize::util::ast_type_to_concrete(ast_type, &empty_bindings))
                    .collect();

                meta.specializations.push(SpecializationEntry::new(
                    type_args,
                    enum_def.name.clone(),
                    enum_def.type_bindings
                        .iter()
                        .map(|(k, v)| (k.clone(), crate::monomorphize::util::ast_type_to_concrete(v, &empty_bindings)))
                        .collect(),
                ));
            }
        }
    }

    metadata
}
