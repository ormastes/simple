//! Monomorphization metadata for tracking generic specializations.
//!
//! This module provides data structures to track:
//! - Generic template definitions (functions, structs, enums, traits)
//! - Specialization instances and their type bindings
//! - Mapping between templates and specialized instances

use std::collections::HashMap;

use super::types::{ConcreteType, SpecializationKey};

/// Complete monomorphization metadata for a module.
///
/// Stores all generic templates and their specializations for serialization to .smf files.
#[derive(Debug, Clone)]
pub struct MonomorphizationMetadata {
    /// Generic function templates and their specializations
    pub functions: HashMap<String, GenericFunctionMeta>,
    /// Generic struct templates and their specializations
    pub structs: HashMap<String, GenericStructMeta>,
    /// Generic enum templates and their specializations
    pub enums: HashMap<String, GenericEnumMeta>,
    /// Generic trait templates and their implementations
    pub traits: HashMap<String, GenericTraitMeta>,
}

impl MonomorphizationMetadata {
    /// Create a new empty metadata collection
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            structs: HashMap::new(),
            enums: HashMap::new(),
            traits: HashMap::new(),
        }
    }

    /// Check if metadata is empty (no generic constructs)
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty() && self.structs.is_empty() && self.enums.is_empty() && self.traits.is_empty()
    }
}

impl Default for MonomorphizationMetadata {
    fn default() -> Self {
        Self::new()
    }
}

/// Metadata for a generic function template
#[derive(Debug, Clone)]
pub struct GenericFunctionMeta {
    /// Base name of the generic function (before mangling)
    pub base_name: String,
    /// Generic type parameter names (e.g., ["T", "U"])
    pub generic_params: Vec<String>,
    /// All specializations generated for this function
    pub specializations: Vec<SpecializationEntry>,
}

impl GenericFunctionMeta {
    pub fn new(base_name: String, generic_params: Vec<String>) -> Self {
        Self {
            base_name,
            generic_params,
            specializations: Vec::new(),
        }
    }
}

/// Metadata for a generic struct template
#[derive(Debug, Clone)]
pub struct GenericStructMeta {
    /// Base name of the generic struct (before mangling)
    pub base_name: String,
    /// Generic type parameter names (e.g., ["T", "U"])
    pub generic_params: Vec<String>,
    /// All specializations generated for this struct
    pub specializations: Vec<SpecializationEntry>,
}

impl GenericStructMeta {
    pub fn new(base_name: String, generic_params: Vec<String>) -> Self {
        Self {
            base_name,
            generic_params,
            specializations: Vec::new(),
        }
    }
}

/// Metadata for a generic enum template
#[derive(Debug, Clone)]
pub struct GenericEnumMeta {
    /// Base name of the generic enum (before mangling)
    pub base_name: String,
    /// Generic type parameter names (e.g., ["T", "E"])
    pub generic_params: Vec<String>,
    /// All specializations generated for this enum
    pub specializations: Vec<SpecializationEntry>,
}

impl GenericEnumMeta {
    pub fn new(base_name: String, generic_params: Vec<String>) -> Self {
        Self {
            base_name,
            generic_params,
            specializations: Vec::new(),
        }
    }
}

/// Metadata for a generic trait template
#[derive(Debug, Clone)]
pub struct GenericTraitMeta {
    /// Base name of the generic trait (before mangling)
    pub base_name: String,
    /// Generic type parameter names (e.g., ["T"])
    pub generic_params: Vec<String>,
    /// All trait implementations for this generic trait
    pub impl_specializations: Vec<TraitImplEntry>,
}

impl GenericTraitMeta {
    pub fn new(base_name: String, generic_params: Vec<String>) -> Self {
        Self {
            base_name,
            generic_params,
            impl_specializations: Vec::new(),
        }
    }
}

/// A single specialization instance
#[derive(Debug, Clone)]
pub struct SpecializationEntry {
    /// Concrete type arguments (e.g., [Int, String])
    pub type_args: Vec<ConcreteType>,
    /// Mangled name of the specialized instance (e.g., "identity$Int")
    pub mangled_name: String,
    /// Type parameter bindings (e.g., T -> Int, U -> String)
    pub bindings: HashMap<String, ConcreteType>,
    // TODO: Add optimization_level field for future profile-guided optimization
    // pub optimization_level: OptimizationLevel,
}

impl SpecializationEntry {
    /// Create a new specialization entry from a key
    pub fn from_key(key: &SpecializationKey) -> Self {
        let bindings = HashMap::new(); // Will be filled later
        Self {
            type_args: key.type_args.clone(),
            mangled_name: key.mangled_name(),
            bindings,
        }
    }

    /// Create a specialization entry with explicit bindings
    pub fn new(type_args: Vec<ConcreteType>, mangled_name: String, bindings: HashMap<String, ConcreteType>) -> Self {
        Self {
            type_args,
            mangled_name,
            bindings,
        }
    }
}

/// Trait implementation entry
#[derive(Debug, Clone)]
pub struct TraitImplEntry {
    /// Trait name (possibly generic, e.g., "Iterator<T>")
    pub trait_name: String,
    /// Concrete type arguments for the trait (e.g., [Int])
    pub type_args: Vec<ConcreteType>,
    /// The type this trait is implemented for
    pub impl_for_type: String,
    /// Mangled name of the implementation (e.g., "Iterator$Int_impl_for_List$Int")
    pub mangled_name: String,
}

impl TraitImplEntry {
    pub fn new(trait_name: String, type_args: Vec<ConcreteType>, impl_for_type: String, mangled_name: String) -> Self {
        Self {
            trait_name,
            type_args,
            impl_for_type,
            mangled_name,
        }
    }
}
