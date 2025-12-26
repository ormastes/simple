//! Monomorphization tracking table.

use super::types::{ConcreteType, SpecializationKey};
use simple_parser::ast::{ClassDef, FunctionDef, StructDef};
use std::collections::{HashMap, HashSet, VecDeque};

/// Tracks specializations needed and generated.
#[derive(Debug, Default)]
pub struct MonomorphizationTable {
    /// Functions that need to be specialized
    pending_functions: VecDeque<(SpecializationKey, FunctionDef)>,

    /// Structs that need to be specialized
    pending_structs: VecDeque<(SpecializationKey, StructDef)>,

    /// Classes that need to be specialized
    pending_classes: VecDeque<(SpecializationKey, ClassDef)>,

    /// Already specialized functions (key -> specialized def)
    specialized_functions: HashMap<SpecializationKey, FunctionDef>,

    /// Already specialized structs
    specialized_structs: HashMap<SpecializationKey, StructDef>,

    /// Already specialized classes
    specialized_classes: HashMap<SpecializationKey, ClassDef>,

    /// Keys that have been processed (to avoid infinite loops)
    pub(super) processed: HashSet<SpecializationKey>,
}

impl MonomorphizationTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Request a function specialization.
    ///
    /// Returns the mangled name for the specialization.
    pub fn request_function(
        &mut self,
        name: &str,
        type_args: Vec<ConcreteType>,
        original: &FunctionDef,
    ) -> String {
        let key = SpecializationKey::new(name, type_args);

        if !self.processed.contains(&key) && !self.specialized_functions.contains_key(&key) {
            self.pending_functions
                .push_back((key.clone(), original.clone()));
        }

        key.mangled_name()
    }

    /// Request a struct specialization.
    pub fn request_struct(
        &mut self,
        name: &str,
        type_args: Vec<ConcreteType>,
        original: &StructDef,
    ) -> String {
        let key = SpecializationKey::new(name, type_args);

        if !self.processed.contains(&key) && !self.specialized_structs.contains_key(&key) {
            self.pending_structs
                .push_back((key.clone(), original.clone()));
        }

        key.mangled_name()
    }

    /// Request a class specialization.
    pub fn request_class(
        &mut self,
        name: &str,
        type_args: Vec<ConcreteType>,
        original: &ClassDef,
    ) -> String {
        let key = SpecializationKey::new(name, type_args);

        if !self.processed.contains(&key) && !self.specialized_classes.contains_key(&key) {
            self.pending_classes
                .push_back((key.clone(), original.clone()));
        }

        key.mangled_name()
    }

    /// Check if there are pending specializations.
    pub fn has_pending(&self) -> bool {
        !self.pending_functions.is_empty()
            || !self.pending_structs.is_empty()
            || !self.pending_classes.is_empty()
    }

    /// Get the next pending function to specialize.
    pub fn pop_pending_function(&mut self) -> Option<(SpecializationKey, FunctionDef)> {
        self.pending_functions.pop_front()
    }

    /// Get the next pending struct to specialize.
    pub fn pop_pending_struct(&mut self) -> Option<(SpecializationKey, StructDef)> {
        self.pending_structs.pop_front()
    }

    /// Get the next pending class to specialize.
    pub fn pop_pending_class(&mut self) -> Option<(SpecializationKey, ClassDef)> {
        self.pending_classes.pop_front()
    }

    /// Mark a key as processed.
    pub fn mark_processed(&mut self, key: &SpecializationKey) {
        self.processed.insert(key.clone());
    }

    /// Add a specialized function.
    pub fn add_specialized_function(&mut self, key: SpecializationKey, func: FunctionDef) {
        self.specialized_functions.insert(key, func);
    }

    /// Add a specialized struct.
    pub fn add_specialized_struct(&mut self, key: SpecializationKey, s: StructDef) {
        self.specialized_structs.insert(key, s);
    }

    /// Add a specialized class.
    pub fn add_specialized_class(&mut self, key: SpecializationKey, c: ClassDef) {
        self.specialized_classes.insert(key, c);
    }

    /// Get a specialized function by key.
    pub fn get_specialized_function(&self, key: &SpecializationKey) -> Option<&FunctionDef> {
        self.specialized_functions.get(key)
    }

    /// Get all specialized functions.
    pub fn specialized_functions(
        &self,
    ) -> impl Iterator<Item = (&SpecializationKey, &FunctionDef)> {
        self.specialized_functions.iter()
    }

    /// Get all specialized structs.
    pub fn specialized_structs(&self) -> impl Iterator<Item = (&SpecializationKey, &StructDef)> {
        self.specialized_structs.iter()
    }

    /// Get all specialized classes.
    pub fn specialized_classes(&self) -> impl Iterator<Item = (&SpecializationKey, &ClassDef)> {
        self.specialized_classes.iter()
    }
}
