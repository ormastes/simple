//! Core method registry structures.

use std::collections::HashMap;
use std::sync::LazyLock;

/// Information about a built-in method.
#[derive(Debug, Clone)]
pub struct MethodInfo {
    /// Method name (e.g., "push", "len")
    pub name: &'static str,
    /// Corresponding runtime function name
    pub runtime_fn: RuntimeFn,
    /// Parameter count (excluding receiver)
    pub param_count: usize,
    /// Whether the method mutates the receiver
    pub is_mutating: bool,
    /// Brief description for error messages
    pub description: &'static str,
}

/// Runtime function specification.
#[derive(Debug, Clone)]
pub enum RuntimeFn {
    /// Simple runtime function with name
    Simple(&'static str),
    /// Runtime function with specific signature info
    WithSignature {
        name: &'static str,
        /// Number of pointer-sized arguments (including receiver)
        arg_count: usize,
        /// Returns a value (vs void)
        has_return: bool,
    },
    /// Method is implemented inline (no runtime call)
    Inline,
}

impl RuntimeFn {
    /// Get the runtime function name, if any.
    pub fn name(&self) -> Option<&'static str> {
        match self {
            RuntimeFn::Simple(name) => Some(name),
            RuntimeFn::WithSignature { name, .. } => Some(name),
            RuntimeFn::Inline => None,
        }
    }
}

/// Registry of all built-in methods.
///
/// Uses a nested HashMap structure for efficient lookup with borrowed strings.
pub struct MethodRegistry {
    /// Methods indexed by type_name -> method_name -> info
    methods: HashMap<&'static str, HashMap<&'static str, MethodInfo>>,
}

impl MethodRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self {
            methods: HashMap::new(),
        }
    }

    /// Register a method.
    pub fn register(&mut self, type_name: &'static str, info: MethodInfo) {
        let method_name = info.name;
        self.methods
            .entry(type_name)
            .or_insert_with(HashMap::new)
            .insert(method_name, info);
    }

    /// Look up a method by type and name.
    pub fn get(&self, type_name: &str, method_name: &str) -> Option<&MethodInfo> {
        self.methods
            .get(type_name)
            .and_then(|type_methods| type_methods.get(method_name))
    }

    /// Get all methods for a type.
    pub fn methods_for_type(&self, type_name: &str) -> Option<Vec<&'static str>> {
        self.methods
            .get(type_name)
            .map(|type_methods| type_methods.keys().copied().collect())
    }

    /// Get the runtime function name for a method.
    pub fn runtime_fn(&self, type_name: &str, method_name: &str) -> Option<&'static str> {
        self.get(type_name, method_name).and_then(|info| info.runtime_fn.name())
    }

    /// Check if a method exists for a type.
    pub fn has_method(&self, type_name: &str, method_name: &str) -> bool {
        self.get(type_name, method_name).is_some()
    }

    /// Check if a method mutates its receiver.
    pub fn is_mutating(&self, type_name: &str, method_name: &str) -> bool {
        self.get(type_name, method_name)
            .map(|info| info.is_mutating)
            .unwrap_or(false)
    }

    /// Get all registered type names.
    pub fn type_names(&self) -> Vec<&'static str> {
        self.methods.keys().copied().collect()
    }
}

impl Default for MethodRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Global method registry initialized with all built-in methods.
pub static GLOBAL_REGISTRY: LazyLock<MethodRegistry> = LazyLock::new(|| {
    let mut registry = MethodRegistry::new();

    // Register array methods
    for info in super::builtins::ARRAY_METHODS.iter() {
        registry.register("Array", info.clone());
    }

    // Register dict methods
    for info in super::builtins::DICT_METHODS.iter() {
        registry.register("Dict", info.clone());
    }

    // Register string methods
    for info in super::builtins::STRING_METHODS.iter() {
        registry.register("String", info.clone());
    }

    // Register tuple methods
    for info in super::builtins::TUPLE_METHODS.iter() {
        registry.register("Tuple", info.clone());
    }

    // Register option methods
    for info in super::builtins::OPTION_METHODS.iter() {
        registry.register("Option", info.clone());
    }

    // Register int methods
    for info in super::builtins::INT_METHODS.iter() {
        registry.register("Int", info.clone());
    }

    // Register float methods
    for info in super::builtins::FLOAT_METHODS.iter() {
        registry.register("Float", info.clone());
    }

    registry
});

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_lookup() {
        let registry = &*GLOBAL_REGISTRY;

        // Array methods
        assert!(registry.has_method("Array", "push"));
        assert!(registry.has_method("Array", "len"));
        assert!(registry.has_method("Array", "pop"));
        assert!(!registry.has_method("Array", "nonexistent"));

        // Dict methods
        assert!(registry.has_method("Dict", "keys"));
        assert!(registry.has_method("Dict", "values"));
        assert!(registry.has_method("Dict", "len"));

        // String methods
        assert!(registry.has_method("String", "len"));
        assert!(registry.has_method("String", "concat"));
    }

    #[test]
    fn test_runtime_fn_lookup() {
        let registry = &*GLOBAL_REGISTRY;

        assert_eq!(registry.runtime_fn("Array", "push"), Some("rt_array_push"));
        assert_eq!(registry.runtime_fn("Array", "len"), Some("rt_array_len"));
        assert_eq!(registry.runtime_fn("Dict", "keys"), Some("rt_dict_keys"));
    }

    #[test]
    fn test_mutating_methods() {
        let registry = &*GLOBAL_REGISTRY;

        assert!(registry.is_mutating("Array", "push"));
        assert!(registry.is_mutating("Array", "pop"));
        assert!(registry.is_mutating("Array", "clear"));
        assert!(!registry.is_mutating("Array", "len"));
        assert!(!registry.is_mutating("Array", "get"));
    }

    #[test]
    fn test_methods_for_type() {
        let registry = &*GLOBAL_REGISTRY;

        let array_methods = registry.methods_for_type("Array").unwrap();
        assert!(array_methods.contains(&"push"));
        assert!(array_methods.contains(&"len"));
        assert!(array_methods.contains(&"pop"));
    }

    #[test]
    fn test_get_method_info() {
        let registry = &*GLOBAL_REGISTRY;

        let push_info = registry.get("Array", "push").unwrap();
        assert_eq!(push_info.name, "push");
        assert_eq!(push_info.param_count, 1);
        assert!(push_info.is_mutating);

        let len_info = registry.get("Array", "len").unwrap();
        assert_eq!(len_info.name, "len");
        assert_eq!(len_info.param_count, 0);
        assert!(!len_info.is_mutating);
    }

    #[test]
    fn test_type_names() {
        let registry = &*GLOBAL_REGISTRY;
        let types = registry.type_names();

        assert!(types.contains(&"Array"));
        assert!(types.contains(&"Dict"));
        assert!(types.contains(&"String"));
        assert!(types.contains(&"Int"));
        assert!(types.contains(&"Float"));
    }
}
