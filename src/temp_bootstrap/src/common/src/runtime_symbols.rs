//! Runtime symbol resolution abstraction.
//!
//! Provides a unified interface for resolving runtime FFI symbols,
//! supporting both static linking (compiled into binary) and dynamic
//! loading (.so/.dylib/.dll).

/// Runtime ABI version for compatibility checking.
///
/// Uses semantic versioning where:
/// - `major`: Breaking changes (signature changes, removed symbols)
/// - `minor`: Additive changes (new symbols only)
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbiVersion {
    pub major: u16,
    pub minor: u16,
}

impl AbiVersion {
    /// Current ABI version of the runtime.
    pub const CURRENT: Self = Self { major: 1, minor: 0 };

    /// Create a new ABI version.
    pub const fn new(major: u16, minor: u16) -> Self {
        Self { major, minor }
    }

    /// Check if this version is compatible with the required version.
    ///
    /// Compatible means:
    /// - Same major version (no breaking changes)
    /// - Same or higher minor version (additive changes OK)
    pub fn is_compatible_with(&self, required: &AbiVersion) -> bool {
        self.major == required.major && self.minor >= required.minor
    }

    /// Create from a packed u32 representation.
    pub fn from_u32(v: u32) -> Self {
        Self {
            major: (v >> 16) as u16,
            minor: (v & 0xFFFF) as u16,
        }
    }

    /// Convert to a packed u32 representation.
    pub fn to_u32(&self) -> u32 {
        ((self.major as u32) << 16) | (self.minor as u32)
    }
}

impl std::fmt::Display for AbiVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.major, self.minor)
    }
}

impl Default for AbiVersion {
    fn default() -> Self {
        Self::CURRENT
    }
}

/// Trait for resolving runtime FFI symbols.
///
/// This trait abstracts over different symbol resolution strategies:
/// - `StaticSymbolProvider`: Compiled-in function pointers (zero runtime cost)
/// - `DynamicSymbolProvider`: Loaded from shared library (.so/.dylib/.dll)
/// - `ChainedProvider`: Multiple providers, first match wins (plugin support)
pub trait RuntimeSymbolProvider: Send + Sync {
    /// Get function pointer for a runtime symbol by name.
    ///
    /// Returns `None` if the symbol is not found.
    fn get_symbol(&self, name: &str) -> Option<*const u8>;

    /// Check if a symbol exists without retrieving it.
    fn has_symbol(&self, name: &str) -> bool {
        self.get_symbol(name).is_some()
    }

    /// Get list of all available symbol names.
    fn symbols(&self) -> &[&'static str];

    /// Get the ABI version of this provider.
    fn abi_version(&self) -> AbiVersion;

    /// Get the provider name (for logging/debugging).
    fn name(&self) -> &str;
}

/// List of all runtime FFI symbols.
///
/// These are the extern "C" functions exported by the runtime library
/// that can be called from compiled Simple code.
pub const RUNTIME_SYMBOL_NAMES: &[&str] = &[
    // Array operations
    "rt_array_new",
    "rt_array_push",
    "rt_array_get",
    "rt_array_set",
    "rt_array_pop",
    "rt_array_clear",
    "rt_array_len",
    // Tuple operations
    "rt_tuple_new",
    "rt_tuple_set",
    "rt_tuple_get",
    "rt_tuple_len",
    // Dict operations
    "rt_dict_new",
    "rt_dict_set",
    "rt_dict_get",
    "rt_dict_len",
    "rt_dict_clear",
    "rt_dict_keys",
    "rt_dict_values",
    // Index/slice operations
    "rt_index_get",
    "rt_index_set",
    "rt_slice",
    "rt_contains",
    // String operations
    "rt_string_new",
    "rt_string_concat",
    // Value creation/conversion
    "rt_value_int",
    "rt_value_float",
    "rt_value_bool",
    "rt_value_nil",
    // Object operations
    "rt_object_new",
    "rt_object_field_get",
    "rt_object_field_set",
    // Closure operations
    "rt_closure_new",
    "rt_closure_set_capture",
    "rt_closure_get_capture",
    "rt_closure_func_ptr",
    // Enum operations
    "rt_enum_new",
    "rt_enum_discriminant",
    "rt_enum_payload",
    // Raw memory allocation
    "rt_alloc",
    "rt_free",
    "rt_ptr_to_value",
    "rt_value_to_ptr",
    // Async/concurrency operations
    "rt_wait",
    "rt_future_new",
    "rt_future_await",
    "rt_actor_spawn",
    "rt_actor_send",
    "rt_actor_recv",
    // Generator operations
    "rt_generator_new",
    "rt_generator_next",
    "rt_generator_get_state",
    "rt_generator_set_state",
    "rt_generator_store_slot",
    "rt_generator_load_slot",
    "rt_generator_get_ctx",
    "rt_generator_mark_done",
    // Interpreter bridge FFI
    "rt_interp_call",
    "rt_interp_eval",
    // Error handling
    "rt_function_not_found",
    "rt_method_not_found",
    // I/O operations
    "rt_print_str",
    "rt_println_str",
    "rt_eprint_str",
    "rt_eprintln_str",
    "rt_print_value",
    "rt_println_value",
    "rt_eprint_value",
    "rt_eprintln_value",
    "rt_capture_stdout_start",
    "rt_capture_stderr_start",
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abi_version_compatibility() {
        let v1_0 = AbiVersion::new(1, 0);
        let v1_1 = AbiVersion::new(1, 1);
        let v2_0 = AbiVersion::new(2, 0);

        // Same version is compatible
        assert!(v1_0.is_compatible_with(&v1_0));

        // Higher minor is compatible
        assert!(v1_1.is_compatible_with(&v1_0));

        // Lower minor is NOT compatible
        assert!(!v1_0.is_compatible_with(&v1_1));

        // Different major is NOT compatible
        assert!(!v2_0.is_compatible_with(&v1_0));
        assert!(!v1_0.is_compatible_with(&v2_0));
    }

    #[test]
    fn test_abi_version_u32_roundtrip() {
        let v = AbiVersion::new(1, 5);
        let packed = v.to_u32();
        let unpacked = AbiVersion::from_u32(packed);
        assert_eq!(v, unpacked);
    }

    #[test]
    fn test_abi_version_display() {
        let v = AbiVersion::new(1, 2);
        assert_eq!(format!("{}", v), "1.2");
    }

    #[test]
    fn test_symbol_list_not_empty() {
        assert!(!RUNTIME_SYMBOL_NAMES.is_empty());
        assert!(RUNTIME_SYMBOL_NAMES.contains(&"rt_array_new"));
        assert!(RUNTIME_SYMBOL_NAMES.contains(&"rt_println_value"));
    }
}
