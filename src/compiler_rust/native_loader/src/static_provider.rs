//! Static symbol provider - runtime functions registered into the process.
//!
//! The actual symbol table is owned by `simple-runtime` and published through
//! `simple-runtime-abi`, which lets this crate avoid a normal dependency on
//! the runtime implementation.

use simple_runtime_abi::{
    AbiVersion,
    RUNTIME_SYMBOL_NAMES,
    RuntimeSymbolProvider,
    lookup_registered_static_runtime_symbol,
};

/// Provides runtime symbols via static linking (compiled into binary).
pub struct StaticSymbolProvider;

impl StaticSymbolProvider {
    /// Create a new static symbol provider.
    pub fn new() -> Self {
        Self
    }
}

impl Default for StaticSymbolProvider {
    fn default() -> Self {
        Self::new()
    }
}

impl RuntimeSymbolProvider for StaticSymbolProvider {
    fn get_symbol(&self, name: &str) -> Option<*const u8> {
        let normalized = name.strip_prefix('_').unwrap_or(name);
        lookup_registered_static_runtime_symbol(normalized)
    }

    fn symbols(&self) -> &[&'static str] {
        RUNTIME_SYMBOL_NAMES
    }

    fn abi_version(&self) -> AbiVersion {
        AbiVersion::CURRENT
    }

    fn name(&self) -> &str {
        "static"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_runtime_abi::{RuntimeSymbolEntry, register_static_runtime_symbols};
    use std::sync::Once;

    extern "C" fn rt_array_new() {}

    extern "C" fn rt_println_value() {}

    extern "C" fn rt_value_int() {}

    extern "C" fn rt_interp_call() {}

    static TEST_RUNTIME_SYMBOLS: &[RuntimeSymbolEntry] = &[
        RuntimeSymbolEntry::new("rt_array_new", rt_array_new as *const u8),
        RuntimeSymbolEntry::new("rt_println_value", rt_println_value as *const u8),
        RuntimeSymbolEntry::new("rt_value_int", rt_value_int as *const u8),
        RuntimeSymbolEntry::new("rt_interp_call", rt_interp_call as *const u8),
    ];

    fn ensure_runtime_registered() {
        static ONCE: Once = Once::new();
        ONCE.call_once(|| {
            let _ = register_static_runtime_symbols(TEST_RUNTIME_SYMBOLS);
        });
    }

    #[test]
    fn test_static_provider_has_symbols() {
        ensure_runtime_registered();
        let provider = StaticSymbolProvider::new();

        assert!(provider.get_symbol("rt_array_new").is_some());
        assert!(provider.get_symbol("_rt_array_new").is_some());
        assert!(provider.get_symbol("rt_println_value").is_some());
        assert!(provider.get_symbol("_rt_println_value").is_some());
        assert!(provider.get_symbol("rt_value_int").is_some());
        assert!(provider.get_symbol("_rt_interp_call").is_some());
        assert!(provider.get_symbol("rt_nonexistent").is_none());
    }

    #[test]
    fn test_static_provider_abi_version() {
        ensure_runtime_registered();
        let provider = StaticSymbolProvider::new();
        assert_eq!(provider.abi_version(), AbiVersion::CURRENT);
    }

    #[test]
    fn test_static_provider_name() {
        ensure_runtime_registered();
        let provider = StaticSymbolProvider::new();
        assert_eq!(provider.name(), "static");
    }
}
