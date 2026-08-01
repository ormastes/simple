#[path = "../../common/src/runtime_symbols.rs"]
mod runtime_symbols;

pub use runtime_symbols::{
    AbiVersion, CORE_REQUIRED_RUNTIME_SYMBOLS, RUNTIME_SYMBOL_NAMES, RuntimeSymbolClass, RuntimeSymbolProvider,
    RuntimeSymbolTier, runtime_symbols_for_baremetal, symbol_class_of, symbol_tier_of,
};

use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeSymbolEntry {
    pub name: &'static str,
    pub ptr: *const u8,
}

impl RuntimeSymbolEntry {
    pub const fn new(name: &'static str, ptr: *const u8) -> Self {
        Self { name, ptr }
    }
}

unsafe impl Send for RuntimeSymbolEntry {}
unsafe impl Sync for RuntimeSymbolEntry {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeSymbolRegistrationError {
    AlreadyRegistered,
}

static REGISTERED_STATIC_RUNTIME_SYMBOLS: OnceLock<&'static [RuntimeSymbolEntry]> = OnceLock::new();

pub fn register_static_runtime_symbols(
    entries: &'static [RuntimeSymbolEntry],
) -> Result<(), RuntimeSymbolRegistrationError> {
    REGISTERED_STATIC_RUNTIME_SYMBOLS
        .set(entries)
        .map_err(|_| RuntimeSymbolRegistrationError::AlreadyRegistered)
}

pub fn registered_static_runtime_symbols() -> &'static [RuntimeSymbolEntry] {
    REGISTERED_STATIC_RUNTIME_SYMBOLS.get().copied().unwrap_or(&[])
}

pub fn lookup_registered_static_runtime_symbol(name: &str) -> Option<*const u8> {
    registered_static_runtime_symbols()
        .iter()
        .find(|entry| entry.name == name)
        .map(|entry| entry.ptr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unregistered_lookup_returns_none() {
        assert!(lookup_registered_static_runtime_symbol("rt_array_new").is_none());
    }
}
