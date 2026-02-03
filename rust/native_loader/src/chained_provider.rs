//! Chained symbol provider - supports multiple libraries (plugins).
//!
//! Chains multiple providers together, with first-match-wins semantics.
//! This enables plugin support where custom libraries can override
//! or extend the base runtime symbols.

use simple_common::{AbiVersion, RuntimeSymbolProvider, RUNTIME_SYMBOL_NAMES};
use std::sync::Arc;

/// Chains multiple providers together for symbol resolution.
///
/// Symbols are looked up in order - the first provider that has
/// a symbol wins. This enables plugin support where custom libraries
/// can override or extend the base runtime.
///
/// Example use cases:
/// - Plugin systems: load custom libraries before the base runtime
/// - Testing: mock specific functions while using real implementations for others
/// - Extensions: add new FFI functions without modifying the core runtime
pub struct ChainedProvider {
    /// Providers in lookup order (first match wins).
    providers: Vec<Arc<dyn RuntimeSymbolProvider>>,
    /// Cached name for debugging/logging.
    name: String,
}

impl ChainedProvider {
    /// Create a new empty chained provider.
    pub fn new() -> Self {
        Self {
            providers: Vec::new(),
            name: "chained".to_string(),
        }
    }

    /// Create from a list of providers.
    pub fn from_providers(providers: Vec<Arc<dyn RuntimeSymbolProvider>>) -> Self {
        let mut chained = Self::new();
        for provider in providers {
            chained.add(provider);
        }
        chained
    }

    /// Add a provider to the end of the chain (lowest priority).
    pub fn add(&mut self, provider: Arc<dyn RuntimeSymbolProvider>) {
        self.providers.push(provider);
        self.update_name();
    }

    /// Add a provider at the front of the chain (highest priority).
    ///
    /// Use this to add plugins or overrides that should take precedence
    /// over existing providers.
    pub fn add_front(&mut self, provider: Arc<dyn RuntimeSymbolProvider>) {
        self.providers.insert(0, provider);
        self.update_name();
    }

    /// Remove a provider by index.
    pub fn remove(&mut self, index: usize) -> Option<Arc<dyn RuntimeSymbolProvider>> {
        if index < self.providers.len() {
            let provider = self.providers.remove(index);
            self.update_name();
            Some(provider)
        } else {
            None
        }
    }

    /// Get the list of providers.
    pub fn providers(&self) -> &[Arc<dyn RuntimeSymbolProvider>] {
        &self.providers
    }

    /// Check if the chain is empty.
    pub fn is_empty(&self) -> bool {
        self.providers.is_empty()
    }

    /// Get the number of providers in the chain.
    pub fn len(&self) -> usize {
        self.providers.len()
    }

    /// Find which provider has a specific symbol.
    ///
    /// Returns the index and name of the provider that would resolve the symbol.
    pub fn find_provider_for(&self, symbol: &str) -> Option<(usize, &str)> {
        for (i, provider) in self.providers.iter().enumerate() {
            if provider.has_symbol(symbol) {
                return Some((i, provider.name()));
            }
        }
        None
    }

    fn update_name(&mut self) {
        if self.providers.is_empty() {
            self.name = "chained(empty)".to_string();
        } else {
            self.name = format!(
                "chained[{}]",
                self.providers.iter().map(|p| p.name()).collect::<Vec<_>>().join(" -> ")
            );
        }
    }
}

impl Default for ChainedProvider {
    fn default() -> Self {
        Self::new()
    }
}

impl RuntimeSymbolProvider for ChainedProvider {
    fn get_symbol(&self, name: &str) -> Option<*const u8> {
        // First match wins
        for provider in &self.providers {
            if let Some(ptr) = provider.get_symbol(name) {
                return Some(ptr);
            }
        }
        None
    }

    fn symbols(&self) -> &[&'static str] {
        // Return the base symbol list
        // In a more sophisticated implementation, we could compute
        // the union of all provider symbols
        RUNTIME_SYMBOL_NAMES
    }

    fn abi_version(&self) -> AbiVersion {
        // Return the minimum compatible version from all providers
        self.providers
            .iter()
            .map(|p| p.abi_version())
            .min_by_key(|v| (v.major, v.minor))
            .unwrap_or(AbiVersion::CURRENT)
    }

    fn name(&self) -> &str {
        &self.name
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A mock provider for testing
    struct MockProvider {
        name: String,
        symbols: Vec<(&'static str, usize)>,
    }

    // Safety: The pointers in symbols are just test addresses, not actually dereferenced
    unsafe impl Send for MockProvider {}
    unsafe impl Sync for MockProvider {}

    impl MockProvider {
        fn new(name: &str, symbols: Vec<(&'static str, usize)>) -> Self {
            Self {
                name: name.to_string(),
                symbols,
            }
        }
    }

    impl RuntimeSymbolProvider for MockProvider {
        fn get_symbol(&self, name: &str) -> Option<*const u8> {
            self.symbols
                .iter()
                .find(|(n, _)| *n == name)
                .map(|(_, ptr)| *ptr as *const u8)
        }

        fn symbols(&self) -> &[&'static str] {
            RUNTIME_SYMBOL_NAMES
        }

        fn abi_version(&self) -> AbiVersion {
            AbiVersion::CURRENT
        }

        fn name(&self) -> &str {
            &self.name
        }
    }

    #[test]
    fn test_empty_chain() {
        let chain = ChainedProvider::new();
        assert!(chain.is_empty());
        assert_eq!(chain.len(), 0);
        assert!(chain.get_symbol("rt_array_new").is_none());
    }

    #[test]
    fn test_first_match_wins() {
        let ptr1: usize = 0x1000;
        let ptr2: usize = 0x2000;

        let p1 = Arc::new(MockProvider::new("first", vec![("test_sym", ptr1)]));
        let p2 = Arc::new(MockProvider::new("second", vec![("test_sym", ptr2)]));

        let mut chain = ChainedProvider::new();
        chain.add(p1);
        chain.add(p2);

        // First provider wins
        assert_eq!(chain.get_symbol("test_sym"), Some(ptr1 as *const u8));
    }

    #[test]
    fn test_add_front() {
        let ptr1: usize = 0x1000;
        let ptr2: usize = 0x2000;

        let p1 = Arc::new(MockProvider::new("first", vec![("test_sym", ptr1)]));
        let p2 = Arc::new(MockProvider::new("second", vec![("test_sym", ptr2)]));

        let mut chain = ChainedProvider::new();
        chain.add(p1);
        chain.add_front(p2.clone()); // Add p2 at front

        // Now p2 (added to front) should win
        assert_eq!(chain.get_symbol("test_sym"), Some(ptr2 as *const u8));
    }

    #[test]
    fn test_fallback() {
        let ptr1: usize = 0x1000;
        let ptr2: usize = 0x2000;

        let p1 = Arc::new(MockProvider::new("first", vec![("sym_a", ptr1)]));
        let p2 = Arc::new(MockProvider::new("second", vec![("sym_b", ptr2)]));

        let mut chain = ChainedProvider::new();
        chain.add(p1);
        chain.add(p2);

        // Each provider handles different symbols
        assert_eq!(chain.get_symbol("sym_a"), Some(ptr1 as *const u8));
        assert_eq!(chain.get_symbol("sym_b"), Some(ptr2 as *const u8));
        assert!(chain.get_symbol("sym_c").is_none());
    }

    #[test]
    fn test_find_provider_for() {
        let p1 = Arc::new(MockProvider::new("first", vec![("sym_a", 0x1000)]));
        let p2 = Arc::new(MockProvider::new("second", vec![("sym_b", 0x2000)]));

        let mut chain = ChainedProvider::new();
        chain.add(p1);
        chain.add(p2);

        assert_eq!(chain.find_provider_for("sym_a"), Some((0, "first")));
        assert_eq!(chain.find_provider_for("sym_b"), Some((1, "second")));
        assert_eq!(chain.find_provider_for("sym_c"), None);
    }
}
