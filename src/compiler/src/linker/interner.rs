//! Linker Symbol Interning (#814) and Hash Precomputation (#815)
//!
//! Provides efficient symbol interning for the linker using the `lasso` crate.
//! Symbols are interned to reduce memory usage and enable O(1) comparisons
//! during linking operations.
//!
//! Hash precomputation stores pre-calculated hashes alongside symbols for
//! faster lookups in hash tables without re-hashing.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::num::NonZeroUsize;
use std::sync::Arc;

use ahash::AHasher;
use lasso::{Capacity, Rodeo, Spur, ThreadedRodeo};

/// Interned symbol key - a lightweight handle to an interned symbol.
/// Comparing two `SymbolKey` values is O(1) instead of O(n).
pub type SymbolKey = Spur;

/// Thread-local symbol interner for single-threaded linking.
#[derive(Debug)]
pub struct SymbolInterner {
    rodeo: Rodeo,
    /// Mapping from symbol key to section index (for fast lookup).
    section_map: HashMap<SymbolKey, u16>,
    /// Mapping from symbol key to value/offset.
    value_map: HashMap<SymbolKey, u64>,
}

impl SymbolInterner {
    /// Create a new symbol interner.
    pub fn new() -> Self {
        Self {
            rodeo: Rodeo::default(),
            section_map: HashMap::new(),
            value_map: HashMap::new(),
        }
    }

    /// Create with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let bytes = NonZeroUsize::new(capacity * 32).unwrap_or(NonZeroUsize::new(32).unwrap());
        Self {
            rodeo: Rodeo::with_capacity(Capacity::new(capacity, bytes)),
            section_map: HashMap::with_capacity(capacity),
            value_map: HashMap::with_capacity(capacity),
        }
    }

    /// Intern a symbol name, returning a lightweight key.
    #[inline]
    pub fn intern(&mut self, name: &str) -> SymbolKey {
        self.rodeo.get_or_intern(name)
    }

    /// Resolve a key back to the symbol name.
    #[inline]
    pub fn resolve(&self, key: SymbolKey) -> &str {
        self.rodeo.resolve(&key)
    }

    /// Check if a symbol name is already interned.
    #[inline]
    pub fn contains(&self, name: &str) -> bool {
        self.rodeo.contains(name)
    }

    /// Get the key for a symbol if it's already interned.
    #[inline]
    pub fn get(&self, name: &str) -> Option<SymbolKey> {
        self.rodeo.get(name)
    }

    /// Get the number of interned symbols.
    #[inline]
    pub fn len(&self) -> usize {
        self.rodeo.len()
    }

    /// Check if the interner is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.rodeo.is_empty()
    }

    /// Set the section index for a symbol.
    pub fn set_section(&mut self, key: SymbolKey, section: u16) {
        self.section_map.insert(key, section);
    }

    /// Get the section index for a symbol.
    pub fn get_section(&self, key: SymbolKey) -> Option<u16> {
        self.section_map.get(&key).copied()
    }

    /// Set the value/offset for a symbol.
    pub fn set_value(&mut self, key: SymbolKey, value: u64) {
        self.value_map.insert(key, value);
    }

    /// Get the value/offset for a symbol.
    pub fn get_value(&self, key: SymbolKey) -> Option<u64> {
        self.value_map.get(&key).copied()
    }
}

impl Default for SymbolInterner {
    fn default() -> Self {
        Self::new()
    }
}

/// Thread-safe symbol interner for parallel linking.
#[derive(Debug, Clone)]
pub struct SharedSymbolInterner {
    rodeo: Arc<ThreadedRodeo>,
}

impl SharedSymbolInterner {
    /// Create a new shared symbol interner.
    pub fn new() -> Self {
        Self {
            rodeo: Arc::new(ThreadedRodeo::default()),
        }
    }

    /// Create with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let bytes = NonZeroUsize::new(capacity * 32).unwrap_or(NonZeroUsize::new(32).unwrap());
        Self {
            rodeo: Arc::new(ThreadedRodeo::with_capacity(Capacity::new(capacity, bytes))),
        }
    }

    /// Intern a symbol name, returning a lightweight key.
    /// Thread-safe: can be called from multiple threads concurrently.
    #[inline]
    pub fn intern(&self, name: &str) -> SymbolKey {
        self.rodeo.get_or_intern(name)
    }

    /// Resolve a key back to the symbol name.
    #[inline]
    pub fn resolve(&self, key: SymbolKey) -> &str {
        self.rodeo.resolve(&key)
    }

    /// Check if a symbol name is already interned.
    #[inline]
    pub fn contains(&self, name: &str) -> bool {
        self.rodeo.contains(name)
    }

    /// Get the key for a symbol if it's already interned.
    #[inline]
    pub fn get(&self, name: &str) -> Option<SymbolKey> {
        self.rodeo.get(name)
    }

    /// Get the number of interned symbols.
    #[inline]
    pub fn len(&self) -> usize {
        self.rodeo.len()
    }

    /// Check if the interner is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.rodeo.is_empty()
    }
}

impl Default for SharedSymbolInterner {
    fn default() -> Self {
        Self::new()
    }
}

/// Symbol table with interning support.
/// Combines symbol interning with symbol table functionality.
#[derive(Debug)]
pub struct InternedSymbolTable {
    interner: SymbolInterner,
    /// Symbol info indexed by key.
    symbols: HashMap<SymbolKey, SymbolInfo>,
    /// Order in which symbols were added (for deterministic output).
    order: Vec<SymbolKey>,
}

/// Information about a symbol in the symbol table.
#[derive(Debug, Clone)]
pub struct SymbolInfo {
    /// Symbol binding (local, global, weak).
    pub binding: SymbolBinding,
    /// Symbol type (function, object, section, etc.).
    pub sym_type: SymbolType,
    /// Section index.
    pub section_index: u16,
    /// Symbol value/offset.
    pub value: u64,
    /// Symbol size.
    pub size: u64,
}

/// Symbol binding type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolBinding {
    Local,
    Global,
    Weak,
}

/// Symbol type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolType {
    None,
    Object,
    Function,
    Section,
    File,
}

impl InternedSymbolTable {
    /// Create a new interned symbol table.
    pub fn new() -> Self {
        Self {
            interner: SymbolInterner::new(),
            symbols: HashMap::new(),
            order: Vec::new(),
        }
    }

    /// Create with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            interner: SymbolInterner::with_capacity(capacity),
            symbols: HashMap::with_capacity(capacity),
            order: Vec::with_capacity(capacity),
        }
    }

    /// Add a symbol to the table.
    /// Returns the symbol key.
    pub fn add_symbol(&mut self, name: &str, info: SymbolInfo) -> SymbolKey {
        let key = self.interner.intern(name);

        if !self.symbols.contains_key(&key) {
            self.order.push(key);
        }

        self.symbols.insert(key, info);
        key
    }

    /// Look up a symbol by name.
    pub fn lookup(&self, name: &str) -> Option<(SymbolKey, &SymbolInfo)> {
        let key = self.interner.get(name)?;
        let info = self.symbols.get(&key)?;
        Some((key, info))
    }

    /// Look up a symbol by key.
    pub fn get(&self, key: SymbolKey) -> Option<&SymbolInfo> {
        self.symbols.get(&key)
    }

    /// Get a mutable reference to a symbol.
    pub fn get_mut(&mut self, key: SymbolKey) -> Option<&mut SymbolInfo> {
        self.symbols.get_mut(&key)
    }

    /// Resolve a key to its name.
    pub fn resolve(&self, key: SymbolKey) -> &str {
        self.interner.resolve(key)
    }

    /// Iterate over symbols in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = (SymbolKey, &str, &SymbolInfo)> {
        self.order.iter().map(|&key| {
            let name = self.interner.resolve(key);
            let info = self.symbols.get(&key).unwrap();
            (key, name, info)
        })
    }

    /// Get the number of symbols.
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Check if the table is empty.
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    /// Check if a symbol exists.
    pub fn contains(&self, name: &str) -> bool {
        self.interner.contains(name)
    }

    /// Get all global symbols.
    pub fn globals(&self) -> impl Iterator<Item = (SymbolKey, &str, &SymbolInfo)> {
        self.iter().filter(|(_, _, info)| info.binding == SymbolBinding::Global)
    }

    /// Get all undefined symbols (those with no section).
    pub fn undefined(&self) -> impl Iterator<Item = (SymbolKey, &str, &SymbolInfo)> {
        self.iter().filter(|(_, _, info)| info.section_index == 0 && info.sym_type != SymbolType::File)
    }
}

impl Default for InternedSymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Precomputed hash value for a symbol.
/// This allows O(1) hash lookups without re-computing the hash.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrecomputedHash(u64);

impl PrecomputedHash {
    /// Compute a hash for the given string using AHash.
    pub fn compute(s: &str) -> Self {
        let mut hasher = AHasher::default();
        s.hash(&mut hasher);
        Self(hasher.finish())
    }

    /// Get the raw hash value.
    #[inline]
    pub fn value(&self) -> u64 {
        self.0
    }
}

impl Hash for PrecomputedHash {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // The hash is already computed, just use it directly
        state.write_u64(self.0);
    }
}

/// Symbol with precomputed hash for O(1) lookup.
#[derive(Debug, Clone)]
pub struct HashedSymbol {
    /// The interned symbol key.
    pub key: SymbolKey,
    /// Precomputed hash value.
    pub hash: PrecomputedHash,
}

impl HashedSymbol {
    /// Create a new hashed symbol.
    pub fn new(key: SymbolKey, hash: PrecomputedHash) -> Self {
        Self { key, hash }
    }
}

impl PartialEq for HashedSymbol {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Eq for HashedSymbol {}

impl Hash for HashedSymbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

/// Hash table optimized for precomputed hashes.
/// Uses the precomputed hash for bucket selection, avoiding re-hashing.
pub struct PrehashedTable<V> {
    /// The underlying storage - buckets indexed by hash.
    buckets: Vec<Vec<(HashedSymbol, V)>>,
    /// Number of buckets (power of 2).
    bucket_count: usize,
    /// Mask for bucket index calculation.
    bucket_mask: usize,
    /// Total number of entries.
    len: usize,
}

impl<V> PrehashedTable<V> {
    /// Create a new prehashed table with default capacity.
    pub fn new() -> Self {
        Self::with_capacity(256)
    }

    /// Create a new prehashed table with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        // Round up to power of 2
        let bucket_count = capacity.next_power_of_two();
        let mut buckets = Vec::with_capacity(bucket_count);
        for _ in 0..bucket_count {
            buckets.push(Vec::new());
        }

        Self {
            buckets,
            bucket_count,
            bucket_mask: bucket_count - 1,
            len: 0,
        }
    }

    /// Get the bucket index for a hash.
    #[inline]
    fn bucket_index(&self, hash: &PrecomputedHash) -> usize {
        (hash.value() as usize) & self.bucket_mask
    }

    /// Insert a value with a hashed symbol key.
    pub fn insert(&mut self, key: HashedSymbol, value: V) -> Option<V> {
        let bucket_idx = self.bucket_index(&key.hash);
        let bucket = &mut self.buckets[bucket_idx];

        // Check if key already exists
        for (existing_key, existing_value) in bucket.iter_mut() {
            if existing_key.key == key.key {
                let old = std::mem::replace(existing_value, value);
                return Some(old);
            }
        }

        // Insert new entry
        bucket.push((key, value));
        self.len += 1;
        None
    }

    /// Get a value by hashed symbol key.
    pub fn get(&self, key: &HashedSymbol) -> Option<&V> {
        let bucket_idx = self.bucket_index(&key.hash);
        let bucket = &self.buckets[bucket_idx];

        for (existing_key, value) in bucket {
            if existing_key.key == key.key {
                return Some(value);
            }
        }

        None
    }

    /// Get a mutable value by hashed symbol key.
    pub fn get_mut(&mut self, key: &HashedSymbol) -> Option<&mut V> {
        let bucket_idx = self.bucket_index(&key.hash);
        let bucket = &mut self.buckets[bucket_idx];

        for (existing_key, value) in bucket {
            if existing_key.key == key.key {
                return Some(value);
            }
        }

        None
    }

    /// Check if the table contains a key.
    pub fn contains(&self, key: &HashedSymbol) -> bool {
        self.get(key).is_some()
    }

    /// Get the number of entries.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Check if the table is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Iterate over all entries.
    pub fn iter(&self) -> impl Iterator<Item = (&HashedSymbol, &V)> {
        self.buckets
            .iter()
            .flat_map(|bucket| bucket.iter().map(|(k, v)| (k, v)))
    }
}

impl<V> Default for PrehashedTable<V> {
    fn default() -> Self {
        Self::new()
    }
}

/// Symbol interner with hash precomputation.
/// Combines interning with hash caching for maximum performance.
#[derive(Debug)]
pub struct HashedInterner {
    rodeo: Rodeo,
    /// Cached hashes for interned symbols.
    hashes: HashMap<SymbolKey, PrecomputedHash>,
}

impl HashedInterner {
    /// Create a new hashed interner.
    pub fn new() -> Self {
        Self {
            rodeo: Rodeo::default(),
            hashes: HashMap::new(),
        }
    }

    /// Create with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let bytes = NonZeroUsize::new(capacity * 32).unwrap_or(NonZeroUsize::new(32).unwrap());
        Self {
            rodeo: Rodeo::with_capacity(Capacity::new(capacity, bytes)),
            hashes: HashMap::with_capacity(capacity),
        }
    }

    /// Intern a string and return a hashed symbol.
    pub fn intern(&mut self, s: &str) -> HashedSymbol {
        let key = self.rodeo.get_or_intern(s);

        // Get or compute hash
        let hash = self.hashes.entry(key).or_insert_with(|| PrecomputedHash::compute(s));

        HashedSymbol::new(key, *hash)
    }

    /// Get a hashed symbol if already interned.
    pub fn get(&self, s: &str) -> Option<HashedSymbol> {
        let key = self.rodeo.get(s)?;
        let hash = self.hashes.get(&key)?;
        Some(HashedSymbol::new(key, *hash))
    }

    /// Resolve a key to its string.
    #[inline]
    pub fn resolve(&self, key: SymbolKey) -> &str {
        self.rodeo.resolve(&key)
    }

    /// Get the precomputed hash for a key.
    pub fn get_hash(&self, key: SymbolKey) -> Option<PrecomputedHash> {
        self.hashes.get(&key).copied()
    }

    /// Get the number of interned symbols.
    #[inline]
    pub fn len(&self) -> usize {
        self.rodeo.len()
    }

    /// Check if the interner is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.rodeo.is_empty()
    }
}

impl Default for HashedInterner {
    fn default() -> Self {
        Self::new()
    }
}

/// Pre-intern common linker symbols for faster lookup.
pub struct CommonSymbols {
    pub main: SymbolKey,
    pub start: SymbolKey,
    pub init: SymbolKey,
    pub fini: SymbolKey,
    pub text: SymbolKey,
    pub data: SymbolKey,
    pub bss: SymbolKey,
    pub rodata: SymbolKey,
}

impl CommonSymbols {
    /// Pre-intern common symbols.
    pub fn new(interner: &mut SymbolInterner) -> Self {
        Self {
            main: interner.intern("main"),
            start: interner.intern("_start"),
            init: interner.intern("_init"),
            fini: interner.intern("_fini"),
            text: interner.intern(".text"),
            data: interner.intern(".data"),
            bss: interner.intern(".bss"),
            rodata: interner.intern(".rodata"),
        }
    }

    /// Pre-intern common symbols with shared interner.
    pub fn new_shared(interner: &SharedSymbolInterner) -> Self {
        Self {
            main: interner.intern("main"),
            start: interner.intern("_start"),
            init: interner.intern("_init"),
            fini: interner.intern("_fini"),
            text: interner.intern(".text"),
            data: interner.intern(".data"),
            bss: interner.intern(".bss"),
            rodata: interner.intern(".rodata"),
        }
    }
}


#[cfg(test)]
#[path = "interner_tests.rs"]
mod tests;
