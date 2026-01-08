//! Analyzed symbol representation

use std::collections::{HashMap, HashSet};

use super::types::{RefKind, SymbolVisibility};

pub struct AnalyzedSymbol {
    /// Symbol name.
    pub name: String,
    /// Symbol visibility.
    pub visibility: SymbolVisibility,
    /// Estimated size in bytes.
    pub size: usize,
    /// Symbols this symbol references.
    pub references: HashSet<String>,
    /// Reference kinds.
    pub ref_kinds: HashMap<String, RefKind>,
    /// Whether this symbol is reachable from an entry point.
    pub is_reachable: bool,
    /// Group ID for cache locality optimization.
    pub group_id: Option<u32>,
    /// Section name (e.g., ".text", ".data").
    pub section: String,
}

impl AnalyzedSymbol {
    /// Create a new analyzed symbol.
    pub fn new(name: String, visibility: SymbolVisibility) -> Self {
        Self {
            name,
            visibility,
            size: 0,
            references: HashSet::new(),
            ref_kinds: HashMap::new(),
            is_reachable: false,
            group_id: None,
            section: ".text".to_string(),
        }
    }

    /// Add a reference to another symbol.
    pub fn add_reference(&mut self, target: String, kind: RefKind) {
        self.references.insert(target.clone());
        self.ref_kinds.insert(target, kind);
    }

    /// Check if symbol is exported.
    pub fn is_exported(&self) -> bool {
        self.visibility == SymbolVisibility::Export
    }

    /// Check if symbol is imported.
    pub fn is_imported(&self) -> bool {
        self.visibility == SymbolVisibility::Import
    }

    /// Check if symbol is local.
    pub fn is_local(&self) -> bool {
        self.visibility == SymbolVisibility::Local
    }
}

/// Statistics from symbol analysis.
#[derive(Debug, Clone, Default)]
