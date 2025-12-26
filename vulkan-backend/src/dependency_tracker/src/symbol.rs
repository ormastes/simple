//! # Symbol Table
//!
//! This module provides symbol table management for cross-module symbol resolution.
//! It tracks symbols defined in each module, their visibility, and handles
//! import resolution.

use std::collections::HashMap;
use std::path::PathBuf;

use crate::macro_import::SymKind;
use crate::visibility::Visibility;

/// The kind of a symbol entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    /// Function definition
    Function,
    /// Type definition (struct, class, enum)
    Type,
    /// Constant value
    Constant,
    /// Variable
    Variable,
    /// Macro definition
    Macro,
    /// Module
    Module,
}

impl From<SymKind> for SymbolKind {
    fn from(kind: SymKind) -> Self {
        match kind {
            SymKind::ValueOrType => SymbolKind::Function, // Default; caller should specify
            SymKind::Macro => SymbolKind::Macro,
        }
    }
}

impl SymbolKind {
    /// Check if this is a macro.
    pub fn is_macro(&self) -> bool {
        matches!(self, SymbolKind::Macro)
    }

    /// Convert to SymKind for macro import logic.
    pub fn to_sym_kind(&self) -> SymKind {
        if self.is_macro() {
            SymKind::Macro
        } else {
            SymKind::ValueOrType
        }
    }
}

/// A symbol entry in the symbol table.
#[derive(Debug, Clone)]
pub struct SymbolEntry {
    /// The symbol's local name.
    pub name: String,
    /// Fully qualified name (e.g., "crate.sys.http.Router")
    pub qualified_name: String,
    /// The kind of symbol.
    pub kind: SymbolKind,
    /// The visibility of the symbol.
    pub visibility: Visibility,
    /// The source module path.
    pub source_module: String,
    /// The source file (if known).
    pub source_file: Option<PathBuf>,
    /// Whether this symbol was imported (vs. defined locally).
    pub is_imported: bool,
    /// The original name if this was aliased (e.g., `use foo.Bar as Baz`)
    pub original_name: Option<String>,
}

impl SymbolEntry {
    /// Create a new locally-defined symbol.
    pub fn local(
        name: impl Into<String>,
        qualified_name: impl Into<String>,
        kind: SymbolKind,
        visibility: Visibility,
        source_module: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            qualified_name: qualified_name.into(),
            kind,
            visibility,
            source_module: source_module.into(),
            source_file: None,
            is_imported: false,
            original_name: None,
        }
    }

    /// Create an imported symbol.
    pub fn imported(
        name: impl Into<String>,
        qualified_name: impl Into<String>,
        kind: SymbolKind,
        visibility: Visibility,
        source_module: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            qualified_name: qualified_name.into(),
            kind,
            visibility,
            source_module: source_module.into(),
            source_file: None,
            is_imported: true,
            original_name: None,
        }
    }

    /// Create an aliased import (e.g., `use foo.Bar as Baz`).
    pub fn aliased(
        alias: impl Into<String>,
        original: impl Into<String>,
        qualified_name: impl Into<String>,
        kind: SymbolKind,
        visibility: Visibility,
        source_module: impl Into<String>,
    ) -> Self {
        Self {
            name: alias.into(),
            qualified_name: qualified_name.into(),
            kind,
            visibility,
            source_module: source_module.into(),
            source_file: None,
            is_imported: true,
            original_name: Some(original.into()),
        }
    }

    /// Check if this symbol is visible to external modules.
    pub fn is_public(&self) -> bool {
        self.visibility.is_public()
    }

    /// Set the source file.
    pub fn with_source_file(mut self, path: PathBuf) -> Self {
        self.source_file = Some(path);
        self
    }
}

/// A symbol table for a single module.
#[derive(Debug, Clone, Default)]
pub struct SymbolTable {
    /// The module path (e.g., "crate.sys.http")
    pub module_path: String,
    /// Symbols defined in this module, keyed by local name.
    symbols: HashMap<String, SymbolEntry>,
}

impl SymbolTable {
    /// Create a new symbol table for a module.
    pub fn new(module_path: impl Into<String>) -> Self {
        Self {
            module_path: module_path.into(),
            symbols: HashMap::new(),
        }
    }

    /// Define a new symbol in this module.
    pub fn define(&mut self, entry: SymbolEntry) -> Result<(), SymbolConflictError> {
        if let Some(existing) = self.symbols.get(&entry.name) {
            return Err(SymbolConflictError {
                name: entry.name.clone(),
                existing_qualified: existing.qualified_name.clone(),
                new_qualified: entry.qualified_name.clone(),
            });
        }
        self.symbols.insert(entry.name.clone(), entry);
        Ok(())
    }

    /// Define or replace a symbol (for re-exports).
    pub fn define_or_replace(&mut self, entry: SymbolEntry) {
        self.symbols.insert(entry.name.clone(), entry);
    }

    /// Look up a symbol by name.
    pub fn lookup(&self, name: &str) -> Option<&SymbolEntry> {
        self.symbols.get(name)
    }

    /// Get all symbols in this module.
    pub fn all_symbols(&self) -> impl Iterator<Item = &SymbolEntry> {
        self.symbols.values()
    }

    /// Get all public symbols in this module.
    pub fn public_symbols(&self) -> impl Iterator<Item = &SymbolEntry> {
        self.symbols.values().filter(|s| s.is_public())
    }

    /// Get all locally-defined (non-imported) symbols.
    pub fn local_symbols(&self) -> impl Iterator<Item = &SymbolEntry> {
        self.symbols.values().filter(|s| !s.is_imported)
    }

    /// Get all macros.
    pub fn macros(&self) -> impl Iterator<Item = &SymbolEntry> {
        self.symbols.values().filter(|s| s.kind.is_macro())
    }

    /// Get all public non-macro symbols.
    pub fn public_non_macros(&self) -> impl Iterator<Item = &SymbolEntry> {
        self.symbols
            .values()
            .filter(|s| s.is_public() && !s.kind.is_macro())
    }

    /// Get all public macros.
    pub fn public_macros(&self) -> impl Iterator<Item = &SymbolEntry> {
        self.symbols
            .values()
            .filter(|s| s.is_public() && s.kind.is_macro())
    }

    /// Check if a symbol exists.
    pub fn contains(&self, name: &str) -> bool {
        self.symbols.contains_key(name)
    }

    /// Get the number of symbols.
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Check if the table is empty.
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    /// Remove a symbol.
    pub fn remove(&mut self, name: &str) -> Option<SymbolEntry> {
        self.symbols.remove(name)
    }
}

/// Error when a symbol is already defined.
#[derive(Debug, Clone, thiserror::Error)]
#[error("Symbol '{name}' already defined as '{existing_qualified}', cannot redefine as '{new_qualified}'")]
pub struct SymbolConflictError {
    pub name: String,
    pub existing_qualified: String,
    pub new_qualified: String,
}

/// A collection of symbol tables for all modules in a project.
#[derive(Debug, Clone, Default)]
pub struct ProjectSymbols {
    /// Symbol tables keyed by module path.
    tables: HashMap<String, SymbolTable>,
}

impl ProjectSymbols {
    /// Create a new empty project symbol collection.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get or create a symbol table for a module.
    pub fn get_or_create(&mut self, module_path: &str) -> &mut SymbolTable {
        self.tables
            .entry(module_path.to_string())
            .or_insert_with(|| SymbolTable::new(module_path))
    }

    /// Get a symbol table for a module.
    pub fn get(&self, module_path: &str) -> Option<&SymbolTable> {
        self.tables.get(module_path)
    }

    /// Get a mutable symbol table for a module.
    pub fn get_mut(&mut self, module_path: &str) -> Option<&mut SymbolTable> {
        self.tables.get_mut(module_path)
    }

    /// Look up a fully qualified symbol (e.g., "crate.sys.http.Router").
    pub fn lookup_qualified(&self, qualified_name: &str) -> Option<&SymbolEntry> {
        // Parse the qualified name to find the module and symbol
        if let Some(dot_pos) = qualified_name.rfind('.') {
            let module_path = &qualified_name[..dot_pos];
            let symbol_name = &qualified_name[dot_pos + 1..];
            self.tables
                .get(module_path)
                .and_then(|t| t.lookup(symbol_name))
        } else {
            None
        }
    }

    /// Get all module paths.
    pub fn module_paths(&self) -> impl Iterator<Item = &str> {
        self.tables.keys().map(|s| s.as_str())
    }

    /// Get all symbol tables.
    pub fn all_tables(&self) -> impl Iterator<Item = (&str, &SymbolTable)> {
        self.tables.iter().map(|(k, v)| (k.as_str(), v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbol_table_define_and_lookup() {
        let mut table = SymbolTable::new("crate.foo");

        let entry = SymbolEntry::local(
            "Bar",
            "crate.foo.Bar",
            SymbolKind::Type,
            Visibility::Public,
            "crate.foo",
        );

        assert!(table.define(entry).is_ok());
        assert!(table.contains("Bar"));

        let looked_up = table.lookup("Bar").unwrap();
        assert_eq!(looked_up.qualified_name, "crate.foo.Bar");
    }

    #[test]
    fn symbol_table_conflict() {
        let mut table = SymbolTable::new("crate.foo");

        let entry1 = SymbolEntry::local(
            "Bar",
            "crate.foo.Bar",
            SymbolKind::Type,
            Visibility::Public,
            "crate.foo",
        );

        let entry2 = SymbolEntry::local(
            "Bar",
            "crate.foo.Bar2",
            SymbolKind::Function,
            Visibility::Public,
            "crate.foo",
        );

        assert!(table.define(entry1).is_ok());
        assert!(table.define(entry2).is_err());
    }

    #[test]
    fn symbol_table_public_symbols() {
        let mut table = SymbolTable::new("crate.foo");

        table.define_or_replace(SymbolEntry::local(
            "Public",
            "crate.foo.Public",
            SymbolKind::Function,
            Visibility::Public,
            "crate.foo",
        ));

        table.define_or_replace(SymbolEntry::local(
            "Private",
            "crate.foo.Private",
            SymbolKind::Function,
            Visibility::Private,
            "crate.foo",
        ));

        let public: Vec<_> = table.public_symbols().collect();
        assert_eq!(public.len(), 1);
        assert_eq!(public[0].name, "Public");
    }

    #[test]
    fn project_symbols_lookup_qualified() {
        let mut project = ProjectSymbols::new();

        {
            let table = project.get_or_create("crate.foo");
            table.define_or_replace(SymbolEntry::local(
                "Bar",
                "crate.foo.Bar",
                SymbolKind::Type,
                Visibility::Public,
                "crate.foo",
            ));
        }

        let result = project.lookup_qualified("crate.foo.Bar");
        assert!(result.is_some());
        assert_eq!(result.unwrap().name, "Bar");
    }

    #[test]
    fn symbol_kinds() {
        assert!(SymbolKind::Macro.is_macro());
        assert!(!SymbolKind::Function.is_macro());
        assert!(!SymbolKind::Type.is_macro());

        assert_eq!(SymbolKind::Macro.to_sym_kind(), SymKind::Macro);
        assert_eq!(SymbolKind::Function.to_sym_kind(), SymKind::ValueOrType);
    }

    #[test]
    fn aliased_import() {
        let entry = SymbolEntry::aliased(
            "MyBar",
            "Bar",
            "crate.foo.Bar",
            SymbolKind::Type,
            Visibility::Public,
            "crate.foo",
        );

        assert_eq!(entry.name, "MyBar");
        assert_eq!(entry.original_name, Some("Bar".to_string()));
        assert!(entry.is_imported);
    }
}
