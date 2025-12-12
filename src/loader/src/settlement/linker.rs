//! Multi-module linker for settlement.
//!
//! This module handles:
//! - Cross-module symbol resolution
//! - Dependency tracking
//! - Hot code replacement via indirection tables

use std::collections::HashMap;

use crate::module::LoadedModule;
use crate::smf::{SymbolBinding, SymbolType};

use super::container::{ModuleHandle, SettlementError};
use super::tables::TableIndex;

/// An exported symbol from a module.
#[derive(Debug, Clone)]
pub struct ExportedSymbol {
    /// Name of the symbol
    pub name: String,
    /// Module that exports this symbol
    pub module: ModuleHandle,
    /// Type of symbol
    pub sym_type: SymbolType,
    /// Index in the appropriate indirection table
    pub table_index: TableIndex,
    /// Direct address (for resolution before table registration)
    pub address: usize,
    /// Symbol version (for compatibility checking)
    pub version: u32,
}

/// An imported symbol required by a module.
#[derive(Debug, Clone)]
pub struct ImportedSymbol {
    /// Name of the symbol
    pub name: String,
    /// Type of symbol expected
    pub sym_type: SymbolType,
    /// Relocation offset in code
    pub reloc_offset: u64,
    /// Whether this is a weak import (optional)
    pub weak: bool,
}

/// Result of linking a module.
#[derive(Debug)]
pub struct LinkResult {
    /// Modules that this module depends on
    pub dependencies: Vec<ModuleHandle>,
    /// Resolved addresses for imports (symbol_name -> resolved_address)
    pub resolved_imports: HashMap<String, usize>,
    /// Unresolved symbols (only an error if not weak)
    pub unresolved: Vec<String>,
}

/// Settlement linker for cross-module symbol resolution.
pub struct SettlementLinker {
    /// Global export index: symbol name -> export info
    exports: HashMap<String, ExportedSymbol>,
    /// Per-module exports: module handle -> list of exported symbol names
    module_exports: HashMap<ModuleHandle, Vec<String>>,
    /// Dependency graph: module -> modules it depends on
    dependencies: HashMap<ModuleHandle, Vec<ModuleHandle>>,
    /// Reverse dependencies: module -> modules that depend on it
    dependents: HashMap<ModuleHandle, Vec<ModuleHandle>>,
}

impl SettlementLinker {
    /// Create a new linker.
    pub fn new() -> Self {
        Self {
            exports: HashMap::new(),
            module_exports: HashMap::new(),
            dependencies: HashMap::new(),
            dependents: HashMap::new(),
        }
    }

    /// Register a module's exports.
    ///
    /// This should be called after code is loaded into settlement memory
    /// so that addresses are valid settlement addresses.
    pub fn register_exports(
        &mut self,
        module: &LoadedModule,
        handle: ModuleHandle,
        code_base: usize,
        func_indices: &[(String, TableIndex)],
    ) {
        let mut export_names = Vec::new();

        // Register function exports
        for (name, table_idx) in func_indices {
            // Look up the symbol to get its offset
            if let Some(sym) = module.symbols.lookup(name) {
                if sym.binding == SymbolBinding::Global {
                    let address = code_base + sym.value as usize;
                    let export = ExportedSymbol {
                        name: name.clone(),
                        module: handle,
                        sym_type: sym.sym_type,
                        table_index: *table_idx,
                        address,
                        version: module.version,
                    };
                    self.exports.insert(name.clone(), export);
                    export_names.push(name.clone());
                }
            }
        }

        // Also register exports not yet in func_indices (for data, types, etc.)
        for sym in module.symbols.exports() {
            let sym_name = module.symbols.symbol_name(sym).to_string();
            if !self.exports.contains_key(&sym_name) {
                let address = code_base + sym.value as usize;
                let export = ExportedSymbol {
                    name: sym_name.clone(),
                    module: handle,
                    sym_type: sym.sym_type,
                    table_index: TableIndex::INVALID, // Not in table yet
                    address,
                    version: module.version,
                };
                self.exports.insert(sym_name.clone(), export);
                export_names.push(sym_name);
            }
        }

        self.module_exports.insert(handle, export_names);
        self.dependencies.entry(handle).or_insert_with(Vec::new);
        self.dependents.entry(handle).or_insert_with(Vec::new);
    }

    /// Extract imports from a module (symbols that need external resolution).
    pub fn extract_imports(&self, module: &LoadedModule) -> Vec<ImportedSymbol> {
        let mut imports = Vec::new();

        for sym in &module.symbols.symbols {
            // Non-local symbols that aren't defined in this module need resolution
            if sym.binding != SymbolBinding::Local {
                // Check if this symbol has relocations pointing to it
                // For now, we consider all non-local, non-exported symbols as imports
                let sym_name = module.symbols.symbol_name(sym).to_string();

                // Skip if we export this symbol ourselves
                if module.symbols.lookup(&sym_name)
                    .map(|s| s.binding == SymbolBinding::Global && s.value != 0)
                    .unwrap_or(false)
                {
                    continue;
                }

                // External symbol needs resolution
                if sym.value == 0 && sym.binding != SymbolBinding::Local {
                    imports.push(ImportedSymbol {
                        name: sym_name,
                        sym_type: sym.sym_type,
                        reloc_offset: 0, // Will be filled from relocations
                        weak: sym.binding == SymbolBinding::Weak,
                    });
                }
            }
        }

        imports
    }

    /// Link a module against existing exports.
    ///
    /// Returns the dependencies and resolved import addresses.
    pub fn link_module(
        &mut self,
        module: &LoadedModule,
        handle: ModuleHandle,
    ) -> Result<LinkResult, SettlementError> {
        let imports = self.extract_imports(module);
        let mut resolved_imports = HashMap::new();
        let mut dependencies = Vec::new();
        let mut unresolved = Vec::new();

        for import in imports {
            if let Some(export) = self.exports.get(&import.name) {
                // Symbol found - record dependency and resolved address
                resolved_imports.insert(import.name.clone(), export.address);

                if !dependencies.contains(&export.module) && export.module != handle {
                    dependencies.push(export.module);

                    // Update dependency graph
                    self.dependencies
                        .entry(handle)
                        .or_insert_with(Vec::new)
                        .push(export.module);

                    // Update reverse dependencies
                    self.dependents
                        .entry(export.module)
                        .or_insert_with(Vec::new)
                        .push(handle);
                }
            } else if !import.weak {
                // Required symbol not found
                unresolved.push(import.name);
            }
        }

        Ok(LinkResult {
            dependencies,
            resolved_imports,
            unresolved,
        })
    }

    /// Create a resolver function for use with relocation application.
    pub fn create_resolver(&self) -> impl Fn(&str) -> Option<usize> + '_ {
        move |name: &str| self.resolve_symbol(name)
    }

    /// Resolve a symbol by name.
    pub fn resolve_symbol(&self, name: &str) -> Option<usize> {
        self.exports.get(name).map(|e| e.address)
    }

    /// Resolve a symbol and get the table index.
    pub fn resolve_symbol_with_index(&self, name: &str) -> Option<(usize, TableIndex)> {
        self.exports.get(name).map(|e| (e.address, e.table_index))
    }

    /// Get all modules that depend on the given module.
    pub fn get_dependents(&self, handle: ModuleHandle) -> Vec<ModuleHandle> {
        self.dependents.get(&handle).cloned().unwrap_or_default()
    }

    /// Get all modules that the given module depends on.
    pub fn get_dependencies(&self, handle: ModuleHandle) -> Vec<ModuleHandle> {
        self.dependencies.get(&handle).cloned().unwrap_or_default()
    }

    /// Check if a module can be safely removed (no dependents).
    pub fn can_remove(&self, handle: ModuleHandle) -> bool {
        self.get_dependents(handle).is_empty()
    }

    /// Unregister a module's exports.
    pub fn unregister_module(&mut self, handle: ModuleHandle) {
        // Remove from exports
        if let Some(export_names) = self.module_exports.remove(&handle) {
            for name in export_names {
                self.exports.remove(&name);
            }
        }

        // Remove from dependency graph
        self.dependencies.remove(&handle);

        // Remove from reverse dependencies
        for deps in self.dependents.values_mut() {
            deps.retain(|&h| h != handle);
        }
        self.dependents.remove(&handle);

        // Also remove from other modules' dependencies
        for deps in self.dependencies.values_mut() {
            deps.retain(|&h| h != handle);
        }
    }

    /// Update exports for a module (for hot reload).
    pub fn update_exports(
        &mut self,
        module: &LoadedModule,
        handle: ModuleHandle,
        code_base: usize,
        func_indices: &[(String, TableIndex)],
    ) {
        // First unregister old exports
        self.unregister_module(handle);
        // Then register new ones
        self.register_exports(module, handle, code_base, func_indices);
    }

    /// Get export information for a symbol.
    pub fn get_export(&self, name: &str) -> Option<&ExportedSymbol> {
        self.exports.get(name)
    }

    /// Check for dependency cycles starting from a module.
    pub fn check_dependency_cycle(&self, start: ModuleHandle) -> Option<Vec<ModuleHandle>> {
        let mut visited = Vec::new();
        let mut path = Vec::new();

        if self.dfs_cycle(start, &mut visited, &mut path) {
            Some(path)
        } else {
            None
        }
    }

    fn dfs_cycle(
        &self,
        current: ModuleHandle,
        visited: &mut Vec<ModuleHandle>,
        path: &mut Vec<ModuleHandle>,
    ) -> bool {
        if path.contains(&current) {
            path.push(current);
            return true;
        }

        if visited.contains(&current) {
            return false;
        }

        visited.push(current);
        path.push(current);

        if let Some(deps) = self.dependencies.get(&current) {
            for &dep in deps {
                if self.dfs_cycle(dep, visited, path) {
                    return true;
                }
            }
        }

        path.pop();
        false
    }

    /// Get all exports.
    pub fn exports(&self) -> impl Iterator<Item = (&String, &ExportedSymbol)> {
        self.exports.iter()
    }

    /// Get number of exports.
    pub fn export_count(&self) -> usize {
        self.exports.len()
    }
}

impl Default for SettlementLinker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linker_creation() {
        let linker = SettlementLinker::new();
        assert_eq!(linker.export_count(), 0);
    }

    #[test]
    fn test_dependency_tracking() {
        let mut linker = SettlementLinker::new();

        let h1 = ModuleHandle(0);
        let h2 = ModuleHandle(1);

        // Manually add dependency
        linker.dependencies.insert(h2, vec![h1]);
        linker.dependents.insert(h1, vec![h2]);

        assert_eq!(linker.get_dependencies(h2), vec![h1]);
        assert_eq!(linker.get_dependents(h1), vec![h2]);
        assert!(linker.can_remove(h2)); // h2 has no dependents
        assert!(!linker.can_remove(h1)); // h1 has h2 as dependent
    }

    #[test]
    fn test_cycle_detection() {
        let mut linker = SettlementLinker::new();

        let h1 = ModuleHandle(0);
        let h2 = ModuleHandle(1);
        let h3 = ModuleHandle(2);

        // Create a cycle: h1 -> h2 -> h3 -> h1
        linker.dependencies.insert(h1, vec![h2]);
        linker.dependencies.insert(h2, vec![h3]);
        linker.dependencies.insert(h3, vec![h1]);

        let cycle = linker.check_dependency_cycle(h1);
        assert!(cycle.is_some());
    }

    #[test]
    fn test_no_cycle() {
        let mut linker = SettlementLinker::new();

        let h1 = ModuleHandle(0);
        let h2 = ModuleHandle(1);
        let h3 = ModuleHandle(2);

        // Linear: h1 -> h2 -> h3
        linker.dependencies.insert(h1, vec![h2]);
        linker.dependencies.insert(h2, vec![h3]);
        linker.dependencies.insert(h3, vec![]);

        assert!(linker.check_dependency_cycle(h1).is_none());
    }
}
