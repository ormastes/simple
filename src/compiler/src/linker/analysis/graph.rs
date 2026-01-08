//! Symbol dependency graph

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

use parking_lot::RwLock;

use super::symbol::AnalyzedSymbol;
use super::stats::AnalysisStats;
use super::types::{RefKind, SymbolVisibility};

pub struct SymbolGraph {
    /// All symbols.
    symbols: HashMap<String, AnalyzedSymbol>,
    /// Reverse references (who references this symbol).
    reverse_refs: HashMap<String, HashSet<String>>,
    /// Entry points (roots for reachability).
    entry_points: HashSet<String>,
    /// Analysis statistics.
    stats: RwLock<AnalysisStats>,
}

impl SymbolGraph {
    /// Create a new empty symbol graph.
    pub fn new() -> Self {
        Self {
            symbols: HashMap::new(),
            reverse_refs: HashMap::new(),
            entry_points: HashSet::new(),
            stats: RwLock::new(AnalysisStats::default()),
        }
    }

    /// Add a symbol to the graph.
    pub fn add_symbol(&mut self, symbol: AnalyzedSymbol) {
        let name = symbol.name.clone();

        // Update reverse references
        for target in &symbol.references {
            self.reverse_refs
                .entry(target.clone())
                .or_insert_with(HashSet::new)
                .insert(name.clone());
        }

        self.symbols.insert(name, symbol);
    }

    /// Add an entry point (root for reachability analysis).
    pub fn add_entry_point(&mut self, name: &str) {
        self.entry_points.insert(name.to_string());
    }

    /// Get a symbol by name.
    pub fn get_symbol(&self, name: &str) -> Option<&AnalyzedSymbol> {
        self.symbols.get(name)
    }

    /// Get mutable symbol by name.
    pub fn get_symbol_mut(&mut self, name: &str) -> Option<&mut AnalyzedSymbol> {
        self.symbols.get_mut(name)
    }

    /// Get all symbol names.
    pub fn symbol_names(&self) -> impl Iterator<Item = &String> {
        self.symbols.keys()
    }

    /// Get symbols that reference the given symbol.
    pub fn get_referrers(&self, name: &str) -> Option<&HashSet<String>> {
        self.reverse_refs.get(name)
    }

    /// Record a reverse reference (who references a symbol).
    pub fn add_reverse_ref(&mut self, from: &str, to: &str) {
        self.reverse_refs
            .entry(to.to_string())
            .or_insert_with(HashSet::new)
            .insert(from.to_string());
    }

    /// Perform reachability analysis from entry points.
    pub fn analyze_reachability(&mut self) {
        // Reset reachability
        for symbol in self.symbols.values_mut() {
            symbol.is_reachable = false;
        }

        // BFS from entry points
        let mut queue: VecDeque<String> = self.entry_points.iter().cloned().collect();
        let mut visited = HashSet::new();

        // Also mark all exports as reachable
        for (name, symbol) in &self.symbols {
            if symbol.is_exported() {
                queue.push_back(name.clone());
            }
        }

        while let Some(name) = queue.pop_front() {
            if visited.contains(&name) {
                continue;
            }
            visited.insert(name.clone());

            if let Some(symbol) = self.symbols.get_mut(&name) {
                symbol.is_reachable = true;

                // Add referenced symbols to queue
                for target in symbol.references.clone() {
                    if !visited.contains(&target) {
                        queue.push_back(target);
                    }
                }
            }
        }

        // Update stats
        self.update_stats();
    }

    /// Identify dead (unreachable) symbols.
    pub fn find_dead_symbols(&self) -> Vec<&AnalyzedSymbol> {
        self.symbols
            .values()
            .filter(|s| !s.is_reachable && !s.is_imported())
            .collect()
    }

    /// Group symbols by call graph locality.
    ///
    /// Symbols that frequently call each other are placed in the same group
    /// for better cache locality.
    pub fn group_by_locality(&mut self) {
        let mut group_id = 0u32;
        let mut visited = HashSet::new();

        // Start from entry points
        for entry in self.entry_points.clone() {
            if visited.contains(&entry) {
                continue;
            }

            // BFS to assign group
            let mut queue = VecDeque::new();
            queue.push_back(entry.clone());

            while let Some(name) = queue.pop_front() {
                if visited.contains(&name) {
                    continue;
                }
                visited.insert(name.clone());

                if let Some(symbol) = self.symbols.get_mut(&name) {
                    symbol.group_id = Some(group_id);

                    // Add call references (not data refs) to same group
                    for (target, kind) in symbol.ref_kinds.clone() {
                        if kind == RefKind::Call && !visited.contains(&target) {
                            queue.push_back(target);
                        }
                    }
                }
            }

            group_id += 1;
        }

        // Assign remaining symbols to their own groups
        for symbol in self.symbols.values_mut() {
            if symbol.group_id.is_none() {
                symbol.group_id = Some(group_id);
                group_id += 1;
            }
        }

        self.stats.write().group_count = group_id;
    }

    /// Get symbols sorted by group for cache-friendly layout.
    pub fn get_grouped_symbols(&self) -> Vec<Vec<&AnalyzedSymbol>> {
        let mut groups: HashMap<u32, Vec<&AnalyzedSymbol>> = HashMap::new();

        for symbol in self.symbols.values() {
            if let Some(gid) = symbol.group_id {
                groups.entry(gid).or_insert_with(Vec::new).push(symbol);
            }
        }

        let mut result: Vec<_> = groups.into_values().collect();
        result.sort_by_key(|g| g.first().map(|s| s.group_id).unwrap_or(Some(0)));
        result
    }

    /// Analyze imports and exports.
    pub fn analyze_imports_exports(&self) -> (Vec<&AnalyzedSymbol>, Vec<&AnalyzedSymbol>) {
        let imports: Vec<_> = self.symbols.values().filter(|s| s.is_imported()).collect();
        let exports: Vec<_> = self.symbols.values().filter(|s| s.is_exported()).collect();
        (imports, exports)
    }

    /// Find circular dependencies.
    pub fn find_cycles(&self) -> Vec<Vec<String>> {
        let mut cycles = Vec::new();
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();
        let mut path = Vec::new();

        for name in self.symbols.keys() {
            if !visited.contains(name) {
                self.dfs_cycles(name, &mut visited, &mut rec_stack, &mut path, &mut cycles);
            }
        }

        cycles
    }

    fn dfs_cycles(
        &self,
        name: &str,
        visited: &mut HashSet<String>,
        rec_stack: &mut HashSet<String>,
        path: &mut Vec<String>,
        cycles: &mut Vec<Vec<String>>,
    ) {
        visited.insert(name.to_string());
        rec_stack.insert(name.to_string());
        path.push(name.to_string());

        if let Some(symbol) = self.symbols.get(name) {
            for target in &symbol.references {
                if !visited.contains(target) {
                    self.dfs_cycles(target, visited, rec_stack, path, cycles);
                } else if rec_stack.contains(target) {
                    // Found a cycle
                    let cycle_start = path.iter().position(|s| s == target).unwrap();
                    let cycle: Vec<_> = path[cycle_start..].to_vec();
                    cycles.push(cycle);
                }
            }
        }

        path.pop();
        rec_stack.remove(name);
    }

    /// Update statistics.
    fn update_stats(&mut self) {
        let mut stats = AnalysisStats::default();

        for symbol in self.symbols.values() {
            stats.total_symbols += 1;
            stats.total_size += symbol.size;

            match symbol.visibility {
                SymbolVisibility::Export => stats.exported_symbols += 1,
                SymbolVisibility::Import => stats.imported_symbols += 1,
                SymbolVisibility::Local | SymbolVisibility::Hidden => stats.local_symbols += 1,
            }

            if symbol.is_reachable {
                stats.reachable_symbols += 1;
            } else if !symbol.is_imported() {
                stats.dead_symbols += 1;
                stats.dead_size += symbol.size;
            }
        }

        *self.stats.write() = stats;
    }

    /// Get analysis statistics.
    pub fn stats(&self) -> AnalysisStats {
        (*self.stats.read()).clone()
    }

    /// Get total number of symbols.
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Check if graph is empty.
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}

impl Default for SymbolGraph {
    fn default() -> Self {
        Self::new()
    }
}
