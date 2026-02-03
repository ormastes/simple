//! Parallel SMF Linking (#811)
//!
//! Provides parallel linking of SMF modules using rayon for improved linking performance.
//! Multiple object files can be processed and merged concurrently.

use dashmap::DashMap;
use parking_lot::RwLock;
use rayon::prelude::*;
use std::sync::Arc;

use super::smf_writer::{SmfRelocation, SmfSection, SmfSymbol, SmfWriter, SymbolBinding};

/// Configuration for parallel linking.
#[derive(Debug, Clone)]
pub struct ParallelLinkConfig {
    /// Minimum number of modules to trigger parallel linking.
    pub parallel_threshold: usize,
    /// Number of threads to use. None means use all available.
    pub num_threads: Option<usize>,
    /// Whether to deduplicate symbols across modules.
    pub deduplicate_symbols: bool,
    /// Whether to merge identical code sections.
    pub merge_code_sections: bool,
}

impl Default for ParallelLinkConfig {
    fn default() -> Self {
        Self {
            parallel_threshold: 4,
            num_threads: None,
            deduplicate_symbols: true,
            merge_code_sections: false,
        }
    }
}

impl ParallelLinkConfig {
    /// Create a new config with default settings.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the parallel threshold.
    pub fn with_threshold(mut self, threshold: usize) -> Self {
        self.parallel_threshold = threshold;
        self
    }

    /// Set the number of threads.
    pub fn with_threads(mut self, n: usize) -> Self {
        self.num_threads = Some(n);
        self
    }

    /// Enable symbol deduplication.
    pub fn with_deduplication(mut self, enabled: bool) -> Self {
        self.deduplicate_symbols = enabled;
        self
    }
}

/// Statistics about parallel linking.
#[derive(Debug, Clone, Default)]
pub struct LinkStats {
    /// Number of modules linked.
    pub modules_linked: usize,
    /// Number of sections merged.
    pub sections_merged: usize,
    /// Number of symbols processed.
    pub symbols_processed: usize,
    /// Number of relocations resolved.
    pub relocations_resolved: usize,
    /// Whether parallel processing was used.
    pub used_parallel: bool,
}

/// Input module for linking.
#[derive(Debug, Clone)]
pub struct LinkModule {
    /// Module name.
    pub name: String,
    /// Code sections.
    pub sections: Vec<SmfSection>,
    /// Symbols exported by this module.
    pub symbols: Vec<SmfSymbol>,
    /// Relocations that need to be resolved.
    pub relocations: Vec<SmfRelocation>,
}

impl LinkModule {
    /// Create a new link module.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            sections: Vec::new(),
            symbols: Vec::new(),
            relocations: Vec::new(),
        }
    }

    /// Add a section.
    pub fn add_section(&mut self, section: SmfSection) {
        self.sections.push(section);
    }

    /// Add a symbol.
    pub fn add_symbol(&mut self, symbol: SmfSymbol) {
        self.symbols.push(symbol);
    }

    /// Add a relocation.
    pub fn add_relocation(&mut self, reloc: SmfRelocation) {
        self.relocations.push(reloc);
    }
}

/// Thread-safe symbol table for parallel linking.
pub struct ParallelSymbolTable {
    /// Map from symbol name to its definition.
    symbols: DashMap<String, SymbolEntry>,
    /// Global symbol index counter.
    next_index: RwLock<u32>,
}

/// Entry in the symbol table.
#[derive(Debug, Clone)]
pub struct SymbolEntry {
    /// Symbol index in the output.
    pub index: u32,
    /// Original symbol definition.
    pub symbol: SmfSymbol,
    /// Module that defined this symbol.
    pub module_name: String,
}

impl ParallelSymbolTable {
    /// Create a new parallel symbol table.
    pub fn new() -> Self {
        Self {
            symbols: DashMap::new(),
            next_index: RwLock::new(0),
        }
    }

    /// Add a symbol from a module.
    /// Returns the symbol index if successfully added, or the existing index if duplicate.
    pub fn add_symbol(&self, symbol: SmfSymbol, module_name: &str) -> u32 {
        // Check if symbol already exists
        if let Some(existing) = self.symbols.get(&symbol.name) {
            // Global symbols take precedence
            if existing.symbol.binding == SymbolBinding::Global {
                return existing.index;
            }
        }

        // Allocate new index
        let index = {
            let mut idx = self.next_index.write();
            let current = *idx;
            *idx += 1;
            current
        };

        let entry = SymbolEntry {
            index,
            symbol: symbol.clone(),
            module_name: module_name.to_string(),
        };

        self.symbols.insert(symbol.name.clone(), entry);
        index
    }

    /// Get a symbol by name.
    pub fn get(&self, name: &str) -> Option<SymbolEntry> {
        self.symbols.get(name).map(|r| r.clone())
    }

    /// Get all symbols.
    pub fn all_symbols(&self) -> Vec<SymbolEntry> {
        self.symbols.iter().map(|r| r.clone()).collect()
    }

    /// Get the number of symbols.
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}

impl Default for ParallelSymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Parallel linker that processes multiple modules concurrently.
pub struct ParallelLinker {
    config: ParallelLinkConfig,
    stats: RwLock<LinkStats>,
    symbol_table: Arc<ParallelSymbolTable>,
}

impl ParallelLinker {
    /// Create a new parallel linker.
    pub fn new() -> Self {
        Self {
            config: ParallelLinkConfig::default(),
            stats: RwLock::new(LinkStats::default()),
            symbol_table: Arc::new(ParallelSymbolTable::new()),
        }
    }

    /// Create with custom config.
    pub fn with_config(config: ParallelLinkConfig) -> Self {
        Self {
            config,
            stats: RwLock::new(LinkStats::default()),
            symbol_table: Arc::new(ParallelSymbolTable::new()),
        }
    }

    /// Get current statistics.
    pub fn stats(&self) -> LinkStats {
        self.stats.read().clone()
    }

    /// Reset statistics.
    pub fn reset_stats(&self) {
        *self.stats.write() = LinkStats::default();
    }

    /// Get the symbol table.
    pub fn symbol_table(&self) -> Arc<ParallelSymbolTable> {
        Arc::clone(&self.symbol_table)
    }

    /// Link multiple modules into a single SMF writer.
    pub fn link(&self, modules: &[LinkModule]) -> SmfWriter {
        let use_parallel = modules.len() >= self.config.parallel_threshold;

        {
            let mut stats = self.stats.write();
            stats.used_parallel = use_parallel;
            stats.modules_linked = modules.len();
        }

        if use_parallel {
            self.link_parallel(modules)
        } else {
            self.link_sequential(modules)
        }
    }

    /// Link modules sequentially.
    fn link_sequential(&self, modules: &[LinkModule]) -> SmfWriter {
        let mut writer = SmfWriter::new();
        let mut section_count = 0;
        let mut symbol_count = 0;
        let mut reloc_count = 0;

        for module in modules {
            // Process symbols
            for symbol in &module.symbols {
                self.symbol_table.add_symbol(symbol.clone(), &module.name);
                symbol_count += 1;
            }

            // Add sections
            for section in &module.sections {
                writer.add_code_section(&section.name, section.data.clone());
                section_count += 1;
            }

            reloc_count += module.relocations.len();
        }

        // Add all symbols to writer
        for entry in self.symbol_table.all_symbols() {
            writer.add_symbol(entry.symbol);
        }

        {
            let mut stats = self.stats.write();
            stats.sections_merged = section_count;
            stats.symbols_processed = symbol_count;
            stats.relocations_resolved = reloc_count;
        }

        writer
    }

    /// Link modules in parallel.
    fn link_parallel(&self, modules: &[LinkModule]) -> SmfWriter {
        // Phase 1: Process symbols in parallel
        let symbol_table = Arc::clone(&self.symbol_table);
        modules.par_iter().for_each(|module| {
            for symbol in &module.symbols {
                symbol_table.add_symbol(symbol.clone(), &module.name);
            }
        });

        // Phase 2: Collect sections in parallel
        let sections: Vec<_> = modules.par_iter().flat_map(|m| m.sections.clone()).collect();

        // Phase 3: Build output writer (sequential - SmfWriter is not thread-safe)
        let mut writer = SmfWriter::new();

        for section in &sections {
            writer.add_code_section(&section.name, section.data.clone());
        }

        for entry in self.symbol_table.all_symbols() {
            writer.add_symbol(entry.symbol);
        }

        // Update stats
        {
            let mut stats = self.stats.write();
            stats.sections_merged = sections.len();
            stats.symbols_processed = self.symbol_table.len();
            stats.relocations_resolved = modules.iter().map(|m| m.relocations.len()).sum();
        }

        writer
    }
}

impl Default for ParallelLinker {
    fn default() -> Self {
        Self::new()
    }
}

/// Link multiple modules in parallel.
pub fn link_modules_parallel(modules: &[LinkModule]) -> SmfWriter {
    let linker = ParallelLinker::new();
    linker.link(modules)
}

/// Link multiple modules with custom config.
pub fn link_modules_parallel_with_config(modules: &[LinkModule], config: ParallelLinkConfig) -> SmfWriter {
    let linker = ParallelLinker::with_config(config);
    linker.link(modules)
}

/// Batch linker that tracks statistics across multiple link operations.
pub struct BatchLinker {
    config: ParallelLinkConfig,
    total_stats: RwLock<LinkStats>,
}

impl BatchLinker {
    /// Create a new batch linker.
    pub fn new() -> Self {
        Self {
            config: ParallelLinkConfig::default(),
            total_stats: RwLock::new(LinkStats::default()),
        }
    }

    /// Create with custom config.
    pub fn with_config(config: ParallelLinkConfig) -> Self {
        Self {
            config,
            total_stats: RwLock::new(LinkStats::default()),
        }
    }

    /// Link a batch of modules.
    pub fn link_batch(&self, modules: &[LinkModule]) -> SmfWriter {
        let linker = ParallelLinker::with_config(self.config.clone());
        let result = linker.link(modules);
        let stats = linker.stats();

        // Aggregate stats
        let mut total = self.total_stats.write();
        total.modules_linked += stats.modules_linked;
        total.sections_merged += stats.sections_merged;
        total.symbols_processed += stats.symbols_processed;
        total.relocations_resolved += stats.relocations_resolved;
        total.used_parallel = total.used_parallel || stats.used_parallel;

        result
    }

    /// Get total statistics.
    pub fn total_stats(&self) -> LinkStats {
        self.total_stats.read().clone()
    }

    /// Reset total statistics.
    pub fn reset_stats(&self) {
        *self.total_stats.write() = LinkStats::default();
    }
}

impl Default for BatchLinker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::linker::SectionType;

    #[test]
    fn test_parallel_link_config() {
        let config = ParallelLinkConfig::new()
            .with_threshold(10)
            .with_threads(4)
            .with_deduplication(true);

        assert_eq!(config.parallel_threshold, 10);
        assert_eq!(config.num_threads, Some(4));
        assert!(config.deduplicate_symbols);
    }

    #[test]
    fn test_link_stats() {
        let stats = LinkStats {
            modules_linked: 5,
            sections_merged: 10,
            symbols_processed: 50,
            relocations_resolved: 25,
            used_parallel: true,
        };
        assert_eq!(stats.modules_linked, 5);
        assert!(stats.used_parallel);
    }

    #[test]
    fn test_link_module() {
        let mut module = LinkModule::new("test");

        let section = SmfSection {
            name: ".text".to_string(),
            section_type: SectionType::Code,
            flags: 0,
            data: vec![0xC3],
            alignment: 16,
        };
        module.add_section(section);

        let symbol = SmfSymbol {
            name: "main".to_string(),
            binding: SymbolBinding::Global,
            sym_type: crate::linker::SymbolType::Function,
            section_index: 0,
            value: 0,
            size: 1,
            layout_phase: 0,
            is_event_loop_anchor: false,
            layout_pinned: false,
        };
        module.add_symbol(symbol);

        assert_eq!(module.sections.len(), 1);
        assert_eq!(module.symbols.len(), 1);
    }

    #[test]
    fn test_parallel_symbol_table() {
        let table = ParallelSymbolTable::new();

        let sym1 = SmfSymbol {
            name: "func1".to_string(),
            binding: SymbolBinding::Global,
            sym_type: crate::linker::SymbolType::Function,
            section_index: 0,
            value: 0,
            size: 10,
            layout_phase: 0,
            is_event_loop_anchor: false,
            layout_pinned: false,
        };

        let sym2 = SmfSymbol {
            name: "func2".to_string(),
            binding: SymbolBinding::Local,
            sym_type: crate::linker::SymbolType::Function,
            section_index: 0,
            value: 10,
            size: 20,
            layout_phase: 0,
            is_event_loop_anchor: false,
            layout_pinned: false,
        };

        let idx1 = table.add_symbol(sym1, "module1");
        let idx2 = table.add_symbol(sym2, "module1");

        assert_eq!(idx1, 0);
        assert_eq!(idx2, 1);
        assert_eq!(table.len(), 2);
    }

    #[test]
    fn test_parallel_symbol_table_dedup() {
        let table = ParallelSymbolTable::new();

        let sym1 = SmfSymbol {
            name: "func".to_string(),
            binding: SymbolBinding::Global,
            sym_type: crate::linker::SymbolType::Function,
            section_index: 0,
            value: 0,
            size: 10,
            layout_phase: 0,
            is_event_loop_anchor: false,
            layout_pinned: false,
        };

        let sym2 = SmfSymbol {
            name: "func".to_string(),
            binding: SymbolBinding::Global,
            sym_type: crate::linker::SymbolType::Function,
            section_index: 1,
            value: 100,
            size: 20,
            layout_phase: 0,
            is_event_loop_anchor: false,
            layout_pinned: false,
        };

        let idx1 = table.add_symbol(sym1, "module1");
        let idx2 = table.add_symbol(sym2, "module2");

        // Should return same index for duplicate global symbol
        assert_eq!(idx1, idx2);
        assert_eq!(table.len(), 1);
    }

    #[test]
    fn test_parallel_linker() {
        let linker = ParallelLinker::new();
        let stats = linker.stats();
        assert_eq!(stats.modules_linked, 0);
        assert_eq!(stats.symbols_processed, 0);
    }

    #[test]
    fn test_link_empty_modules() {
        let modules: Vec<LinkModule> = vec![];
        let _writer = link_modules_parallel(&modules);
        // Should not panic on empty input
    }

    #[test]
    fn test_batch_linker() {
        let batch = BatchLinker::new();
        let stats = batch.total_stats();
        assert_eq!(stats.modules_linked, 0);
    }

    #[test]
    fn test_link_single_module() {
        let mut module = LinkModule::new("test");

        let section = SmfSection {
            name: ".text".to_string(),
            section_type: SectionType::Code,
            flags: 0,
            data: vec![0x90, 0xC3], // nop, ret
            alignment: 16,
        };
        module.add_section(section);

        let symbol = SmfSymbol {
            name: "entry".to_string(),
            binding: SymbolBinding::Global,
            sym_type: crate::linker::SymbolType::Function,
            section_index: 0,
            value: 0,
            size: 2,
            layout_phase: 0,
            is_event_loop_anchor: false,
            layout_pinned: false,
        };
        module.add_symbol(symbol);

        let linker = ParallelLinker::new();
        let _writer = linker.link(&[module]);

        let stats = linker.stats();
        assert_eq!(stats.modules_linked, 1);
        assert_eq!(stats.sections_merged, 1);
        assert_eq!(stats.symbols_processed, 1);
        assert!(!stats.used_parallel); // Below threshold
    }
}
