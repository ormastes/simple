//! Symbol analyzer

use std::collections::HashMap;
use std::sync::Arc;

use parking_lot::RwLock;

use super::symbol::AnalyzedSymbol;
use super::types::{RefKind, SymbolVisibility};
use super::stats::AnalysisStats;
use super::graph::SymbolGraph;

pub struct SymbolAnalyzer {
    graph: SymbolGraph,
}

impl SymbolAnalyzer {
    /// Create a new analyzer.
    pub fn new() -> Self {
        Self {
            graph: SymbolGraph::new(),
        }
    }

    /// Add a symbol to analyze.
    pub fn add_symbol(
        &mut self,
        name: &str,
        visibility: SymbolVisibility,
        size: usize,
        section: &str,
    ) {
        let mut symbol = AnalyzedSymbol::new(name.to_string(), visibility);
        symbol.size = size;
        symbol.section = section.to_string();
        self.graph.add_symbol(symbol);
    }

    /// Add a reference between symbols.
    pub fn add_reference(&mut self, from: &str, to: &str, kind: RefKind) {
        if let Some(symbol) = self.graph.get_symbol_mut(from) {
            symbol.add_reference(to.to_string(), kind);
        }

        // Update reverse refs
        self.graph.add_reverse_ref(from, to);
    }

    /// Set entry point.
    pub fn set_entry_point(&mut self, name: &str) {
        self.graph.add_entry_point(name);
    }

    /// Run full analysis.
    pub fn analyze(&mut self) -> &SymbolGraph {
        self.graph.analyze_reachability();
        self.graph.group_by_locality();
        &self.graph
    }

    /// Get the analyzed graph.
    pub fn graph(&self) -> &SymbolGraph {
        &self.graph
    }

    /// Get dead symbols that can be removed.
    pub fn get_removable_symbols(&self) -> Vec<String> {
        self.graph
            .find_dead_symbols()
            .into_iter()
            .map(|s| s.name.clone())
            .collect()
    }

    /// Get analysis statistics.
    pub fn stats(&self) -> AnalysisStats {
        self.graph.stats()
    }
}

impl Default for SymbolAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_analyzed_symbol() {
        let mut sym = AnalyzedSymbol::new("main".to_string(), SymbolVisibility::Export);
        sym.add_reference("helper".to_string(), RefKind::Call);

        assert!(sym.is_exported());
        assert!(!sym.is_imported());
        assert!(sym.references.contains("helper"));
    }

    #[test]
    fn test_symbol_graph_reachability() {
        let mut graph = SymbolGraph::new();

        graph.add_symbol(AnalyzedSymbol::new("main".to_string(), SymbolVisibility::Export));
        graph.add_symbol(AnalyzedSymbol::new("used".to_string(), SymbolVisibility::Local));
        graph.add_symbol(AnalyzedSymbol::new("unused".to_string(), SymbolVisibility::Local));

        // main -> used
        if let Some(main) = graph.get_symbol_mut("main") {
            main.add_reference("used".to_string(), RefKind::Call);
        }

        graph.add_entry_point("main");
        graph.analyze_reachability();

        assert!(graph.get_symbol("main").unwrap().is_reachable);
        assert!(graph.get_symbol("used").unwrap().is_reachable);
        assert!(!graph.get_symbol("unused").unwrap().is_reachable);
    }

    #[test]
    fn test_find_dead_symbols() {
        let mut graph = SymbolGraph::new();

        let mut main = AnalyzedSymbol::new("main".to_string(), SymbolVisibility::Export);
        main.size = 100;
        graph.add_symbol(main);

        let mut dead = AnalyzedSymbol::new("dead".to_string(), SymbolVisibility::Local);
        dead.size = 50;
        graph.add_symbol(dead);

        graph.add_entry_point("main");
        graph.analyze_reachability();

        let dead_symbols = graph.find_dead_symbols();
        assert_eq!(dead_symbols.len(), 1);
        assert_eq!(dead_symbols[0].name, "dead");

        let stats = graph.stats();
        assert_eq!(stats.dead_symbols, 1);
        assert_eq!(stats.dead_size, 50);
    }

    #[test]
    fn test_symbol_grouping() {
        let mut graph = SymbolGraph::new();

        let mut main = AnalyzedSymbol::new("main".to_string(), SymbolVisibility::Export);
        main.add_reference("helper1".to_string(), RefKind::Call);
        graph.add_symbol(main);

        let mut helper1 = AnalyzedSymbol::new("helper1".to_string(), SymbolVisibility::Local);
        helper1.add_reference("helper2".to_string(), RefKind::Call);
        graph.add_symbol(helper1);

        graph.add_symbol(AnalyzedSymbol::new("helper2".to_string(), SymbolVisibility::Local));
        graph.add_symbol(AnalyzedSymbol::new("separate".to_string(), SymbolVisibility::Local));

        graph.add_entry_point("main");
        graph.group_by_locality();

        // main, helper1, helper2 should be in same group
        let main_group = graph.get_symbol("main").unwrap().group_id;
        let h1_group = graph.get_symbol("helper1").unwrap().group_id;
        let h2_group = graph.get_symbol("helper2").unwrap().group_id;

        assert_eq!(main_group, h1_group);
        assert_eq!(h1_group, h2_group);

        // separate should be in different group
        let sep_group = graph.get_symbol("separate").unwrap().group_id;
        assert_ne!(main_group, sep_group);
    }

    #[test]
    fn test_imports_exports() {
        let mut graph = SymbolGraph::new();

        graph.add_symbol(AnalyzedSymbol::new("exported".to_string(), SymbolVisibility::Export));
        graph.add_symbol(AnalyzedSymbol::new("imported".to_string(), SymbolVisibility::Import));
        graph.add_symbol(AnalyzedSymbol::new("local".to_string(), SymbolVisibility::Local));

        let (imports, exports) = graph.analyze_imports_exports();

        assert_eq!(imports.len(), 1);
        assert_eq!(exports.len(), 1);
        assert_eq!(imports[0].name, "imported");
        assert_eq!(exports[0].name, "exported");
    }

    #[test]
    fn test_find_cycles() {
        let mut graph = SymbolGraph::new();

        let mut a = AnalyzedSymbol::new("a".to_string(), SymbolVisibility::Local);
        a.add_reference("b".to_string(), RefKind::Call);
        graph.add_symbol(a);

        let mut b = AnalyzedSymbol::new("b".to_string(), SymbolVisibility::Local);
        b.add_reference("c".to_string(), RefKind::Call);
        graph.add_symbol(b);

        let mut c = AnalyzedSymbol::new("c".to_string(), SymbolVisibility::Local);
        c.add_reference("a".to_string(), RefKind::Call); // Creates cycle
        graph.add_symbol(c);

        let cycles = graph.find_cycles();
        assert!(!cycles.is_empty());
    }

    #[test]
    fn test_symbol_analyzer() {
        let mut analyzer = SymbolAnalyzer::new();

        analyzer.add_symbol("main", SymbolVisibility::Export, 100, ".text");
        analyzer.add_symbol("helper", SymbolVisibility::Local, 50, ".text");
        analyzer.add_symbol("unused", SymbolVisibility::Local, 30, ".text");

        analyzer.add_reference("main", "helper", RefKind::Call);
        analyzer.set_entry_point("main");

        analyzer.analyze();

        let removable = analyzer.get_removable_symbols();
        assert_eq!(removable.len(), 1);
        assert_eq!(removable[0], "unused");

        let stats = analyzer.stats();
        assert_eq!(stats.total_symbols, 3);
        assert_eq!(stats.reachable_symbols, 2);
        assert_eq!(stats.dead_symbols, 1);
    }

    #[test]
    fn test_analysis_stats() {
        let stats = AnalysisStats {
            total_symbols: 100,
            dead_symbols: 25,
            total_size: 1000,
            dead_size: 200,
            ..Default::default()
        };

        assert_eq!(stats.dead_ratio(), 0.25);
        assert_eq!(stats.dead_size_ratio(), 0.2);
    }

    #[test]
    fn test_reverse_refs() {
        let mut graph = SymbolGraph::new();

        let mut caller = AnalyzedSymbol::new("caller".to_string(), SymbolVisibility::Local);
        caller.add_reference("callee".to_string(), RefKind::Call);
        graph.add_symbol(caller);

        graph.add_symbol(AnalyzedSymbol::new("callee".to_string(), SymbolVisibility::Local));

        let referrers = graph.get_referrers("callee");
        assert!(referrers.is_some());
        assert!(referrers.unwrap().contains("caller"));
    }

    #[test]
    fn test_deep_call_chain() {
        // Test reachability through deep call chain: main -> a -> b -> c -> d
        let mut graph = SymbolGraph::new();

        let symbols = ["main", "a", "b", "c", "d"];
        for (i, name) in symbols.iter().enumerate() {
            let vis = if i == 0 {
                SymbolVisibility::Export
            } else {
                SymbolVisibility::Local
            };
            let mut sym = AnalyzedSymbol::new(name.to_string(), vis);
            if i < symbols.len() - 1 {
                sym.add_reference(symbols[i + 1].to_string(), RefKind::Call);
            }
            graph.add_symbol(sym);
        }

        graph.add_entry_point("main");
        graph.analyze_reachability();

        // All symbols should be reachable
        for name in &symbols {
            assert!(
                graph.get_symbol(name).unwrap().is_reachable,
                "{} should be reachable",
                name
            );
        }
    }

    #[test]
    fn test_data_vs_call_references() {
        let mut graph = SymbolGraph::new();

        let mut main = AnalyzedSymbol::new("main".to_string(), SymbolVisibility::Export);
        main.add_reference("data_sym".to_string(), RefKind::Data);
        main.add_reference("call_sym".to_string(), RefKind::Call);
        graph.add_symbol(main);

        graph.add_symbol(AnalyzedSymbol::new("data_sym".to_string(), SymbolVisibility::Local));
        graph.add_symbol(AnalyzedSymbol::new("call_sym".to_string(), SymbolVisibility::Local));
        graph.add_symbol(AnalyzedSymbol::new("separate".to_string(), SymbolVisibility::Local));

        graph.add_entry_point("main");
        graph.group_by_locality();

        // main and call_sym should be in same group (call refs)
        let main_group = graph.get_symbol("main").unwrap().group_id;
        let call_group = graph.get_symbol("call_sym").unwrap().group_id;
        assert_eq!(main_group, call_group);

        // data_sym should be in different group (data refs don't affect grouping)
        let data_group = graph.get_symbol("data_sym").unwrap().group_id;
        assert_ne!(main_group, data_group);
    }

    #[test]
    fn test_multiple_entry_points() {
        let mut graph = SymbolGraph::new();

        // Two entry points with separate call trees
        let mut entry1 = AnalyzedSymbol::new("entry1".to_string(), SymbolVisibility::Export);
        entry1.add_reference("helper1".to_string(), RefKind::Call);
        graph.add_symbol(entry1);

        let mut entry2 = AnalyzedSymbol::new("entry2".to_string(), SymbolVisibility::Export);
        entry2.add_reference("helper2".to_string(), RefKind::Call);
        graph.add_symbol(entry2);

        graph.add_symbol(AnalyzedSymbol::new("helper1".to_string(), SymbolVisibility::Local));
        graph.add_symbol(AnalyzedSymbol::new("helper2".to_string(), SymbolVisibility::Local));
        graph.add_symbol(AnalyzedSymbol::new("unused".to_string(), SymbolVisibility::Local));

        graph.add_entry_point("entry1");
        graph.add_entry_point("entry2");
        graph.analyze_reachability();

        assert!(graph.get_symbol("entry1").unwrap().is_reachable);
        assert!(graph.get_symbol("entry2").unwrap().is_reachable);
        assert!(graph.get_symbol("helper1").unwrap().is_reachable);
        assert!(graph.get_symbol("helper2").unwrap().is_reachable);
        assert!(!graph.get_symbol("unused").unwrap().is_reachable);
    }

    #[test]
    fn test_hidden_visibility() {
        let sym = AnalyzedSymbol::new("internal".to_string(), SymbolVisibility::Hidden);

        assert!(!sym.is_exported());
        assert!(!sym.is_imported());
        assert!(!sym.is_local()); // Hidden is different from Local
    }

    #[test]
    fn test_empty_graph() {
        let graph = SymbolGraph::new();

        assert!(graph.is_empty());
        assert_eq!(graph.len(), 0);
        assert!(graph.find_dead_symbols().is_empty());
        assert!(graph.find_cycles().is_empty());

        let (imports, exports) = graph.analyze_imports_exports();
        assert!(imports.is_empty());
        assert!(exports.is_empty());
    }

    #[test]
    fn test_self_referencing_symbol() {
        // A symbol that references itself (recursive function)
        let mut graph = SymbolGraph::new();

        let mut recursive = AnalyzedSymbol::new("recursive".to_string(), SymbolVisibility::Export);
        recursive.add_reference("recursive".to_string(), RefKind::Call);
        graph.add_symbol(recursive);

        graph.add_entry_point("recursive");
        graph.analyze_reachability();

        assert!(graph.get_symbol("recursive").unwrap().is_reachable);

        // Self-reference creates a trivial cycle
        let cycles = graph.find_cycles();
        assert!(!cycles.is_empty());
    }

    #[test]
    fn test_grouped_symbols_order() {
        let mut graph = SymbolGraph::new();

        // Create two distinct call trees
        let mut main = AnalyzedSymbol::new("main".to_string(), SymbolVisibility::Export);
        main.add_reference("func_a".to_string(), RefKind::Call);
        graph.add_symbol(main);

        graph.add_symbol(AnalyzedSymbol::new("func_a".to_string(), SymbolVisibility::Local));
        graph.add_symbol(AnalyzedSymbol::new("orphan".to_string(), SymbolVisibility::Local));

        graph.add_entry_point("main");
        graph.group_by_locality();

        let groups = graph.get_grouped_symbols();
        assert!(!groups.is_empty());

        // Verify groups are non-empty
        for group in &groups {
            assert!(!group.is_empty());
        }
    }

    #[test]
    fn test_symbol_size_tracking() {
        let mut analyzer = SymbolAnalyzer::new();

        analyzer.add_symbol("large", SymbolVisibility::Export, 1000, ".text");
        analyzer.add_symbol("small", SymbolVisibility::Export, 100, ".text");
        analyzer.add_symbol("dead", SymbolVisibility::Local, 500, ".text");

        analyzer.add_reference("large", "small", RefKind::Call);
        analyzer.set_entry_point("large");
        analyzer.analyze();

        let stats = analyzer.stats();
        assert_eq!(stats.total_size, 1600);
        assert_eq!(stats.dead_size, 500);
    }

    #[test]
    fn test_address_of_reference() {
        let mut analyzer = SymbolAnalyzer::new();

        analyzer.add_symbol("main", SymbolVisibility::Export, 100, ".text");
        analyzer.add_symbol("callback", SymbolVisibility::Local, 50, ".text");

        // Address-of reference (function pointer)
        analyzer.add_reference("main", "callback", RefKind::AddressOf);
        analyzer.set_entry_point("main");
        analyzer.analyze();

        // callback should still be reachable
        assert!(analyzer.graph().get_symbol("callback").unwrap().is_reachable);
    }

    #[test]
    fn test_type_reference() {
        let mut analyzer = SymbolAnalyzer::new();

        analyzer.add_symbol("main", SymbolVisibility::Export, 100, ".text");
        analyzer.add_symbol("MyType", SymbolVisibility::Local, 0, ".data");

        analyzer.add_reference("main", "MyType", RefKind::Type);
        analyzer.set_entry_point("main");
        analyzer.analyze();

        assert!(analyzer.graph().get_symbol("MyType").unwrap().is_reachable);
    }

    #[test]
    fn test_section_tracking() {
        let mut analyzer = SymbolAnalyzer::new();

        analyzer.add_symbol("code_fn", SymbolVisibility::Export, 100, ".text");
        analyzer.add_symbol("global_var", SymbolVisibility::Export, 8, ".data");
        analyzer.add_symbol("const_val", SymbolVisibility::Export, 4, ".rodata");

        assert_eq!(analyzer.graph().get_symbol("code_fn").unwrap().section, ".text");
        assert_eq!(analyzer.graph().get_symbol("global_var").unwrap().section, ".data");
        assert_eq!(analyzer.graph().get_symbol("const_val").unwrap().section, ".rodata");
    }

    #[test]
    fn test_complex_cycle_detection() {
        // Create: a -> b -> c -> d -> b (cycle from d back to b)
        let mut graph = SymbolGraph::new();

        let names = ["a", "b", "c", "d"];
        for (i, name) in names.iter().enumerate() {
            let mut sym = AnalyzedSymbol::new(name.to_string(), SymbolVisibility::Local);
            if i < names.len() - 1 {
                sym.add_reference(names[i + 1].to_string(), RefKind::Call);
            }
            graph.add_symbol(sym);
        }

        // Add back-edge: d -> b
        if let Some(d) = graph.get_symbol_mut("d") {
            d.add_reference("b".to_string(), RefKind::Call);
        }

        let cycles = graph.find_cycles();
        assert!(!cycles.is_empty());
    }

    #[test]
    fn test_dead_ratio_edge_cases() {
        // Empty stats
        let empty_stats = AnalysisStats::default();
        assert_eq!(empty_stats.dead_ratio(), 0.0);
        assert_eq!(empty_stats.dead_size_ratio(), 0.0);

        // All dead
        let all_dead = AnalysisStats {
            total_symbols: 10,
            dead_symbols: 10,
            total_size: 1000,
            dead_size: 1000,
            ..Default::default()
        };
        assert_eq!(all_dead.dead_ratio(), 1.0);
        assert_eq!(all_dead.dead_size_ratio(), 1.0);

        // No dead
        let no_dead = AnalysisStats {
            total_symbols: 10,
            dead_symbols: 0,
            total_size: 1000,
            dead_size: 0,
            ..Default::default()
        };
        assert_eq!(no_dead.dead_ratio(), 0.0);
        assert_eq!(no_dead.dead_size_ratio(), 0.0);
    }

    #[test]
    fn test_symbol_names_iterator() {
        let mut graph = SymbolGraph::new();

        graph.add_symbol(AnalyzedSymbol::new("alpha".to_string(), SymbolVisibility::Local));
        graph.add_symbol(AnalyzedSymbol::new("beta".to_string(), SymbolVisibility::Local));
        graph.add_symbol(AnalyzedSymbol::new("gamma".to_string(), SymbolVisibility::Local));

        let names: Vec<_> = graph.symbol_names().collect();
        assert_eq!(names.len(), 3);
        assert!(names.contains(&&"alpha".to_string()));
        assert!(names.contains(&&"beta".to_string()));
        assert!(names.contains(&&"gamma".to_string()));
    }

    #[test]
    fn test_imports_not_marked_dead() {
        let mut graph = SymbolGraph::new();

        // Import symbols should never be marked as dead
        let import = AnalyzedSymbol::new("external_fn".to_string(), SymbolVisibility::Import);
        graph.add_symbol(import);

        graph.analyze_reachability();

        let dead = graph.find_dead_symbols();
        assert!(dead.is_empty(), "Import symbols should not be marked as dead");
    }
}
