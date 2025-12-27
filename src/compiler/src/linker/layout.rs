//! Layout Optimization for 4KB Page Locality (#2030-#2039)
//!
//! This module provides layout optimization for cache-efficient startup:
//! - Section ordering by layout phase (startup → first_frame → steady → cold)
//! - Symbol grouping for cache locality
//! - Profile-guided section layout
//! - Hot/cold code splitting
//!
//! # 4KB Page Locality
//!
//! Modern CPUs load memory in 4KB pages. By grouping related code together,
//! we minimize page faults during startup and improve cache hit rates.
//!
//! ## Phase Ordering
//!
//! Code is ordered by execution phase:
//! 1. **Startup**: Code called once during initialization
//! 2. **FirstFrame**: Code called during first frame/initial render
//! 3. **Steady**: Hot path code called frequently during runtime
//! 4. **Cold**: Rarely called code (error handlers, etc.)

use std::collections::{HashMap, HashSet};

use crate::hir::{LayoutConfig, LayoutPhase, RecordedFunction};

use super::smf_writer::SmfSymbol;

/// Layout phase priority for sorting (lower = earlier in output)
const PHASE_PRIORITY_STARTUP: u8 = 0;
const PHASE_PRIORITY_FIRST_FRAME: u8 = 1;
const PHASE_PRIORITY_STEADY: u8 = 2;
const PHASE_PRIORITY_COLD: u8 = 3;

/// Convert priority byte to LayoutPhase
fn phase_from_priority(priority: u8) -> LayoutPhase {
    match priority {
        0 => LayoutPhase::Startup,
        1 => LayoutPhase::FirstFrame,
        2 => LayoutPhase::Steady,
        _ => LayoutPhase::Cold,
    }
}

/// Symbol layout entry for optimization
#[derive(Debug, Clone)]
pub struct LayoutSymbol {
    /// Symbol name
    pub name: String,
    /// Layout phase (startup, first_frame, steady, cold)
    pub phase: LayoutPhase,
    /// Symbol size in bytes
    pub size: u64,
    /// Call count from profiling
    pub call_count: u64,
    /// Symbols this symbol calls (for grouping)
    pub callees: Vec<String>,
    /// Whether this is an event loop anchor
    pub is_anchor: bool,
    /// Whether layout is pinned (cannot be moved)
    pub pinned: bool,
    /// Group ID for cache locality
    pub group_id: Option<u32>,
}

impl LayoutSymbol {
    /// Create from an SmfSymbol
    pub fn from_smf_symbol(sym: &SmfSymbol) -> Self {
        Self {
            name: sym.name.clone(),
            phase: phase_from_priority(sym.layout_phase),
            size: sym.size,
            call_count: 0,
            callees: Vec::new(),
            is_anchor: sym.is_event_loop_anchor,
            pinned: sym.layout_pinned,
            group_id: None,
        }
    }

    /// Get sort priority (lower = earlier in output)
    pub fn sort_priority(&self) -> u8 {
        match self.phase {
            LayoutPhase::Startup => PHASE_PRIORITY_STARTUP,
            LayoutPhase::FirstFrame => PHASE_PRIORITY_FIRST_FRAME,
            LayoutPhase::Steady => PHASE_PRIORITY_STEADY,
            LayoutPhase::Cold => PHASE_PRIORITY_COLD,
        }
    }
}

/// Layout optimizer for organizing symbols and sections
#[derive(Debug, Default)]
pub struct LayoutOptimizer {
    /// Symbols to optimize
    symbols: Vec<LayoutSymbol>,
    /// Layout configuration (patterns, hints)
    config: Option<LayoutConfig>,
    /// Recorded function data from profiling
    recorded: HashMap<String, RecordedFunction>,
    /// Next group ID for assignment
    next_group_id: u32,
    /// Statistics
    stats: LayoutStats,
}

/// Statistics from layout optimization
#[derive(Debug, Clone, Default)]
pub struct LayoutStats {
    /// Total symbols processed
    pub total_symbols: usize,
    /// Symbols in startup phase
    pub startup_symbols: usize,
    /// Symbols in first_frame phase
    pub first_frame_symbols: usize,
    /// Symbols in steady phase
    pub steady_symbols: usize,
    /// Symbols in cold phase
    pub cold_symbols: usize,
    /// Number of symbol groups created
    pub groups_created: u32,
    /// Estimated page savings from grouping
    pub page_savings: usize,
}

impl LayoutOptimizer {
    /// Create a new layout optimizer
    pub fn new() -> Self {
        Self::default()
    }

    /// Create with layout configuration
    pub fn with_config(config: LayoutConfig) -> Self {
        let mut opt = Self::new();
        opt.set_config(config);
        opt
    }

    /// Set layout configuration
    pub fn set_config(&mut self, config: LayoutConfig) {
        // Index recorded functions by name
        for rec in &config.recorded {
            self.recorded.insert(rec.name.clone(), rec.clone());
        }
        self.config = Some(config);
    }

    /// Add symbols from SMF
    pub fn add_smf_symbols(&mut self, symbols: &[SmfSymbol]) {
        for sym in symbols {
            let mut layout_sym = LayoutSymbol::from_smf_symbol(sym);

            // Enrich with recorded data if available
            if let Some(rec) = self.recorded.get(&sym.name) {
                layout_sym.phase = rec.phase;
                layout_sym.call_count = rec.call_count;
                if rec.size > 0 {
                    layout_sym.size = rec.size;
                }
            }

            // Apply pattern matching from config
            if let Some(config) = &self.config {
                // Use config's get_phase which checks overrides, recorded, and patterns
                layout_sym.phase = config.get_phase(&sym.name);
            }

            self.symbols.push(layout_sym);
        }
    }

    /// Sort symbols by layout phase (Phase 4 - #2030-#2032)
    ///
    /// Orders symbols as: startup → first_frame → steady → cold
    /// Within each phase, anchors come first, then by call count (descending)
    pub fn sort_by_phase(&mut self) {
        self.symbols.sort_by(|a, b| {
            // First by phase priority
            let phase_cmp = a.sort_priority().cmp(&b.sort_priority());
            if phase_cmp != std::cmp::Ordering::Equal {
                return phase_cmp;
            }

            // Within phase: anchors first
            if a.is_anchor != b.is_anchor {
                return if a.is_anchor {
                    std::cmp::Ordering::Less
                } else {
                    std::cmp::Ordering::Greater
                };
            }

            // Then by call count (higher = earlier)
            b.call_count.cmp(&a.call_count)
        });

        // Update stats
        self.update_phase_stats();
    }

    /// Group symbols for cache locality (Phase 4 - #2033-#2035)
    ///
    /// Groups symbols that call each other together to minimize cache misses.
    /// Uses a greedy algorithm to fit symbols into 4KB groups.
    pub fn group_for_locality(&mut self) {
        const PAGE_SIZE: u64 = 4096;

        // Build call graph
        let mut call_graph: HashMap<String, HashSet<String>> = HashMap::new();
        for sym in &self.symbols {
            call_graph.insert(sym.name.clone(), sym.callees.iter().cloned().collect());
        }

        // Assign groups using greedy bin packing
        let mut current_group = 0u32;
        let mut current_size = 0u64;
        let mut assigned: HashSet<String> = HashSet::new();

        // Process in sorted order (startup first)
        let names: Vec<String> = self.symbols.iter().map(|s| s.name.clone()).collect();

        for name in &names {
            if assigned.contains(name) {
                continue;
            }

            let sym_idx = self.symbols.iter().position(|s| &s.name == name);
            if sym_idx.is_none() {
                continue;
            }
            let sym_idx = sym_idx.unwrap();

            let sym_size = self.symbols[sym_idx].size;

            // Check if fits in current group
            if current_size + sym_size > PAGE_SIZE && current_size > 0 {
                current_group += 1;
                current_size = 0;
            }

            // Assign to group
            self.symbols[sym_idx].group_id = Some(current_group);
            current_size += sym_size;
            assigned.insert(name.clone());

            // Try to add callees to same group
            if let Some(callees) = call_graph.get(name) {
                for callee in callees {
                    if assigned.contains(callee) {
                        continue;
                    }

                    if let Some(callee_idx) = self.symbols.iter().position(|s| &s.name == callee) {
                        let callee_size = self.symbols[callee_idx].size;
                        if current_size + callee_size <= PAGE_SIZE {
                            self.symbols[callee_idx].group_id = Some(current_group);
                            current_size += callee_size;
                            assigned.insert(callee.clone());
                        }
                    }
                }
            }
        }

        self.next_group_id = current_group + 1;
        self.stats.groups_created = self.next_group_id;
    }

    /// Apply profile-guided layout (Phase 4 - #2036-#2037)
    ///
    /// Uses recorded execution data to refine layout decisions.
    pub fn apply_profile_guided_layout(&mut self) {
        // Re-classify based on actual call counts
        for sym in &mut self.symbols {
            if let Some(rec) = self.recorded.get(&sym.name) {
                // Override phase based on actual execution
                sym.phase = rec.phase;
                sym.call_count = rec.call_count;
            }
        }

        // Re-sort with updated phases
        self.sort_by_phase();
    }

    /// Split hot and cold code (Phase 4 - #2038-#2039)
    ///
    /// Separates frequently-called symbols from rarely-called ones
    /// to improve instruction cache utilization.
    pub fn split_hot_cold(&mut self) -> (Vec<LayoutSymbol>, Vec<LayoutSymbol>) {
        let mut hot = Vec::new();
        let mut cold = Vec::new();

        for sym in &self.symbols {
            match sym.phase {
                LayoutPhase::Startup | LayoutPhase::FirstFrame | LayoutPhase::Steady => {
                    hot.push(sym.clone());
                }
                LayoutPhase::Cold => {
                    cold.push(sym.clone());
                }
            }
        }

        (hot, cold)
    }

    /// Get ordered symbol names for linker output
    pub fn get_ordered_symbols(&self) -> Vec<String> {
        self.symbols.iter().map(|s| s.name.clone()).collect()
    }

    /// Get symbols grouped by group_id
    pub fn get_grouped_symbols(&self) -> HashMap<u32, Vec<String>> {
        let mut groups: HashMap<u32, Vec<String>> = HashMap::new();

        for sym in &self.symbols {
            if let Some(gid) = sym.group_id {
                groups.entry(gid).or_default().push(sym.name.clone());
            }
        }

        groups
    }

    /// Get layout statistics
    pub fn stats(&self) -> &LayoutStats {
        &self.stats
    }

    /// Update phase statistics
    fn update_phase_stats(&mut self) {
        self.stats.total_symbols = self.symbols.len();
        self.stats.startup_symbols = 0;
        self.stats.first_frame_symbols = 0;
        self.stats.steady_symbols = 0;
        self.stats.cold_symbols = 0;

        for sym in &self.symbols {
            match sym.phase {
                LayoutPhase::Startup => self.stats.startup_symbols += 1,
                LayoutPhase::FirstFrame => self.stats.first_frame_symbols += 1,
                LayoutPhase::Steady => self.stats.steady_symbols += 1,
                LayoutPhase::Cold => self.stats.cold_symbols += 1,
            }
        }
    }

    /// Estimate page savings from layout optimization
    pub fn estimate_savings(&self) -> usize {
        const PAGE_SIZE: usize = 4096;

        // Calculate sizes per phase
        let startup_size: u64 = self
            .symbols
            .iter()
            .filter(|s| s.phase == LayoutPhase::Startup)
            .map(|s| s.size)
            .sum();

        let first_frame_size: u64 = self
            .symbols
            .iter()
            .filter(|s| s.phase == LayoutPhase::FirstFrame)
            .map(|s| s.size)
            .sum();

        // Without optimization: all code interleaved
        // With optimization: startup and first_frame grouped together

        let optimized_startup_pages = (startup_size as usize + PAGE_SIZE - 1) / PAGE_SIZE;
        let optimized_first_frame_pages = (first_frame_size as usize + PAGE_SIZE - 1) / PAGE_SIZE;

        // Estimate unoptimized would touch ~2x more pages due to interleaving
        let unoptimized_estimate = (optimized_startup_pages + optimized_first_frame_pages) * 2;

        // Savings = unoptimized - optimized
        unoptimized_estimate
            .saturating_sub(optimized_startup_pages + optimized_first_frame_pages)
    }
}

/// Create a linker script segment for phase-ordered code
#[derive(Debug, Clone)]
pub struct LayoutSegment {
    /// Segment name (e.g., ".text.startup")
    pub name: String,
    /// Layout phase
    pub phase: LayoutPhase,
    /// Symbols in this segment
    pub symbols: Vec<String>,
    /// Total size estimate
    pub size: u64,
}

impl LayoutSegment {
    /// Create segments from layout optimizer
    pub fn from_optimizer(optimizer: &LayoutOptimizer) -> Vec<Self> {
        let mut segments = vec![
            LayoutSegment {
                name: ".text.startup".to_string(),
                phase: LayoutPhase::Startup,
                symbols: Vec::new(),
                size: 0,
            },
            LayoutSegment {
                name: ".text.first_frame".to_string(),
                phase: LayoutPhase::FirstFrame,
                symbols: Vec::new(),
                size: 0,
            },
            LayoutSegment {
                name: ".text".to_string(),
                phase: LayoutPhase::Steady,
                symbols: Vec::new(),
                size: 0,
            },
            LayoutSegment {
                name: ".text.cold".to_string(),
                phase: LayoutPhase::Cold,
                symbols: Vec::new(),
                size: 0,
            },
        ];

        for sym in &optimizer.symbols {
            let segment = match sym.phase {
                LayoutPhase::Startup => &mut segments[0],
                LayoutPhase::FirstFrame => &mut segments[1],
                LayoutPhase::Steady => &mut segments[2],
                LayoutPhase::Cold => &mut segments[3],
            };
            segment.symbols.push(sym.name.clone());
            segment.size += sym.size;
        }

        segments
    }

    /// Generate linker script input section patterns
    pub fn to_linker_script_pattern(&self) -> String {
        format!(
            "  {} : {{ *({}) }}",
            self.name,
            self.symbols
                .iter()
                .map(|s| format!("*{}*", s))
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_layout_symbol_priority() {
        let startup = LayoutSymbol {
            name: "init".to_string(),
            phase: LayoutPhase::Startup,
            size: 100,
            call_count: 1,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        };

        let cold = LayoutSymbol {
            name: "error_handler".to_string(),
            phase: LayoutPhase::Cold,
            size: 50,
            call_count: 0,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        };

        assert!(startup.sort_priority() < cold.sort_priority());
    }

    #[test]
    fn test_sort_by_phase() {
        let mut optimizer = LayoutOptimizer::new();

        // Add symbols in random order
        optimizer.symbols.push(LayoutSymbol {
            name: "cold_func".to_string(),
            phase: LayoutPhase::Cold,
            size: 50,
            call_count: 0,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        });

        optimizer.symbols.push(LayoutSymbol {
            name: "startup_func".to_string(),
            phase: LayoutPhase::Startup,
            size: 100,
            call_count: 1,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        });

        optimizer.symbols.push(LayoutSymbol {
            name: "steady_func".to_string(),
            phase: LayoutPhase::Steady,
            size: 200,
            call_count: 1000,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        });

        optimizer.sort_by_phase();

        let names: Vec<&str> = optimizer.symbols.iter().map(|s| s.name.as_str()).collect();
        assert_eq!(names, vec!["startup_func", "steady_func", "cold_func"]);
    }

    #[test]
    fn test_group_for_locality() {
        let mut optimizer = LayoutOptimizer::new();

        // Add symbols that fit in one page
        for i in 0..10 {
            optimizer.symbols.push(LayoutSymbol {
                name: format!("func_{}", i),
                phase: LayoutPhase::Startup,
                size: 100, // 100 bytes each, 1000 total < 4096
                call_count: 10 - i as u64,
                callees: vec![],
                is_anchor: false,
                pinned: false,
                group_id: None,
            });
        }

        optimizer.group_for_locality();

        // All should be in same group (group 0)
        for sym in &optimizer.symbols {
            assert_eq!(sym.group_id, Some(0));
        }
    }

    #[test]
    fn test_split_hot_cold() {
        let mut optimizer = LayoutOptimizer::new();

        optimizer.symbols.push(LayoutSymbol {
            name: "hot".to_string(),
            phase: LayoutPhase::Startup,
            size: 100,
            call_count: 100,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        });

        optimizer.symbols.push(LayoutSymbol {
            name: "cold".to_string(),
            phase: LayoutPhase::Cold,
            size: 50,
            call_count: 0,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        });

        let (hot, cold) = optimizer.split_hot_cold();

        assert_eq!(hot.len(), 1);
        assert_eq!(hot[0].name, "hot");
        assert_eq!(cold.len(), 1);
        assert_eq!(cold[0].name, "cold");
    }

    #[test]
    fn test_layout_segments() {
        let mut optimizer = LayoutOptimizer::new();

        optimizer.symbols.push(LayoutSymbol {
            name: "startup".to_string(),
            phase: LayoutPhase::Startup,
            size: 100,
            call_count: 1,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        });

        optimizer.symbols.push(LayoutSymbol {
            name: "cold".to_string(),
            phase: LayoutPhase::Cold,
            size: 50,
            call_count: 0,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        });

        let segments = LayoutSegment::from_optimizer(&optimizer);

        assert_eq!(segments[0].name, ".text.startup");
        assert_eq!(segments[0].symbols, vec!["startup"]);
        assert_eq!(segments[0].size, 100);

        assert_eq!(segments[3].name, ".text.cold");
        assert_eq!(segments[3].symbols, vec!["cold"]);
        assert_eq!(segments[3].size, 50);
    }

    #[test]
    fn test_with_config() {
        let mut config = LayoutConfig::new();
        // Set patterns directly on the patterns struct
        config.patterns.startup = vec!["init_*".to_string()];
        config.patterns.cold = vec!["*_cleanup".to_string()];

        let mut optimizer = LayoutOptimizer::with_config(config);

        // Add symbol matching pattern - initial phase is Steady (will be overridden)
        optimizer.symbols.push(LayoutSymbol {
            name: "init_system".to_string(),
            phase: LayoutPhase::Steady, // Will be overridden by config
            size: 100,
            call_count: 1,
            callees: vec![],
            is_anchor: false,
            pinned: false,
            group_id: None,
        });

        // Process with config
        if let Some(cfg) = &optimizer.config {
            optimizer.symbols[0].phase = cfg.get_phase("init_system");
        }

        assert_eq!(optimizer.symbols[0].phase, LayoutPhase::Startup);
    }
}
