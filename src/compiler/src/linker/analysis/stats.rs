//! Analysis statistics

#[derive(Default)]
pub struct AnalysisStats {
    /// Total number of symbols.
    pub total_symbols: usize,
    /// Number of exported symbols.
    pub exported_symbols: usize,
    /// Number of imported symbols.
    pub imported_symbols: usize,
    /// Number of local symbols.
    pub local_symbols: usize,
    /// Number of reachable symbols.
    pub reachable_symbols: usize,
    /// Number of dead (unreachable) symbols.
    pub dead_symbols: usize,
    /// Total estimated code size.
    pub total_size: usize,
    /// Dead code size (removable).
    pub dead_size: usize,
    /// Number of symbol groups.
    pub group_count: u32,
}

impl AnalysisStats {
    /// Calculate dead code ratio.
    pub fn dead_ratio(&self) -> f64 {
        if self.total_symbols == 0 {
            0.0
        } else {
            self.dead_symbols as f64 / self.total_symbols as f64
        }
    }

    /// Calculate dead size ratio.
    pub fn dead_size_ratio(&self) -> f64 {
        if self.total_size == 0 {
            0.0
        } else {
            self.dead_size as f64 / self.total_size as f64
        }
    }
}
