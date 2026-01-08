//! Symbol Analysis (#804)
//!
//! Provides symbol table analysis for optimization and linking:
//! 1. Dead code elimination (unused symbols)
//! 2. Symbol dependency graphs
//! 3. Symbol grouping for cache locality
//! 4. Export/import analysis
//! 5. Symbol size estimation

pub mod types;
pub mod symbol;
pub mod stats;
pub mod graph;
pub mod analyzer;

// Re-export public API
pub use types::{RefKind, SymbolVisibility};
pub use symbol::AnalyzedSymbol;
pub use stats::AnalysisStats;
pub use graph::SymbolGraph;
pub use analyzer::SymbolAnalyzer;
