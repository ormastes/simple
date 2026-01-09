//! Symbol Analysis (#804)
//!
//! Provides symbol table analysis for optimization and linking:
//! 1. Dead code elimination (unused symbols)
//! 2. Symbol dependency graphs
//! 3. Symbol grouping for cache locality
//! 4. Export/import analysis
//! 5. Symbol size estimation

pub mod analyzer;
pub mod graph;
pub mod stats;
pub mod symbol;
pub mod types;

// Re-export public API
pub use analyzer::SymbolAnalyzer;
pub use graph::SymbolGraph;
pub use stats::AnalysisStats;
pub use symbol::AnalyzedSymbol;
pub use types::{RefKind, SymbolVisibility};
