//! Extended Coverage Analysis
//!
//! Enriches LLVM coverage data with:
//! - Public class/struct method coverage (System tests)
//! - Public function coverage (Integration tests)
//! - Merged line/branch coverage (All tests)

mod analyzer;
mod display;
mod metrics;
mod report;
mod types;
mod utils;

// Re-export public API
pub use analyzer::CoverageAnalyzer;
pub use display::print_coverage_summary;
pub use metrics::CoverageMetrics;
pub use report::{ExtendedCoverageReport, COVERAGE_VERSION};
pub use types::{
    CoverageSource, CoverageType, ExtendedCoverageSummary, ExternalLibCoverage, FileCoverage,
    FunctionCoverage, InterfaceCoverage, MethodCoverage, NeighborCoverage, TypeCoverage,
    TypeMethodSummary, UncoveredItem, UncoveredSummary,
};
