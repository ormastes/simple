//! Type definitions for extended coverage analysis

use serde::{Deserialize, Serialize};

use super::metrics::CoverageMetrics;

/// Coverage report type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum CoverageType {
    /// System test: Public interface class touch
    System,
    /// Service test: Interface class + External lib touch
    Service,
    /// Integration test: Public function + Neighbor package touch
    Integration,
    /// Merged coverage: All metrics combined
    Merged,
}

/// Method coverage information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MethodCoverage {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_start: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_end: Option<u32>,
    pub is_public: bool,
    pub execution_count: u64,
    pub covered: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_coverage: Option<CoverageMetrics>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_coverage: Option<CoverageMetrics>,
}

/// Type method summary
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TypeMethodSummary {
    pub total_methods: usize,
    pub covered_methods: usize,
    pub method_coverage_percent: f64,
    pub total_public_methods: usize,
    pub covered_public_methods: usize,
    pub public_method_coverage_percent: f64,
}

/// Type (class/struct) coverage information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeCoverage {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_start: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_end: Option<u32>,
    pub is_public: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    pub methods: Vec<MethodCoverage>,
    pub summary: TypeMethodSummary,
}

/// Function coverage information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionCoverage {
    pub name: String,
    pub qualified_name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_start: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_end: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,
    pub is_public: bool,
    pub is_exported: bool,
    pub execution_count: u64,
    pub covered: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_coverage: Option<CoverageMetrics>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_coverage: Option<CoverageMetrics>,
}

/// File coverage information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileCoverage {
    pub path: String,
    pub line_coverage: CoverageMetrics,
    pub branch_coverage: CoverageMetrics,
    pub function_coverage: CoverageMetrics,
}

/// Uncovered item reference
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UncoveredItem {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_name: Option<String>,
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<u32>,
}

/// Uncovered items summary
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct UncoveredSummary {
    pub types: Vec<UncoveredItem>,
    pub methods: Vec<UncoveredItem>,
    pub functions: Vec<UncoveredItem>,
}

/// Coverage source information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoverageSource {
    pub llvm_coverage_file: String,
    pub public_api_file: String,
}

/// Interface coverage (for Service tests)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InterfaceCoverage {
    /// Interface/trait name
    pub name: String,
    /// Crate where the interface is defined
    #[serde(skip_serializing_if = "Option::is_none")]
    pub crate_name: Option<String>,
    /// Whether the interface was touched (instantiated/called)
    pub touched: bool,
    /// Execution count
    pub execution_count: u64,
}

/// External library coverage (for Service tests)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExternalLibCoverage {
    /// Library name (e.g., "cranelift")
    pub library: String,
    /// Module within the library (e.g., "codegen")
    pub module: String,
    /// Whether this module was called
    pub touched: bool,
    /// Execution count
    pub execution_count: u64,
}

/// Neighbor package coverage (for Integration tests)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeighborCoverage {
    /// Source crate
    pub crate_name: String,
    /// Neighbor crate that was accessed
    pub neighbor: String,
    /// Whether the neighbor was touched
    pub touched: bool,
    /// Number of cross-crate calls
    pub call_count: u64,
}

/// Overall coverage summary
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ExtendedCoverageSummary {
    // System test metrics
    pub total_types: usize,
    pub covered_types: usize,
    pub type_coverage_percent: f64,
    pub total_methods: usize,
    pub covered_methods: usize,
    pub method_coverage_percent: f64,

    // Service test metrics
    #[serde(default)]
    pub total_interfaces: usize,
    #[serde(default)]
    pub covered_interfaces: usize,
    #[serde(default)]
    pub interface_coverage_percent: f64,
    #[serde(default)]
    pub total_external_libs: usize,
    #[serde(default)]
    pub covered_external_libs: usize,
    #[serde(default)]
    pub external_lib_coverage_percent: f64,

    // Integration test metrics
    pub total_functions: usize,
    pub covered_functions: usize,
    pub function_coverage_percent: f64,
    #[serde(default)]
    pub total_neighbors: usize,
    #[serde(default)]
    pub covered_neighbors: usize,
    #[serde(default)]
    pub neighbor_coverage_percent: f64,

    // Line/branch coverage
    pub total_lines: usize,
    pub covered_lines: usize,
    pub line_coverage_percent: f64,
    pub total_branches: usize,
    pub covered_branches: usize,
    pub branch_coverage_percent: f64,
}
