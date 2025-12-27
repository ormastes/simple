//! Extended coverage report implementation

use serde::{Deserialize, Serialize};
use std::path::Path;

use super::types::{
    CoverageSource, CoverageType, ExternalLibCoverage, ExtendedCoverageSummary, FileCoverage,
    FunctionCoverage, InterfaceCoverage, NeighborCoverage, TypeCoverage, UncoveredSummary,
};

/// Extended coverage report version
pub const COVERAGE_VERSION: &str = "1.0";

/// Extended coverage report
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExtendedCoverageReport {
    pub version: String,
    pub timestamp: String,
    pub coverage_type: CoverageType,
    pub source: CoverageSource,
    pub summary: ExtendedCoverageSummary,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub types: Vec<TypeCoverage>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub functions: Vec<FunctionCoverage>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub files: Vec<FileCoverage>,
    /// Interface coverage (Service tests)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub interfaces: Vec<InterfaceCoverage>,
    /// External library coverage (Service tests)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub external_libs: Vec<ExternalLibCoverage>,
    /// Neighbor package coverage (Integration tests)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub neighbors: Vec<NeighborCoverage>,
    pub uncovered: UncoveredSummary,
}

impl ExtendedCoverageReport {
    /// Create a new empty report
    pub fn new(coverage_type: CoverageType, llvm_file: &str, api_file: &str) -> Self {
        Self {
            version: COVERAGE_VERSION.to_string(),
            timestamp: chrono::Utc::now().to_rfc3339(),
            coverage_type,
            source: CoverageSource {
                llvm_coverage_file: llvm_file.to_string(),
                public_api_file: api_file.to_string(),
            },
            summary: ExtendedCoverageSummary::default(),
            types: Vec::new(),
            functions: Vec::new(),
            files: Vec::new(),
            interfaces: Vec::new(),
            external_libs: Vec::new(),
            neighbors: Vec::new(),
            uncovered: UncoveredSummary::default(),
        }
    }

    /// Check if coverage meets threshold
    pub fn meets_threshold(&self, threshold: f64) -> bool {
        match self.coverage_type {
            CoverageType::System => self.summary.method_coverage_percent >= threshold,
            CoverageType::Service => {
                // Service coverage = min(interface coverage, external lib coverage)
                let interface_pct = self.summary.interface_coverage_percent;
                let ext_lib_pct = self.summary.external_lib_coverage_percent;
                interface_pct.min(ext_lib_pct) >= threshold
            }
            CoverageType::Integration => {
                // Integration coverage = min(function coverage, neighbor coverage)
                let func_pct = self.summary.function_coverage_percent;
                let neighbor_pct = self.summary.neighbor_coverage_percent;
                func_pct.min(neighbor_pct) >= threshold
            }
            CoverageType::Merged => self.summary.line_coverage_percent >= threshold,
        }
    }

    /// Serialize to JSON
    pub fn to_json(&self) -> serde_json::Result<String> {
        serde_json::to_string_pretty(self)
    }

    /// Serialize to JSON file
    pub fn write_json<P: AsRef<Path>>(&self, path: P) -> anyhow::Result<()> {
        let json = self.to_json()?;
        std::fs::write(path, json)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::coverage::{parse_llvm_cov_export, parse_public_api_spec};
    use crate::coverage_extended::CoverageAnalyzer;

    fn create_test_analyzer() -> CoverageAnalyzer {
        let cov_json = r#"{
            "data": [{
                "functions": [
                    {"name": "MyType::method1", "count": 10},
                    {"name": "MyType::method2", "count": 0},
                    {"name": "OtherType::run", "count": 5},
                    {"name": "OtherType::stop", "count": 0}
                ]
            }]
        }"#;

        let api_yaml = r#"
types:
  MyType:
    methods: [method1, method2]
  OtherType:
    methods: [run, stop]
"#;

        let llvm_cov = parse_llvm_cov_export(cov_json).unwrap();
        let api_spec = parse_public_api_spec(api_yaml).unwrap();

        CoverageAnalyzer::new(llvm_cov, api_spec, "test.json", "test.yml")
    }

    #[test]
    fn test_report_json_serialization() {
        let analyzer = create_test_analyzer();
        let report = analyzer.generate_system_report();

        let json = report.to_json().unwrap();
        assert!(json.contains("\"version\""));
        assert!(json.contains("\"coverage_type\""));
        assert!(json.contains("\"summary\""));
    }

    #[test]
    fn test_threshold_check() {
        let analyzer = create_test_analyzer();
        let report = analyzer.generate_system_report();

        // 2/4 = 50% method coverage
        assert!(report.meets_threshold(50.0));
        assert!(!report.meets_threshold(51.0));
    }
}
