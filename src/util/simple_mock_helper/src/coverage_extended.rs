//! Extended Coverage Analysis
//!
//! Enriches LLVM coverage data with:
//! - Public class/struct method coverage (System tests)
//! - Public function coverage (Integration tests)
//! - Merged line/branch coverage (All tests)

use rustc_demangle::demangle;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::coverage::{LlvmCovExport, PublicApiSpec};

/// Demangle a Rust symbol name to human-readable form.
/// Cleans up the output to remove crate hashes and angle brackets.
fn demangle_rust_name(mangled: &str) -> String {
    let demangled = demangle(mangled).to_string();

    // Clean up the demangled name:
    // 1. Remove crate hashes like [8088a71b75a8e98d]
    // 2. Remove leading < and trailing > from impl blocks
    // 3. Remove generic parameters like ::<T>

    let mut cleaned = demangled.clone();

    // Remove crate hashes [hex]
    while let Some(start) = cleaned.find('[') {
        if let Some(end) = cleaned[start..].find(']') {
            let hash = &cleaned[start + 1..start + end];
            if hash.chars().all(|c| c.is_ascii_hexdigit()) {
                cleaned = format!("{}{}", &cleaned[..start], &cleaned[start + end + 1..]);
                continue;
            }
        }
        break;
    }

    // Remove leading < from impl blocks like <Type>::method
    if cleaned.starts_with('<') {
        if let Some(end) = cleaned.find(">::") {
            cleaned = format!("{}{}", &cleaned[1..end], &cleaned[end + 1..]);
        }
    }

    // Remove hash suffix like ::h1234abcd
    if let Some(idx) = cleaned.rfind("::h") {
        if cleaned[idx + 3..].chars().all(|c| c.is_ascii_hexdigit()) {
            cleaned = cleaned[..idx].to_string();
        }
    }

    // Remove generic parameters ::<...> at the end
    while let Some(idx) = cleaned.rfind("::<") {
        if cleaned[idx..].rfind('>').is_some() {
            cleaned = cleaned[..idx].to_string();
        } else {
            break;
        }
    }

    cleaned
}

/// Check if a demangled function name matches a type::method pattern
/// Handles various naming conventions and module paths
fn matches_type_method(demangled: &str, type_name: &str, method_name: &str) -> bool {
    // Extract just the type part from the spec (e.g., "simple_driver::Runner" -> "Runner")
    let spec_type = type_name.split("::").last().unwrap_or(type_name);

    // Check if the demangled name ends with Type::method
    let suffix = format!("{}::{}", spec_type, method_name);
    if demangled.ends_with(&suffix) {
        return true;
    }

    // Also check full path match
    let full_match = format!("{}::{}", type_name, method_name);
    if demangled.contains(&full_match) {
        return true;
    }

    false
}

/// Extended coverage report version
pub const COVERAGE_VERSION: &str = "1.0";

/// Coverage report type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum CoverageType {
    System,
    Integration,
    Merged,
}

/// Line/branch coverage metrics
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CoverageMetrics {
    pub total: usize,
    pub covered: usize,
    pub percent: f64,
}

impl CoverageMetrics {
    pub fn new(total: usize, covered: usize) -> Self {
        let percent = if total == 0 {
            100.0
        } else {
            (covered as f64 / total as f64) * 100.0
        };
        Self {
            total,
            covered,
            percent,
        }
    }

    pub fn add(&mut self, other: &CoverageMetrics) {
        self.total += other.total;
        self.covered += other.covered;
        self.percent = if self.total == 0 {
            100.0
        } else {
            (self.covered as f64 / self.total as f64) * 100.0
        };
    }
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

/// Overall coverage summary
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ExtendedCoverageSummary {
    pub total_types: usize,
    pub covered_types: usize,
    pub type_coverage_percent: f64,
    pub total_methods: usize,
    pub covered_methods: usize,
    pub method_coverage_percent: f64,
    pub total_functions: usize,
    pub covered_functions: usize,
    pub function_coverage_percent: f64,
    pub total_lines: usize,
    pub covered_lines: usize,
    pub line_coverage_percent: f64,
    pub total_branches: usize,
    pub covered_branches: usize,
    pub branch_coverage_percent: f64,
}

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
            uncovered: UncoveredSummary::default(),
        }
    }

    /// Check if coverage meets threshold
    pub fn meets_threshold(&self, threshold: f64) -> bool {
        match self.coverage_type {
            CoverageType::System => self.summary.method_coverage_percent >= threshold,
            CoverageType::Integration => self.summary.function_coverage_percent >= threshold,
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

/// Coverage analyzer that processes LLVM coverage data
pub struct CoverageAnalyzer {
    llvm_cov: LlvmCovExport,
    api_spec: PublicApiSpec,
    llvm_file: String,
    api_file: String,
}

impl CoverageAnalyzer {
    /// Create analyzer from parsed data
    pub fn new(
        llvm_cov: LlvmCovExport,
        api_spec: PublicApiSpec,
        llvm_file: &str,
        api_file: &str,
    ) -> Self {
        Self {
            llvm_cov,
            api_spec,
            llvm_file: llvm_file.to_string(),
            api_file: api_file.to_string(),
        }
    }

    /// Load analyzer from files
    pub fn from_files<P1: AsRef<Path>, P2: AsRef<Path>>(
        llvm_cov_path: P1,
        api_spec_path: P2,
    ) -> anyhow::Result<Self> {
        let llvm_cov = crate::coverage::load_llvm_cov_export(&llvm_cov_path)?;
        let api_spec = crate::coverage::load_public_api_spec(&api_spec_path)?;
        Ok(Self::new(
            llvm_cov,
            api_spec,
            llvm_cov_path.as_ref().to_str().unwrap_or(""),
            api_spec_path.as_ref().to_str().unwrap_or(""),
        ))
    }

    /// Build function execution count map from LLVM data
    /// Demangles Rust symbol names to human-readable form
    fn build_function_counts(&self) -> HashMap<String, u64> {
        let mut counts: HashMap<String, u64> = HashMap::new();

        for data in &self.llvm_cov.data {
            for func in &data.functions {
                // Demangle Rust symbol names
                let demangled = demangle_rust_name(&func.name);
                let entry = counts.entry(demangled).or_insert(0);
                *entry = (*entry).max(func.count);
            }
        }

        counts
    }

    /// Generate system test coverage report (type/method coverage)
    pub fn generate_system_report(&self) -> ExtendedCoverageReport {
        let mut report =
            ExtendedCoverageReport::new(CoverageType::System, &self.llvm_file, &self.api_file);

        let fn_counts = self.build_function_counts();

        // Process each type in the API spec
        for (type_name, type_spec) in &self.api_spec.types {
            let mut type_cov = TypeCoverage {
                name: type_name.clone(),
                file: None,
                line_start: None,
                line_end: None,
                is_public: true,
                kind: Some("struct".to_string()),
                methods: Vec::new(),
                summary: TypeMethodSummary::default(),
            };

            let mut covered_methods = 0;
            let mut covered_public_methods = 0;

            for method_name in &type_spec.methods {
                // Look for function matching Type::method pattern using flexible matching
                let count = fn_counts
                    .iter()
                    .filter(|(k, _)| matches_type_method(k, type_name, method_name))
                    .map(|(_, v)| *v)
                    .max()
                    .unwrap_or(0);

                let covered = count > 0;
                if covered {
                    covered_methods += 1;
                    covered_public_methods += 1;
                }

                type_cov.methods.push(MethodCoverage {
                    name: method_name.clone(),
                    signature: None,
                    line_start: None,
                    line_end: None,
                    is_public: true,
                    execution_count: count,
                    covered,
                    line_coverage: None,
                    branch_coverage: None,
                });
            }

            // Update type summary
            let total = type_spec.methods.len();
            type_cov.summary = TypeMethodSummary {
                total_methods: total,
                covered_methods,
                method_coverage_percent: if total == 0 {
                    100.0
                } else {
                    (covered_methods as f64 / total as f64) * 100.0
                },
                total_public_methods: total,
                covered_public_methods,
                public_method_coverage_percent: if total == 0 {
                    100.0
                } else {
                    (covered_public_methods as f64 / total as f64) * 100.0
                },
            };

            // Track uncovered methods
            for method in &type_cov.methods {
                if !method.covered {
                    report.uncovered.methods.push(UncoveredItem {
                        type_name: Some(type_name.clone()),
                        name: method.name.clone(),
                        file: None,
                        line: None,
                    });
                }
            }

            // Update report summary
            report.summary.total_methods += total;
            report.summary.covered_methods += covered_methods;

            let type_covered = covered_methods > 0;
            if type_covered {
                report.summary.covered_types += 1;
            } else {
                report.uncovered.types.push(UncoveredItem {
                    type_name: None,
                    name: type_name.clone(),
                    file: None,
                    line: None,
                });
            }

            report.types.push(type_cov);
        }

        // Finalize summary
        report.summary.total_types = report.types.len();
        report.summary.type_coverage_percent = if report.summary.total_types == 0 {
            100.0
        } else {
            (report.summary.covered_types as f64 / report.summary.total_types as f64) * 100.0
        };
        report.summary.method_coverage_percent = if report.summary.total_methods == 0 {
            100.0
        } else {
            (report.summary.covered_methods as f64 / report.summary.total_methods as f64) * 100.0
        };

        report
    }

    /// Generate integration test coverage report (function coverage)
    pub fn generate_integration_report(&self) -> ExtendedCoverageReport {
        let mut report = ExtendedCoverageReport::new(
            CoverageType::Integration,
            &self.llvm_file,
            &self.api_file,
        );

        let fn_counts = self.build_function_counts();

        // Get list of public functions from API spec
        let public_functions: HashSet<String> = self
            .api_spec
            .types
            .iter()
            .flat_map(|(type_name, spec)| {
                spec.methods
                    .iter()
                    .map(move |m| format!("{}::{}", type_name, m))
            })
            .collect();

        // Process all functions in coverage data
        for (func_name, count) in &fn_counts {
            // Determine if this is a public function
            let is_public = public_functions.iter().any(|pf| func_name.contains(pf));

            let covered = *count > 0;

            let func_cov = FunctionCoverage {
                name: func_name
                    .split("::")
                    .last()
                    .unwrap_or(func_name)
                    .to_string(),
                qualified_name: func_name.clone(),
                file: None,
                line_start: None,
                line_end: None,
                signature: None,
                is_public,
                is_exported: is_public,
                execution_count: *count,
                covered,
                line_coverage: None,
                branch_coverage: None,
            };

            if is_public {
                report.summary.total_functions += 1;
                if covered {
                    report.summary.covered_functions += 1;
                } else {
                    report.uncovered.functions.push(UncoveredItem {
                        type_name: None,
                        name: func_name.clone(),
                        file: None,
                        line: None,
                    });
                }
            }

            report.functions.push(func_cov);
        }

        // Finalize summary
        report.summary.function_coverage_percent = if report.summary.total_functions == 0 {
            100.0
        } else {
            (report.summary.covered_functions as f64 / report.summary.total_functions as f64)
                * 100.0
        };

        report
    }

    /// Generate merged coverage report (all coverage data)
    pub fn generate_merged_report(&self) -> ExtendedCoverageReport {
        let mut report =
            ExtendedCoverageReport::new(CoverageType::Merged, &self.llvm_file, &self.api_file);

        // Get system and integration reports
        let system_report = self.generate_system_report();
        let integration_report = self.generate_integration_report();

        // Merge summaries
        report.summary.total_types = system_report.summary.total_types;
        report.summary.covered_types = system_report.summary.covered_types;
        report.summary.type_coverage_percent = system_report.summary.type_coverage_percent;
        report.summary.total_methods = system_report.summary.total_methods;
        report.summary.covered_methods = system_report.summary.covered_methods;
        report.summary.method_coverage_percent = system_report.summary.method_coverage_percent;
        report.summary.total_functions = integration_report.summary.total_functions;
        report.summary.covered_functions = integration_report.summary.covered_functions;
        report.summary.function_coverage_percent =
            integration_report.summary.function_coverage_percent;

        // Copy types and functions
        report.types = system_report.types;
        report.functions = integration_report.functions;

        // Merge uncovered items
        report.uncovered.types = system_report.uncovered.types;
        report.uncovered.methods = system_report.uncovered.methods;
        report.uncovered.functions = integration_report.uncovered.functions;

        // Calculate line coverage from function counts
        let fn_counts = self.build_function_counts();
        let total_funcs = fn_counts.len();
        let covered_funcs = fn_counts.values().filter(|&&c| c > 0).count();
        report.summary.total_lines = total_funcs; // Approximate
        report.summary.covered_lines = covered_funcs;
        report.summary.line_coverage_percent = if total_funcs == 0 {
            100.0
        } else {
            (covered_funcs as f64 / total_funcs as f64) * 100.0
        };

        report
    }

    /// Generate all reports
    pub fn generate_all_reports(
        &self,
    ) -> (
        ExtendedCoverageReport,
        ExtendedCoverageReport,
        ExtendedCoverageReport,
    ) {
        (
            self.generate_system_report(),
            self.generate_integration_report(),
            self.generate_merged_report(),
        )
    }
}

/// Print coverage summary to stdout
pub fn print_coverage_summary(report: &ExtendedCoverageReport) {
    println!("Coverage Report ({:?})", report.coverage_type);
    println!("================");
    println!("Version: {}", report.version);
    println!("Timestamp: {}", report.timestamp);
    println!();

    match report.coverage_type {
        CoverageType::System => {
            println!(
                "Types:   {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_types,
                report.summary.total_types,
                report.summary.type_coverage_percent
            );
            println!(
                "Methods: {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_methods,
                report.summary.total_methods,
                report.summary.method_coverage_percent
            );
        }
        CoverageType::Integration => {
            println!(
                "Functions: {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_functions,
                report.summary.total_functions,
                report.summary.function_coverage_percent
            );
        }
        CoverageType::Merged => {
            println!(
                "Types:     {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_types,
                report.summary.total_types,
                report.summary.type_coverage_percent
            );
            println!(
                "Methods:   {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_methods,
                report.summary.total_methods,
                report.summary.method_coverage_percent
            );
            println!(
                "Functions: {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_functions,
                report.summary.total_functions,
                report.summary.function_coverage_percent
            );
            println!(
                "Lines:     {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_lines,
                report.summary.total_lines,
                report.summary.line_coverage_percent
            );
        }
    }

    if !report.uncovered.types.is_empty()
        || !report.uncovered.methods.is_empty()
        || !report.uncovered.functions.is_empty()
    {
        println!();
        println!("Uncovered:");

        for item in &report.uncovered.types {
            println!("  Type: {}", item.name);
        }
        for item in &report.uncovered.methods {
            if let Some(type_name) = &item.type_name {
                println!("  Method: {}::{}", type_name, item.name);
            } else {
                println!("  Method: {}", item.name);
            }
        }
        for item in &report.uncovered.functions {
            println!("  Function: {}", item.name);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coverage::{parse_llvm_cov_export, parse_public_api_spec};

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
    fn test_system_report_generation() {
        let analyzer = create_test_analyzer();
        let report = analyzer.generate_system_report();

        assert_eq!(report.coverage_type, CoverageType::System);
        assert_eq!(report.summary.total_types, 2);
        assert_eq!(report.summary.covered_types, 2); // Both have at least one method covered
        assert_eq!(report.summary.total_methods, 4);
        assert_eq!(report.summary.covered_methods, 2); // method1 and run
    }

    #[test]
    fn test_integration_report_generation() {
        let analyzer = create_test_analyzer();
        let report = analyzer.generate_integration_report();

        assert_eq!(report.coverage_type, CoverageType::Integration);
        // All 4 functions in API spec
        assert_eq!(report.summary.total_functions, 4);
        assert_eq!(report.summary.covered_functions, 2);
    }

    #[test]
    fn test_merged_report_generation() {
        let analyzer = create_test_analyzer();
        let report = analyzer.generate_merged_report();

        assert_eq!(report.coverage_type, CoverageType::Merged);
        assert_eq!(report.summary.total_types, 2);
        assert_eq!(report.summary.total_methods, 4);
    }

    #[test]
    fn test_uncovered_tracking() {
        let analyzer = create_test_analyzer();
        let report = analyzer.generate_system_report();

        // Should have 2 uncovered methods
        assert_eq!(report.uncovered.methods.len(), 2);

        let uncovered_names: Vec<&str> = report
            .uncovered
            .methods
            .iter()
            .map(|u| u.name.as_str())
            .collect();
        assert!(uncovered_names.contains(&"method2"));
        assert!(uncovered_names.contains(&"stop"));
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
    fn test_coverage_metrics() {
        let metrics = CoverageMetrics::new(10, 8);
        assert_eq!(metrics.total, 10);
        assert_eq!(metrics.covered, 8);
        assert!((metrics.percent - 80.0).abs() < 0.01);
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
