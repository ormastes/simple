//! simple_mock_helper::coverage
//!
//! Utilities to derive class/struct public-method coverage from
//! LLVM coverage JSON (`llvm-cov export -format=json`).
//!
//! Pipeline:
//!   1) Merge profraw → profdata
//!   2) `llvm-cov export -format=json`
//!   3) Load `public_api.yml`
//!   4) Call `compute_class_coverage`
//!   5) Optionally use `print_class_coverage_table` or your own output.

use rustc_demangle::demangle;
use serde::Deserialize;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

/// Minimal subset of `llvm-cov export` JSON we care about.
///
/// Shape (simplified):
/// {
///   "data": [ { "functions": [ { "name": "...", "count": 0, ... }, ... ] } ]
/// }
#[derive(Debug, Deserialize)]
pub struct LlvmCovExport {
    pub data: Vec<LlvmCovData>,
}

#[derive(Debug, Deserialize)]
pub struct LlvmCovData {
    #[serde(default)]
    pub functions: Vec<LlvmFunction>,
}

#[derive(Debug, Deserialize)]
pub struct LlvmFunction {
    pub name: String,
    #[serde(default)]
    pub count: u64,
}

/// YAML specification of which types and methods you consider "public".
///
/// Example YAML:
///
/// ```yaml
/// # System Test: Types with methods
/// types:
///   MyNamespace::Foo:
///     methods: [do_stuff, reset]
///   Bar:
///     methods:
///       - run
///       - stop
///
/// # System Test: Public interface classes
/// public_classes:
///   simple_compiler:
///     - CompilerPipeline
///     - Codegen
///
/// # Service Test: Interface classes (trait implementors)
/// interfaces:
///   simple_common:
///     - DynLoader
///     - DynModule
///
/// # Service Test: External library touch points
/// external_libs:
///   cranelift: [codegen, frontend, module]
///   abfall: [GcRuntime]
///
/// # Integration Test: Neighbor package touch
/// neighbors:
///   simple_compiler:
///     depends_on: [simple_parser, simple_runtime]
///
/// # Integration Test: Public functions
/// public_functions:
///   simple_compiler:
///     - CompilerPipeline::new
///     - CompilerPipeline::compile
/// ```
#[derive(Debug, Deserialize, Default)]
pub struct PublicApiSpec {
    /// Types with methods (System test)
    #[serde(default)]
    pub types: HashMap<String, PublicTypeSpec>,

    /// Public interface classes by crate (System test)
    #[serde(default)]
    pub public_classes: HashMap<String, Vec<String>>,

    /// Interface classes (trait implementors) by crate (Service test)
    #[serde(default)]
    pub interfaces: HashMap<String, Vec<String>>,

    /// External library touch points by library name (Service test)
    #[serde(default)]
    pub external_libs: HashMap<String, Vec<String>>,

    /// Neighbor package dependencies by crate (Integration test)
    #[serde(default)]
    pub neighbors: HashMap<String, NeighborSpec>,

    /// Public functions by crate (Integration test)
    #[serde(default)]
    pub public_functions: HashMap<String, Vec<String>>,
}

#[derive(Debug, Deserialize, Default)]
pub struct PublicTypeSpec {
    #[serde(default)]
    pub methods: Vec<String>,
}

/// Neighbor package specification
#[derive(Debug, Deserialize, Default)]
pub struct NeighborSpec {
    /// List of crates this crate depends on
    #[serde(default)]
    pub depends_on: Vec<String>,
}

/// Per-method coverage result.
#[derive(Debug)]
pub struct MethodCoverage {
    pub type_name: String,
    pub method_name: String,
    pub covered: bool,
}

/// Per-type coverage result.
#[derive(Debug)]
pub struct ClassCoverage {
    pub type_name: String,
    pub total_methods: usize,
    pub covered_methods: usize,
    pub methods: Vec<MethodCoverage>,
}

/// Calculate coverage percentage from covered/total counts.
/// Returns 100.0 if total is 0 (nothing to cover = fully covered).
fn calc_coverage_percent(covered: usize, total: usize) -> f64 {
    if total == 0 {
        100.0
    } else {
        (covered as f64) * 100.0 / (total as f64)
    }
}

impl ClassCoverage {
    pub fn coverage_percent(&self) -> f64 {
        calc_coverage_percent(self.covered_methods, self.total_methods)
    }
}

/// Load LLVM coverage JSON from a file produced by:
/// `llvm-cov export -format=json`.
pub fn load_llvm_cov_export<P: AsRef<Path>>(path: P) -> anyhow::Result<LlvmCovExport> {
    let text = fs::read_to_string(path)?;
    let export: LlvmCovExport = serde_json::from_str(&text)?;
    Ok(export)
}

/// Load public API specification from a YAML file.
pub fn load_public_api_spec<P: AsRef<Path>>(path: P) -> anyhow::Result<PublicApiSpec> {
    let text = fs::read_to_string(path)?;
    let spec: PublicApiSpec = serde_yaml::from_str(&text)?;
    Ok(spec)
}

/// Compute class/struct coverage for public methods based on:
/// - LLVM coverage JSON (function list + counts).
/// - Public API spec (types + methods).
///
/// Matching rule:
///   coverage_function.name ~ "<type_name>::<method_name>" (suffix match).
///
/// If any instance of that function has non-zero count, we treat it as covered.
pub fn compute_class_coverage(cov: &LlvmCovExport, api: &PublicApiSpec) -> Vec<ClassCoverage> {
    // Flatten all functions from all "data" entries.
    // Demangle Rust symbol names to human-readable form.
    let mut fn_names_counts: Vec<(String, u64)> = Vec::new();
    for d in &cov.data {
        for f in &d.functions {
            let demangled = demangle_rust_name(&f.name);
            fn_names_counts.push((demangled, f.count));
        }
    }

    // Build a set of covered (type, method) pairs.
    let mut covered_pairs: HashSet<(String, String)> = HashSet::new();

    for (fname, count) in &fn_names_counts {
        if *count == 0 {
            continue;
        }

        // Heuristic: Rust methods typically appear as
        // "crate::module::Type::method" or "Type::method".
        if let Some((type_name, method_name)) = split_type_method(fname) {
            covered_pairs.insert((type_name.to_string(), method_name.to_string()));
        }
    }

    // For each type in public API, compute coverage.
    let mut results = Vec::new();

    for (type_name, tspec) in &api.types {
        let mut methods_cov = Vec::new();
        let mut covered_count = 0usize;

        for m in &tspec.methods {
            let key = (type_name.clone(), m.clone());
            let covered = covered_pairs.contains(&key);
            if covered {
                covered_count += 1;
            }

            methods_cov.push(MethodCoverage {
                type_name: type_name.clone(),
                method_name: m.clone(),
                covered,
            });
        }

        results.push(ClassCoverage {
            type_name: type_name.clone(),
            total_methods: tspec.methods.len(),
            covered_methods: covered_count,
            methods: methods_cov,
        });
    }

    results
}

/// Demangle a Rust symbol name to human-readable form.
///
/// Example: `_RNvNtCs...::run` -> `my_crate::module::run`
fn demangle_rust_name(mangled: &str) -> String {
    let demangled = demangle(mangled).to_string();
    // Remove hash suffix like `::h1234abcd`
    if let Some(idx) = demangled.rfind("::h") {
        if demangled[idx + 3..].chars().all(|c| c.is_ascii_hexdigit()) {
            return demangled[..idx].to_string();
        }
    }
    demangled
}

/// Split a fully-qualified function name into (type_name, method_name)
/// using a simple heuristic:
///
/// - Take everything up to last "::" as `type_name`.
/// - Take last component as `method_name`.
///
/// Returns None for free functions (no "::").
fn split_type_method(name: &str) -> Option<(&str, &str)> {
    let parts: Vec<&str> = name.split("::").collect();
    if parts.len() < 2 {
        return None;
    }
    let method_name = *parts.last().unwrap();
    let type_name = &name[..name.len() - method_name.len() - "::".len()];
    Some((type_name, method_name))
}

/// Simple pretty-printer for class coverage results.
///
/// `type_filter` is an optional substring filter on type_name.
pub fn print_class_coverage_table(results: &[ClassCoverage], type_filter: Option<&str>) {
    println!(
        "{:<50} {:>9} {:>9} {:>9}",
        "Type", "Covered", "Total", "Percent"
    );

    let mut total_methods = 0usize;
    let mut total_covered = 0usize;

    for cc in results {
        if let Some(filter) = type_filter {
            if !cc.type_name.contains(filter) {
                continue;
            }
        }

        total_methods += cc.total_methods;
        total_covered += cc.covered_methods;

        println!(
            "{:<50} {:>4} / {:<4} {:>7.2}%",
            cc.type_name,
            cc.covered_methods,
            cc.total_methods,
            cc.coverage_percent()
        );
    }

    if total_methods > 0 {
        let pct = (total_covered as f64) * 100.0 / (total_methods as f64);
        println!(
            "\nTOTAL: {}/{} public methods covered ({:.2}%)",
            total_covered, total_methods, pct
        );
    } else {
        println!("\nTOTAL: no public methods defined in public_api.yml");
    }
}

/// Parse LLVM coverage JSON from a string.
pub fn parse_llvm_cov_export(json: &str) -> anyhow::Result<LlvmCovExport> {
    let export: LlvmCovExport = serde_json::from_str(json)?;
    Ok(export)
}

/// Parse public API specification from a YAML string.
pub fn parse_public_api_spec(yaml: &str) -> anyhow::Result<PublicApiSpec> {
    let spec: PublicApiSpec = serde_yaml::from_str(yaml)?;
    Ok(spec)
}

/// Summary of coverage results.
#[derive(Debug, Clone)]
pub struct CoverageSummary {
    pub total_types: usize,
    pub total_methods: usize,
    pub covered_methods: usize,
}

impl CoverageSummary {
    /// Compute summary from class coverage results.
    pub fn from_results(results: &[ClassCoverage]) -> Self {
        let total_types = results.len();
        let total_methods: usize = results.iter().map(|c| c.total_methods).sum();
        let covered_methods: usize = results.iter().map(|c| c.covered_methods).sum();
        Self {
            total_types,
            total_methods,
            covered_methods,
        }
    }

    /// Get coverage percentage.
    pub fn coverage_percent(&self) -> f64 {
        calc_coverage_percent(self.covered_methods, self.total_methods)
    }

    /// Check if coverage meets a threshold.
    pub fn meets_threshold(&self, threshold_percent: f64) -> bool {
        self.coverage_percent() >= threshold_percent
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create ClassCoverage for tests
    fn make_class_coverage(name: &str, covered: usize, total: usize) -> ClassCoverage {
        ClassCoverage {
            type_name: name.to_string(),
            total_methods: total,
            covered_methods: covered,
            methods: vec![],
        }
    }

    /// Helper to compute coverage from JSON/YAML strings
    fn compute_coverage(cov_json: &str, api_yaml: &str) -> Vec<ClassCoverage> {
        let cov = parse_llvm_cov_export(cov_json).unwrap();
        let api = parse_public_api_spec(api_yaml).unwrap();
        compute_class_coverage(&cov, &api)
    }

    #[test]
    fn test_split_type_method() {
        assert_eq!(
            split_type_method("Namespace::Type::method"),
            Some(("Namespace::Type", "method"))
        );
        assert_eq!(split_type_method("Type::method"), Some(("Type", "method")));
        assert_eq!(split_type_method("free_function"), None);
    }

    #[test]
    fn test_split_type_method_deep_nesting() {
        assert_eq!(
            split_type_method("a::b::c::d::method"),
            Some(("a::b::c::d", "method"))
        );
    }

    #[test]
    fn test_split_type_method_empty() {
        assert_eq!(split_type_method(""), None);
        assert_eq!(split_type_method("::"), Some(("", "")));
    }

    #[test]
    fn test_class_coverage_percent() {
        assert!((make_class_coverage("Test", 2, 4).coverage_percent() - 50.0).abs() < 0.001);
    }

    #[test]
    fn test_class_coverage_percent_zero_methods() {
        assert!((make_class_coverage("Empty", 0, 0).coverage_percent() - 100.0).abs() < 0.001);
    }

    #[test]
    fn test_class_coverage_percent_full() {
        assert!((make_class_coverage("Full", 5, 5).coverage_percent() - 100.0).abs() < 0.001);
    }

    #[test]
    fn test_parse_llvm_cov_export() {
        let json = r#"{
            "data": [{
                "functions": [
                    {"name": "MyType::method1", "count": 5},
                    {"name": "MyType::method2", "count": 0},
                    {"name": "OtherType::run", "count": 10}
                ]
            }]
        }"#;

        let cov = parse_llvm_cov_export(json).unwrap();
        assert_eq!(cov.data.len(), 1);
        assert_eq!(cov.data[0].functions.len(), 3);
        assert_eq!(cov.data[0].functions[0].name, "MyType::method1");
        assert_eq!(cov.data[0].functions[0].count, 5);
    }

    #[test]
    fn test_parse_llvm_cov_export_empty() {
        let json = r#"{"data": []}"#;
        let cov = parse_llvm_cov_export(json).unwrap();
        assert!(cov.data.is_empty());
    }

    #[test]
    fn test_parse_llvm_cov_export_no_functions() {
        let json = r#"{"data": [{}]}"#;
        let cov = parse_llvm_cov_export(json).unwrap();
        assert_eq!(cov.data.len(), 1);
        assert!(cov.data[0].functions.is_empty());
    }

    #[test]
    fn test_parse_public_api_spec() {
        let yaml = r#"
types:
  MyNamespace::Foo:
    methods: [do_stuff, reset]
  Bar:
    methods:
      - run
      - stop
"#;

        let spec = parse_public_api_spec(yaml).unwrap();
        assert_eq!(spec.types.len(), 2);
        assert!(spec.types.contains_key("MyNamespace::Foo"));
        assert!(spec.types.contains_key("Bar"));
        assert_eq!(
            spec.types["MyNamespace::Foo"].methods,
            vec!["do_stuff", "reset"]
        );
        assert_eq!(spec.types["Bar"].methods, vec!["run", "stop"]);
    }

    #[test]
    fn test_parse_public_api_spec_empty() {
        let yaml = "types: {}";
        let spec = parse_public_api_spec(yaml).unwrap();
        assert!(spec.types.is_empty());
    }

    #[test]
    fn test_compute_class_coverage_basic() {
        let results = compute_coverage(
            r#"{"data": [{"functions": [
                {"name": "MyType::method1", "count": 5},
                {"name": "MyType::method2", "count": 0},
                {"name": "OtherType::run", "count": 10}
            ]}]}"#,
            "types:\n  MyType:\n    methods: [method1, method2, method3]\n  OtherType:\n    methods: [run, stop]"
        );
        assert_eq!(results.len(), 2);

        let my_type = results.iter().find(|r| r.type_name == "MyType").unwrap();
        assert_eq!(my_type.total_methods, 3);
        assert_eq!(my_type.covered_methods, 1); // only method1 is covered

        let other_type = results.iter().find(|r| r.type_name == "OtherType").unwrap();
        assert_eq!(other_type.total_methods, 2);
        assert_eq!(other_type.covered_methods, 1); // only run is covered
    }

    #[test]
    fn test_compute_class_coverage_all_covered() {
        let results = compute_coverage(
            r#"{"data": [{"functions": [{"name": "Type::a", "count": 1}, {"name": "Type::b", "count": 2}]}]}"#,
            "types:\n  Type:\n    methods: [a, b]",
        );
        let type_result = &results[0];
        assert_eq!(type_result.covered_methods, 2);
        assert!((type_result.coverage_percent() - 100.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_class_coverage_none_covered() {
        let results = compute_coverage(
            r#"{"data": [{"functions": [{"name": "Type::a", "count": 0}, {"name": "Type::b", "count": 0}]}]}"#,
            "types:\n  Type:\n    methods: [a, b]",
        );
        let type_result = &results[0];
        assert_eq!(type_result.covered_methods, 0);
        assert!((type_result.coverage_percent() - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_class_coverage_multiple_data_entries() {
        let results = compute_coverage(
            r#"{"data": [{"functions": [{"name": "Type::a", "count": 1}]}, {"functions": [{"name": "Type::b", "count": 2}]}]}"#,
            "types:\n  Type:\n    methods: [a, b, c]",
        );
        let type_result = &results[0];
        assert_eq!(type_result.total_methods, 3);
        assert_eq!(type_result.covered_methods, 2); // a and b from different data entries
    }

    #[test]
    fn test_coverage_summary() {
        let results = vec![
            make_class_coverage("A", 2, 4),
            make_class_coverage("B", 3, 6),
        ];

        let summary = CoverageSummary::from_results(&results);
        assert_eq!(summary.total_types, 2);
        assert_eq!(summary.total_methods, 10);
        assert_eq!(summary.covered_methods, 5);
        assert!((summary.coverage_percent() - 50.0).abs() < 0.001);
    }

    #[test]
    fn test_coverage_summary_empty() {
        let results: Vec<ClassCoverage> = vec![];
        let summary = CoverageSummary::from_results(&results);
        assert_eq!(summary.total_types, 0);
        assert_eq!(summary.total_methods, 0);
        assert_eq!(summary.covered_methods, 0);
        assert!((summary.coverage_percent() - 100.0).abs() < 0.001);
    }

    #[test]
    fn test_coverage_summary_meets_threshold() {
        let summary = CoverageSummary {
            total_types: 1,
            total_methods: 10,
            covered_methods: 8,
        };

        assert!(summary.meets_threshold(80.0));
        assert!(summary.meets_threshold(79.0));
        assert!(!summary.meets_threshold(81.0));
    }

    #[test]
    fn test_method_coverage_struct() {
        let mc = MethodCoverage {
            type_name: "MyType".to_string(),
            method_name: "my_method".to_string(),
            covered: true,
        };
        assert_eq!(mc.type_name, "MyType");
        assert_eq!(mc.method_name, "my_method");
        assert!(mc.covered);
    }
}
