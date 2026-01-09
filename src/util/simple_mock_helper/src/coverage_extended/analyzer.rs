//! Coverage analyzer implementation

use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::coverage::{LlvmCovExport, PublicApiSpec};

use super::report::ExtendedCoverageReport;
use super::types::{
    CoverageType, ExternalLibCoverage, FunctionCoverage, InterfaceCoverage, MethodCoverage,
    TypeCoverage, TypeMethodSummary, UncoveredItem,
};
use super::utils::{demangle_rust_name, matches_type_method};

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
        let mut report =
            ExtendedCoverageReport::new(CoverageType::Integration, &self.llvm_file, &self.api_file);

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

    /// Generate service test coverage report (interface + external lib coverage)
    pub fn generate_service_report(&self) -> ExtendedCoverageReport {
        let mut report =
            ExtendedCoverageReport::new(CoverageType::Service, &self.llvm_file, &self.api_file);

        let fn_counts = self.build_function_counts();

        // Process interfaces from API spec
        for (crate_name, interfaces) in &self.api_spec.interfaces {
            for interface_name in interfaces {
                // Look for any function that matches the interface pattern
                let count = fn_counts
                    .iter()
                    .filter(|(k, _)| {
                        k.contains(interface_name)
                            || k.contains(&format!("{}::", interface_name))
                            || k.contains(&format!("<{}", interface_name))
                    })
                    .map(|(_, v)| *v)
                    .max()
                    .unwrap_or(0);

                let touched = count > 0;

                report.interfaces.push(InterfaceCoverage {
                    name: interface_name.clone(),
                    crate_name: Some(crate_name.clone()),
                    touched,
                    execution_count: count,
                });

                report.summary.total_interfaces += 1;
                if touched {
                    report.summary.covered_interfaces += 1;
                }
            }
        }

        // Process external libraries from API spec
        for (lib_name, modules) in &self.api_spec.external_libs {
            for module_name in modules {
                // Look for any function that mentions the library module
                let count = fn_counts
                    .iter()
                    .filter(|(k, _)| {
                        k.contains(&format!("{}::{}", lib_name, module_name))
                            || k.contains(&format!("{}::{}::", lib_name, module_name))
                    })
                    .map(|(_, v)| *v)
                    .max()
                    .unwrap_or(0);

                let touched = count > 0;

                report.external_libs.push(ExternalLibCoverage {
                    library: lib_name.clone(),
                    module: module_name.clone(),
                    touched,
                    execution_count: count,
                });

                report.summary.total_external_libs += 1;
                if touched {
                    report.summary.covered_external_libs += 1;
                }
            }
        }

        // Finalize summary
        report.summary.interface_coverage_percent = if report.summary.total_interfaces == 0 {
            100.0
        } else {
            (report.summary.covered_interfaces as f64 / report.summary.total_interfaces as f64)
                * 100.0
        };

        report.summary.external_lib_coverage_percent = if report.summary.total_external_libs == 0 {
            100.0
        } else {
            (report.summary.covered_external_libs as f64
                / report.summary.total_external_libs as f64)
                * 100.0
        };

        report
    }

    /// Generate all reports (System, Service, Integration, Merged)
    pub fn generate_all_reports(
        &self,
    ) -> (
        ExtendedCoverageReport,
        ExtendedCoverageReport,
        ExtendedCoverageReport,
        ExtendedCoverageReport,
    ) {
        (
            self.generate_system_report(),
            self.generate_service_report(),
            self.generate_integration_report(),
            self.generate_merged_report(),
        )
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
}
