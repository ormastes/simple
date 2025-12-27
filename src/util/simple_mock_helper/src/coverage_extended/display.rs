//! Coverage display utilities

use super::report::ExtendedCoverageReport;
use super::types::CoverageType;

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
        CoverageType::Service => {
            println!(
                "Interfaces:    {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_interfaces,
                report.summary.total_interfaces,
                report.summary.interface_coverage_percent
            );
            println!(
                "External Libs: {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_external_libs,
                report.summary.total_external_libs,
                report.summary.external_lib_coverage_percent
            );
        }
        CoverageType::Integration => {
            println!(
                "Functions: {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_functions,
                report.summary.total_functions,
                report.summary.function_coverage_percent
            );
            println!(
                "Neighbors: {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_neighbors,
                report.summary.total_neighbors,
                report.summary.neighbor_coverage_percent
            );
        }
        CoverageType::Merged => {
            println!(
                "Types:         {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_types,
                report.summary.total_types,
                report.summary.type_coverage_percent
            );
            println!(
                "Methods:       {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_methods,
                report.summary.total_methods,
                report.summary.method_coverage_percent
            );
            println!(
                "Interfaces:    {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_interfaces,
                report.summary.total_interfaces,
                report.summary.interface_coverage_percent
            );
            println!(
                "External Libs: {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_external_libs,
                report.summary.total_external_libs,
                report.summary.external_lib_coverage_percent
            );
            println!(
                "Functions:     {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_functions,
                report.summary.total_functions,
                report.summary.function_coverage_percent
            );
            println!(
                "Neighbors:     {:>4}/{:<4} ({:.1}%)",
                report.summary.covered_neighbors,
                report.summary.total_neighbors,
                report.summary.neighbor_coverage_percent
            );
            println!(
                "Lines:         {:>4}/{:<4} ({:.1}%)",
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
