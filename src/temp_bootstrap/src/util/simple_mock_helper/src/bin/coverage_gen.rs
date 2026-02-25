//! Extended Coverage Report Generator
//!
//! Generates extended coverage reports from LLVM coverage data:
//! - System test coverage (public class/struct methods)
//! - Integration test coverage (public functions)
//! - Merged coverage (all metrics combined)
//!
//! Usage:
//!   coverage_gen generate --llvm-cov coverage.json --api public_api.yml --output-dir target/coverage/
//!   coverage_gen check --coverage coverage.json --threshold 80
//!   coverage_gen summary --coverage coverage.json

use clap::{Parser, Subcommand};
use simple_mock_helper::coverage_extended::{
    print_coverage_summary, CoverageAnalyzer, CoverageType, ExtendedCoverageReport,
};
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "coverage_gen")]
#[command(about = "Generate extended coverage reports from LLVM coverage data")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Generate coverage reports
    Generate {
        /// LLVM coverage JSON file
        #[arg(long)]
        llvm_cov: PathBuf,

        /// Public API YAML specification
        #[arg(long)]
        api: PathBuf,

        /// Output directory for reports
        #[arg(long, default_value = "target/coverage")]
        output_dir: PathBuf,

        /// Report type to generate (system, integration, merged, all)
        #[arg(long, default_value = "all")]
        report_type: String,
    },

    /// Check coverage against threshold
    Check {
        /// Extended coverage JSON file
        #[arg(long)]
        coverage: PathBuf,

        /// Coverage threshold percentage
        #[arg(long, default_value = "80.0")]
        threshold: f64,
    },

    /// Print coverage summary
    Summary {
        /// Extended coverage JSON file
        #[arg(long)]
        coverage: PathBuf,
    },
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Generate {
            llvm_cov,
            api,
            output_dir,
            report_type,
        } => {
            println!("Loading coverage data from {:?}", llvm_cov);
            println!("Loading API spec from {:?}", api);

            let analyzer = CoverageAnalyzer::from_files(&llvm_cov, &api)?;

            // Create output directory if it doesn't exist
            std::fs::create_dir_all(&output_dir)?;

            match report_type.as_str() {
                "system" => {
                    let report = analyzer.generate_system_report();
                    let path = output_dir.join("coverage_system.json");
                    report.write_json(&path)?;
                    println!("System report written to {:?}", path);
                    print_coverage_summary(&report);
                }
                "integration" => {
                    let report = analyzer.generate_integration_report();
                    let path = output_dir.join("coverage_integration.json");
                    report.write_json(&path)?;
                    println!("Integration report written to {:?}", path);
                    print_coverage_summary(&report);
                }
                "merged" => {
                    let report = analyzer.generate_merged_report();
                    let path = output_dir.join("coverage_merged.json");
                    report.write_json(&path)?;
                    println!("Merged report written to {:?}", path);
                    print_coverage_summary(&report);
                }
                "all" => {
                    let (system, integration, merged) = analyzer.generate_all_reports();

                    let system_path = output_dir.join("coverage_system.json");
                    system.write_json(&system_path)?;
                    println!("System report written to {:?}", system_path);

                    let integration_path = output_dir.join("coverage_integration.json");
                    integration.write_json(&integration_path)?;
                    println!("Integration report written to {:?}", integration_path);

                    let merged_path = output_dir.join("coverage_merged.json");
                    merged.write_json(&merged_path)?;
                    println!("Merged report written to {:?}", merged_path);

                    println!();
                    println!("=== System Coverage ===");
                    print_coverage_summary(&system);
                    println!();
                    println!("=== Integration Coverage ===");
                    print_coverage_summary(&integration);
                    println!();
                    println!("=== Merged Coverage ===");
                    print_coverage_summary(&merged);
                }
                _ => {
                    anyhow::bail!("Unknown report type: {}. Use: system, integration, merged, all", report_type);
                }
            }

            Ok(())
        }

        Commands::Check { coverage, threshold } => {
            println!("Checking coverage in {:?} against {:.1}% threshold", coverage, threshold);

            let json = std::fs::read_to_string(&coverage)?;
            let report: ExtendedCoverageReport = serde_json::from_str(&json)?;

            print_coverage_summary(&report);
            println!();

            let percent = match report.coverage_type {
                CoverageType::System => report.summary.method_coverage_percent,
                CoverageType::Integration => report.summary.function_coverage_percent,
                CoverageType::Merged => report.summary.line_coverage_percent,
            };

            if report.meets_threshold(threshold) {
                println!("PASS: Coverage {:.1}% meets threshold {:.1}%", percent, threshold);
                Ok(())
            } else {
                println!("FAIL: Coverage {:.1}% below threshold {:.1}%", percent, threshold);
                std::process::exit(1);
            }
        }

        Commands::Summary { coverage } => {
            let json = std::fs::read_to_string(&coverage)?;
            let report: ExtendedCoverageReport = serde_json::from_str(&json)?;
            print_coverage_summary(&report);
            Ok(())
        }
    }
}
