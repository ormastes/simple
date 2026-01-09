//! Build audit commands: spec coverage, build replay.

use simple_compiler::{find_spec_file, BuildLog, SpecCoverageReport};
use std::path::PathBuf;

/// Show specification coverage report
pub fn run_spec_coverage(args: &[String]) -> i32 {
    // Find the spec file
    let spec_path = match find_spec_file() {
        Ok(path) => path,
        Err(e) => {
            eprintln!("error: {}", e);
            eprintln!("Make sure specs/language.yaml exists in the project root");
            return 1;
        }
    };

    // Load the spec coverage report
    let report = match SpecCoverageReport::load(&spec_path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    // Parse options
    let by_category = args.iter().any(|a| a == "--by-category");
    let show_missing = args.iter().any(|a| a == "--missing");
    let html_report = args
        .iter()
        .find(|a| a.starts_with("--report="))
        .and_then(|a| a.strip_prefix("--report="));

    // Generate requested output
    if let Some("html") = html_report {
        println!("{}", report.generate_html());
        0
    } else if by_category {
        report.display_by_category();
        0
    } else if show_missing {
        report.display_missing();
        0
    } else {
        report.display_summary();
        0
    }
}

/// Replay and analyze build logs
pub fn run_replay(args: &[String]) -> i32 {
    // Parse options
    let compare_mode = args.iter().any(|a| a == "--compare");
    let extract_errors = args.iter().any(|a| a == "--extract-errors");

    if compare_mode {
        // Compare two build logs
        if args.len() < 3 {
            eprintln!("error: --compare requires two log files");
            eprintln!("Usage: simple replay --compare build1.json build2.json");
            return 1;
        }

        let log1_path = PathBuf::from(&args[1]);
        let log2_path = PathBuf::from(&args[2]);

        let log1 = match BuildLog::load(&log1_path) {
            Ok(l) => l,
            Err(e) => {
                eprintln!("error loading {}: {}", log1_path.display(), e);
                return 1;
            }
        };

        let log2 = match BuildLog::load(&log2_path) {
            Ok(l) => l,
            Err(e) => {
                eprintln!("error loading {}: {}", log2_path.display(), e);
                return 1;
            }
        };

        let comparison = log1.compare(&log2);

        println!("Build Comparison:");
        println!("  Session 1: {}", comparison.session1);
        println!("  Session 2: {}", comparison.session2);
        println!();

        if comparison.result_changed {
            println!("  ⚠ Build result changed!");
            println!();
        }

        println!(
            "  Duration difference: {:+} ms",
            comparison.duration_difference_ms
        );
        println!();

        if !comparison.phase_differences.is_empty() {
            println!("  Phase differences:");
            for diff in &comparison.phase_differences {
                println!(
                    "    {}: {:+} ms{}",
                    diff.phase_name,
                    diff.duration_diff_ms,
                    if diff.result_changed {
                        " (result changed)"
                    } else {
                        ""
                    }
                );
            }
        } else {
            println!("  No significant phase differences (< 5ms)");
        }

        return 0;
    }

    if extract_errors {
        // Extract errors from build log
        if args.len() < 2 {
            eprintln!("error: --extract-errors requires a log file");
            eprintln!("Usage: simple replay --extract-errors build.json");
            return 1;
        }

        let log_path = PathBuf::from(&args[1]);
        let log = match BuildLog::load(&log_path) {
            Ok(l) => l,
            Err(e) => {
                eprintln!("error: {}", e);
                return 1;
            }
        };

        println!("Diagnostics from {}:", log_path.display());
        println!();

        for diag in &log.diagnostics {
            let level_str = match diag.level {
                simple_compiler::DiagnosticLevel::Error => "error",
                simple_compiler::DiagnosticLevel::Warning => "warning",
                simple_compiler::DiagnosticLevel::Info => "info",
            };

            if let (Some(file), Some(line), Some(column)) = (&diag.file, diag.line, diag.column) {
                println!(
                    "{}:{}:{}: {}: {}",
                    file, line, column, level_str, diag.message
                );
            } else {
                println!("{}: {}", level_str, diag.message);
            }
        }

        return if log.error_count() > 0 { 1 } else { 0 };
    }

    // Default: display build log
    if args.len() < 2 {
        eprintln!("error: replay requires a log file");
        eprintln!("Usage: simple replay build.json");
        eprintln!("       simple replay --compare build1.json build2.json");
        eprintln!("       simple replay --extract-errors build.json");
        return 1;
    }

    let log_path = PathBuf::from(&args[1]);
    let log = match BuildLog::load(&log_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    // Display build log summary
    println!("Build Log: {}", log_path.display());
    println!();
    println!("Session ID: {}", log.session_id);
    println!("Timestamp: {}", log.timestamp);
    println!("Compiler: {}", log.compiler_version);
    println!("Command: {}", log.command);
    println!("Working Dir: {}", log.environment.working_dir);
    println!();

    println!("Input Files:");
    for file in &log.inputs.source_files {
        println!("  - {}", file);
    }
    println!();

    if !log.inputs.dependencies.is_empty() {
        println!("Dependencies:");
        for (name, version) in &log.inputs.dependencies {
            println!("  - {} = {}", name, version);
        }
        println!();
    }

    println!("Compilation Phases:");
    for phase in &log.phases {
        let result_str = match phase.result {
            simple_compiler::PhaseResult::Success => "✓",
            simple_compiler::PhaseResult::Failed => "✗",
            simple_compiler::PhaseResult::Skipped => "⊘",
        };
        println!(
            "  {} {}: {} ms{}",
            result_str,
            phase.name,
            phase.duration_ms,
            phase
                .error
                .as_ref()
                .map(|e| format!(" ({})", e))
                .unwrap_or_default()
        );
    }
    println!();

    println!("Total Duration: {} ms", log.total_duration_ms());
    println!();

    if let Some(output) = &log.output {
        println!("Output:");
        println!("  Binary: {}", output.binary);
        println!("  Size: {} bytes", output.size_bytes);
        println!("  Hash: {}", output.hash);
        println!();
    }

    let result_str = match log.result {
        simple_compiler::BuildResult::Success => "SUCCESS",
        simple_compiler::BuildResult::Failed => "FAILED",
        simple_compiler::BuildResult::Cancelled => "CANCELLED",
    };
    println!("Build Result: {}", result_str);

    if !log.diagnostics.is_empty() {
        println!();
        println!(
            "Diagnostics: {} errors, {} warnings",
            log.error_count(),
            log.warning_count()
        );
    }

    if log.error_count() > 0 {
        1
    } else {
        0
    }
}
