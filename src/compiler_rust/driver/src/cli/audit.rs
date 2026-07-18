//! Build audit commands: spec coverage, build replay.

use simple_compiler::{find_spec_file, BuildLog, SpecCoverageReport};
use simple_sdn::{parse_document, SdnValue};
use std::fs;
use std::path::Path;
use std::path::PathBuf;

/// Show specification coverage report
pub fn run_spec_coverage(args: &[String]) -> i32 {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        println!("Usage: simple spec-coverage [options]");
        println!();
        println!("Options:");
        println!("  --log-mode=<human|json>  Output mode");
        println!("  --progress=<summary|dot> Progress rendering");
        println!("  --by-category            Show coverage by group");
        println!("  --missing                Show incomplete features");
        return 0;
    }
    let log_mode = match parse_log_mode(args) {
        Ok(mode) => mode,
        Err(message) => {
            eprintln!("{}", message);
            return 1;
        }
    };
    let as_json = log_mode == "json" || args.iter().any(|arg| arg == "--json");
    let tracking_db = Path::new("doc/08_tracking/feature/feature_db.sdn");
    if tracking_db.exists() {
        return run_tracking_spec_coverage(args, as_json, tracking_db);
    }
    if as_json {
        println!("{{\"command\":\"spec-coverage\",\"status\":\"error\",\"total\":0,\"complete\":0,\"in_progress\":0,\"planned\":0,\"failed\":0,\"coverage\":0}}");
        return 1;
    }

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

fn run_tracking_spec_coverage(args: &[String], as_json: bool, path: &Path) -> i32 {
    let counts = match load_tracking_feature_counts(path) {
        Ok(counts) => counts,
        Err(e) => {
            if as_json {
                println!("{{\"command\":\"spec-coverage\",\"status\":\"error\",\"total\":0,\"complete\":0,\"in_progress\":0,\"planned\":0,\"failed\":0,\"coverage\":0}}");
            } else {
                eprintln!("error: {}", e);
            }
            return 1;
        }
    };
    let coverage = if counts.total > 0 {
        counts.complete * 100 / counts.total
    } else {
        0
    };
    if as_json {
        println!(
            "{{\"command\":\"spec-coverage\",\"status\":\"ok\",\"total\":{},\"complete\":{},\"in_progress\":{},\"planned\":{},\"failed\":{},\"coverage\":{}}}",
            counts.total, counts.complete, counts.current, counts.request, counts.failed, coverage
        );
        return 0;
    }
    let progress = parse_named_arg(args, "progress").unwrap_or_else(|| "summary".to_string());
    if progress == "dot" || args.iter().any(|arg| arg == "--dots") {
        println!(".");
    }
    println!("Simple Language Specification Coverage");
    println!();
    println!("Total features: {}", counts.total);
    println!("Done: {} ({}%)", counts.complete, coverage);
    if counts.current > 0 {
        println!("Current: {}", counts.current);
    }
    if counts.request > 0 {
        println!("Request: {}", counts.request);
    }
    if counts.failed > 0 {
        println!("Failed: {}", counts.failed);
    }
    println!();
    println!("Overall Coverage: {}%", coverage);
    0
}

#[derive(Default)]
struct TrackingCoverageCounts {
    total: i64,
    complete: i64,
    current: i64,
    request: i64,
    failed: i64,
}

fn load_tracking_feature_counts(path: &Path) -> Result<TrackingCoverageCounts, String> {
    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let doc = parse_document(&content).map_err(|e| e.to_string())?;
    let root = doc.root();
    let table = match root {
        SdnValue::Dict(dict) => dict.get("features"),
        _ => None,
    };
    let (fields, rows) = match table {
        Some(SdnValue::Table {
            fields: Some(fields),
            rows,
            ..
        }) => (fields, rows),
        Some(SdnValue::Table { fields: None, .. }) => return Err("features table missing fields".to_string()),
        None => return Err("features table missing".to_string()),
        _ => return Err("features must be a table".to_string()),
    };
    let status_idx = fields.iter().position(|field| field == "status").unwrap_or(6);
    let valid_idx = fields.iter().position(|field| field == "valid").unwrap_or(26);
    let mut counts = TrackingCoverageCounts::default();
    for row in rows {
        let valid = row
            .get(valid_idx)
            .map(sdn_to_string)
            .unwrap_or_else(|| "true".to_string());
        if valid != "true" {
            continue;
        }
        counts.total += 1;
        let status = row
            .get(status_idx)
            .map(sdn_to_string)
            .unwrap_or_else(|| "request".to_string());
        match status.as_str() {
            "done" | "complete" => counts.complete += 1,
            "current" | "in_progress" => counts.current += 1,
            "request" | "planned" => counts.request += 1,
            "blocked" | "failed" | "rejected" => counts.failed += 1,
            _ => {}
        }
    }
    Ok(counts)
}

fn sdn_to_string(value: &SdnValue) -> String {
    match value {
        SdnValue::Null => String::new(),
        SdnValue::Bool(value) => value.to_string(),
        SdnValue::Int(value) => value.to_string(),
        SdnValue::Float(value) => value.to_string(),
        SdnValue::String(value) => value.clone(),
        other => other.to_string(),
    }
}

fn parse_named_arg(args: &[String], name: &str) -> Option<String> {
    let prefix = format!("--{}=", name);
    for (idx, arg) in args.iter().enumerate() {
        if let Some(value) = arg.strip_prefix(&prefix) {
            return Some(value.to_string());
        }
        if arg == &format!("--{}", name) {
            if let Some(value) = args.get(idx + 1) {
                return Some(value.clone());
            }
        }
    }
    None
}

fn parse_log_mode(args: &[String]) -> Result<String, String> {
    let mode = parse_named_arg(args, "log-mode").unwrap_or_else(|| {
        if args.iter().any(|arg| arg == "--json") {
            "json".to_string()
        } else {
            "human".to_string()
        }
    });
    match mode.as_str() {
        "human" | "json" | "llm" | "quiet" => Ok(mode),
        other => Err(format!("invalid log mode: {}", other)),
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

        println!("  Duration difference: {:+} ms", comparison.duration_difference_ms);
        println!();

        if !comparison.phase_differences.is_empty() {
            println!("  Phase differences:");
            for diff in &comparison.phase_differences {
                println!(
                    "    {}: {:+} ms{}",
                    diff.phase_name,
                    diff.duration_diff_ms,
                    if diff.result_changed { " (result changed)" } else { "" }
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
                println!("{}:{}:{}: {}: {}", file, line, column, level_str, diag.message);
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
            phase.error.as_ref().map(|e| format!(" ({})", e)).unwrap_or_default()
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
