//! smh_coverage - Coverage analysis tool for Simple Language Compiler
//!
//! Commands:
//!   scan     - Scan source code and generate/update public_api.yml
//!   class    - Show class/struct touch coverage (for System Tests)
//!   func     - Show public function touch coverage (for Integration Tests)
//!   report   - Show full coverage report

use std::collections::HashMap;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use simple_mock_helper::api_scanner::{scan_directory, write_yaml};
use simple_mock_helper::coverage::{load_llvm_cov_export, LlvmCovExport};

#[derive(Debug, Parser)]
#[command(name = "smh_coverage")]
#[command(about = "Coverage analysis for Simple Language Compiler")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Debug, Subcommand)]
enum Commands {
    /// Scan source code and generate/update public_api.yml
    Scan {
        /// Source directory to scan (default: src/)
        #[arg(long, default_value = "src")]
        source: PathBuf,

        /// Output YAML file (default: public_api.yml)
        #[arg(long, short, default_value = "public_api.yml")]
        output: PathBuf,
    },

    /// Show class/struct touch coverage (for System Tests)
    Class {
        /// Path to llvm-cov export JSON
        #[arg(long)]
        coverage_json: PathBuf,

        /// Source directory to scan for types (default: src/)
        #[arg(long, default_value = "src")]
        source: PathBuf,

        /// Optional filter on type name
        #[arg(long)]
        filter: Option<String>,
    },

    /// Show public function touch coverage (for Integration Tests)
    Func {
        /// Path to llvm-cov export JSON
        #[arg(long)]
        coverage_json: PathBuf,

        /// Source directory to scan for functions (default: src/)
        #[arg(long, default_value = "src")]
        source: PathBuf,

        /// Optional filter on crate/module name
        #[arg(long)]
        filter: Option<String>,
    },

    /// Show full coverage report (legacy mode with YAML)
    Report {
        /// Path to llvm-cov export JSON
        #[arg(long)]
        coverage_json: PathBuf,

        /// Path to public API YAML description
        #[arg(long)]
        public_api: PathBuf,

        /// Optional substring filter on type name
        #[arg(long)]
        type_filter: Option<String>,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Scan { source, output } => {
            cmd_scan(&source, &output)
        }
        Commands::Class { coverage_json, source, filter } => {
            cmd_class_coverage(&coverage_json, &source, filter.as_deref())
        }
        Commands::Func { coverage_json, source, filter } => {
            cmd_func_coverage(&coverage_json, &source, filter.as_deref())
        }
        Commands::Report { coverage_json, public_api, type_filter } => {
            cmd_report(&coverage_json, &public_api, type_filter.as_deref())
        }
    }
}

/// Scan source and generate YAML
fn cmd_scan(source: &PathBuf, output: &PathBuf) -> Result<()> {
    println!("Scanning source directory: {}", source.display());

    let api = scan_directory(source)?;

    println!("Found {} types, {} crates with public functions",
        api.types.len(),
        api.public_functions.len());

    write_yaml(&api, output)?;
    println!("Written to: {}", output.display());

    Ok(())
}

/// Show class/struct touch coverage for System Tests
/// Shows how many classes/structs were touched (at least one method called)
fn cmd_class_coverage(coverage_json: &PathBuf, source: &PathBuf, filter: Option<&str>) -> Result<()> {
    let cov = load_llvm_cov_export(coverage_json)
        .with_context(|| format!("Failed to load coverage JSON: {}", coverage_json.display()))?;

    let api = scan_directory(source)
        .with_context(|| format!("Failed to scan source: {}", source.display()))?;

    // Extract touched functions from coverage
    let touched = extract_touched_functions(&cov);

    println!("╔══════════════════════════════════════════════════════════════════════════════╗");
    println!("║              SYSTEM TEST - Class/Struct Touch Coverage                       ║");
    println!("╚══════════════════════════════════════════════════════════════════════════════╝");
    println!();
    println!("{:<50} {:>10}", "Class/Struct", "Status");
    println!("{}", "─".repeat(62));

    let mut total_classes = 0usize;
    let mut touched_classes = 0usize;
    let mut results: Vec<_> = api.types.iter().collect();
    results.sort_by_key(|(name, _)| name.as_str());

    for (type_name, type_spec) in results {
        if let Some(f) = filter {
            if !type_name.contains(f) {
                continue;
            }
        }

        // Check if ANY method of this class was touched
        let mut class_touched = false;
        for method in &type_spec.methods {
            let key = format!("{}::{}", type_name, method);
            if is_function_touched(&touched, &key) {
                class_touched = true;
                break;
            }
        }

        // Also check if the type itself appears in touched functions (e.g., constructors)
        if !class_touched {
            for (name, _) in &touched {
                if name.contains(&type_name.replace("::", "")) {
                    class_touched = true;
                    break;
                }
            }
        }

        total_classes += 1;
        if class_touched {
            touched_classes += 1;
        }

        let status = if class_touched { "✓ TOUCHED" } else { "✗ NOT TOUCHED" };
        println!("{:<50} {:>10}", type_name, status);
    }

    println!("{}", "─".repeat(62));
    let total_pct = if total_classes > 0 { (touched_classes as f64 / total_classes as f64) * 100.0 } else { 100.0 };
    println!("TOTAL: {}/{} classes/structs touched ({:.1}%)", touched_classes, total_classes, total_pct);

    Ok(())
}

/// Show public function touch coverage for Integration Tests
/// Shows ALL public functions (standalone + methods) touch count
fn cmd_func_coverage(coverage_json: &PathBuf, source: &PathBuf, filter: Option<&str>) -> Result<()> {
    let cov = load_llvm_cov_export(coverage_json)
        .with_context(|| format!("Failed to load coverage JSON: {}", coverage_json.display()))?;

    let api = scan_directory(source)
        .with_context(|| format!("Failed to scan source: {}", source.display()))?;

    // Extract touched functions from coverage
    let touched = extract_touched_functions(&cov);

    println!("╔══════════════════════════════════════════════════════════════════════════════╗");
    println!("║          INTEGRATION TEST - Public Function Touch Coverage                   ║");
    println!("╚══════════════════════════════════════════════════════════════════════════════╝");
    println!();

    // Collect ALL public functions (methods + standalone)
    let mut all_functions: Vec<(String, bool)> = Vec::new();

    // Add all methods from types
    for (type_name, type_spec) in &api.types {
        if let Some(f) = filter {
            if !type_name.contains(f) {
                continue;
            }
        }
        for method in &type_spec.methods {
            let key = format!("{}::{}", type_name, method);
            let is_touched = is_function_touched(&touched, &key);
            all_functions.push((key, is_touched));
        }
    }

    // Add standalone public functions
    for (crate_name, funcs) in &api.public_functions {
        if let Some(f) = filter {
            if !crate_name.contains(f) {
                continue;
            }
        }
        for func in funcs {
            let key = format!("{}::{}", crate_name, func);
            let is_touched = is_function_touched(&touched, &key);
            all_functions.push((key, is_touched));
        }
    }

    // Sort and display
    all_functions.sort_by(|a, b| a.0.cmp(&b.0));

    println!("{:<60} {:>10}", "Public Function/Method", "Status");
    println!("{}", "─".repeat(72));

    let mut total_touched = 0usize;
    let total_funcs = all_functions.len();

    for (func_name, is_touched) in &all_functions {
        if *is_touched {
            total_touched += 1;
        }
        let status = if *is_touched { "✓ TOUCHED" } else { "✗ NOT TOUCHED" };
        // Truncate long names
        let display_name = if func_name.len() > 58 {
            format!("{}...", &func_name[..55])
        } else {
            func_name.clone()
        };
        println!("{:<60} {:>10}", display_name, status);
    }

    println!("{}", "─".repeat(72));
    let total_pct = if total_funcs > 0 { (total_touched as f64 / total_funcs as f64) * 100.0 } else { 100.0 };
    println!("TOTAL: {}/{} public functions/methods touched ({:.1}%)", total_touched, total_funcs, total_pct);

    Ok(())
}

/// Legacy report mode with YAML file
fn cmd_report(coverage_json: &PathBuf, public_api: &PathBuf, type_filter: Option<&str>) -> Result<()> {
    use simple_mock_helper::coverage::{compute_class_coverage, load_public_api_spec, print_class_coverage_table};

    let cov = load_llvm_cov_export(coverage_json)?;
    let api = load_public_api_spec(public_api)?;

    let results = compute_class_coverage(&cov, &api);
    print_class_coverage_table(&results, type_filter);

    Ok(())
}

/// Extract touched functions from coverage data.
/// Returns a map of demangled function names to their execution counts.
fn extract_touched_functions(cov: &LlvmCovExport) -> HashMap<String, u64> {
    let mut touched = HashMap::new();

    for data in &cov.data {
        for func in &data.functions {
            if func.count > 0 {
                // Try to demangle the function name
                let demangled = demangle_rust_symbol(&func.name);
                touched.insert(demangled, func.count);
            }
        }
    }

    touched
}

/// Check if a function was touched (by checking various name patterns)
fn is_function_touched(touched: &HashMap<String, u64>, key: &str) -> bool {
    // Direct match
    if touched.contains_key(key) {
        return true;
    }

    // Check if any touched function contains this pattern
    // e.g., "simple_driver::Runner::new" might appear as part of a longer mangled name
    let parts: Vec<&str> = key.split("::").collect();
    if parts.len() >= 2 {
        let type_name = parts[parts.len() - 2];
        let method_name = parts[parts.len() - 1];

        for (name, _count) in touched {
            // Check for pattern like "Type::method" in demangled name
            if name.contains(&format!("{}::{}", type_name, method_name)) {
                return true;
            }
            // Check for pattern in mangled name (has type and method as substrings)
            if name.contains(type_name) && name.contains(method_name) {
                return true;
            }
        }
    }

    false
}

/// Demangle Rust symbol using rustc-demangle
fn demangle_rust_symbol(mangled: &str) -> String {
    rustc_demangle::demangle(mangled).to_string()
}
