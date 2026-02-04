//! FFI bindings for Simple coverage tool
//!
//! These functions are called from src/app/coverage/main.spl

use crate::api_scanner::{scan_directory, write_yaml};
use crate::coverage::{load_llvm_cov_export, LlvmCovExport};
use crate::coverage_extended::{print_coverage_summary, CoverageAnalyzer, ExtendedCoverageReport};
use std::collections::HashMap;
use std::ffi::CStr;
use std::os::raw::c_char;
use std::path::Path;

/// Helper to convert C string to Rust &str
unsafe fn cstr_to_str<'a>(ptr: *const c_char) -> &'a str {
    if ptr.is_null() {
        return "";
    }
    CStr::from_ptr(ptr).to_str().unwrap_or("")
}

/// Scan source directory and generate public_api.yml
#[no_mangle]
pub extern "C" fn coverage_scan(source_ptr: *const c_char, output_ptr: *const c_char) -> i64 {
    let source = unsafe { cstr_to_str(source_ptr) };
    let output = unsafe { cstr_to_str(output_ptr) };

    let source_path = Path::new(source);
    let output_path = Path::new(output);

    match scan_directory(source_path) {
        Ok(api) => {
            println!(
                "Found {} types, {} crates with public functions",
                api.types.len(),
                api.public_functions.len()
            );

            match write_yaml(&api, output_path) {
                Ok(_) => 0,
                Err(e) => {
                    eprintln!("Error writing YAML: {}", e);
                    1
                }
            }
        }
        Err(e) => {
            eprintln!("Error scanning directory: {}", e);
            1
        }
    }
}

/// Extract touched functions from coverage data
fn extract_touched_functions(cov: &LlvmCovExport) -> HashMap<String, u64> {
    let mut touched = HashMap::new();

    for data in &cov.data {
        for func in &data.functions {
            if func.count > 0 {
                let demangled = rustc_demangle::demangle(&func.name).to_string();
                touched.insert(demangled, func.count);
            }
        }
    }

    touched
}

/// Check if a function was touched
fn is_function_touched(touched: &HashMap<String, u64>, key: &str) -> bool {
    if touched.contains_key(key) {
        return true;
    }

    let parts: Vec<&str> = key.split("::").collect();
    if parts.len() >= 2 {
        let type_name = parts[parts.len() - 2];
        let method_name = parts[parts.len() - 1];

        for name in touched.keys() {
            if name.contains(&format!("{}::{}", type_name, method_name)) {
                return true;
            }
            if name.contains(type_name) && name.contains(method_name) {
                return true;
            }
        }
    }

    false
}

/// Check if a class was touched
fn is_class_touched(type_name: &str, methods: &[String], touched: &HashMap<String, u64>) -> bool {
    for method in methods {
        let key = format!("{}::{}", type_name, method);
        if is_function_touched(touched, &key) {
            return true;
        }
    }

    let normalized_name = type_name.replace("::", "");
    for name in touched.keys() {
        if name.contains(&normalized_name) {
            return true;
        }
    }

    false
}

/// Print header box
fn print_header(title: &str) {
    println!("╔══════════════════════════════════════════════════════════════════════════════╗");
    println!("║{:^78}║", title);
    println!("╚══════════════════════════════════════════════════════════════════════════════╝");
    println!();
}

/// Print summary line
fn print_summary(touched: usize, total: usize, label: &str) {
    let pct = if total > 0 {
        (touched as f64 / total as f64) * 100.0
    } else {
        100.0
    };
    println!("TOTAL: {}/{} {} ({:.1}%)", touched, total, label, pct);
}

/// Show class/struct touch coverage
#[no_mangle]
pub extern "C" fn coverage_class(
    coverage_json_ptr: *const c_char,
    source_ptr: *const c_char,
    filter_ptr: *const c_char,
) -> i64 {
    let coverage_json = unsafe { cstr_to_str(coverage_json_ptr) };
    let source = unsafe { cstr_to_str(source_ptr) };
    let filter = unsafe { cstr_to_str(filter_ptr) };
    let filter_opt = if filter.is_empty() { None } else { Some(filter) };

    let coverage_path = Path::new(coverage_json);
    let source_path = Path::new(source);

    let cov = match load_llvm_cov_export(coverage_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error loading coverage JSON: {}", e);
            return 1;
        }
    };

    let api = match scan_directory(source_path) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("Error scanning source: {}", e);
            return 1;
        }
    };

    let touched = extract_touched_functions(&cov);

    print_header("SYSTEM TEST - Class/Struct Touch Coverage");
    println!("{:<50} {:>10}", "Class/Struct", "Status");
    println!("{}", "─".repeat(62));

    let mut total_classes = 0usize;
    let mut touched_classes = 0usize;
    let mut results: Vec<_> = api.types.iter().collect();
    results.sort_by_key(|(name, _)| name.as_str());

    for (type_name, type_spec) in results {
        if let Some(f) = filter_opt {
            if !type_name.contains(f) {
                continue;
            }
        }

        let class_touched = is_class_touched(type_name, &type_spec.methods, &touched);

        total_classes += 1;
        if class_touched {
            touched_classes += 1;
        }

        let status = if class_touched {
            "✓ TOUCHED"
        } else {
            "✗ NOT TOUCHED"
        };
        println!("{:<50} {:>10}", type_name, status);
    }

    println!("{}", "─".repeat(62));
    print_summary(touched_classes, total_classes, "classes/structs touched");

    0
}

/// Show public function touch coverage
#[no_mangle]
pub extern "C" fn coverage_func(
    coverage_json_ptr: *const c_char,
    source_ptr: *const c_char,
    filter_ptr: *const c_char,
) -> i64 {
    let coverage_json = unsafe { cstr_to_str(coverage_json_ptr) };
    let source = unsafe { cstr_to_str(source_ptr) };
    let filter = unsafe { cstr_to_str(filter_ptr) };
    let filter_opt = if filter.is_empty() { None } else { Some(filter) };

    let coverage_path = Path::new(coverage_json);
    let source_path = Path::new(source);

    let cov = match load_llvm_cov_export(coverage_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error loading coverage JSON: {}", e);
            return 1;
        }
    };

    let api = match scan_directory(source_path) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("Error scanning source: {}", e);
            return 1;
        }
    };

    let touched = extract_touched_functions(&cov);

    print_header("INTEGRATION TEST - Public Function Touch Coverage");

    let mut all_functions: Vec<(String, bool)> = Vec::new();

    for (type_name, type_spec) in &api.types {
        if let Some(f) = filter_opt {
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

    for (crate_name, funcs) in &api.public_functions {
        if let Some(f) = filter_opt {
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
        let display_name = if func_name.len() > 58 {
            format!("{}...", &func_name[..55])
        } else {
            func_name.clone()
        };
        println!("{:<60} {:>10}", display_name, status);
    }

    println!("{}", "─".repeat(72));
    print_summary(total_touched, total_funcs, "public functions/methods touched");

    0
}

/// Show full coverage report (legacy)
#[no_mangle]
pub extern "C" fn coverage_report(
    coverage_json_ptr: *const c_char,
    public_api_ptr: *const c_char,
    type_filter_ptr: *const c_char,
) -> i64 {
    use crate::coverage::{compute_class_coverage, load_public_api_spec, print_class_coverage_table};

    let coverage_json = unsafe { cstr_to_str(coverage_json_ptr) };
    let public_api = unsafe { cstr_to_str(public_api_ptr) };
    let type_filter = unsafe { cstr_to_str(type_filter_ptr) };
    let filter_opt = if type_filter.is_empty() {
        None
    } else {
        Some(type_filter)
    };

    let coverage_path = Path::new(coverage_json);
    let api_path = Path::new(public_api);

    let cov = match load_llvm_cov_export(coverage_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error loading coverage JSON: {}", e);
            return 1;
        }
    };

    let api = match load_public_api_spec(api_path) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("Error loading public API spec: {}", e);
            return 1;
        }
    };

    let results = compute_class_coverage(&cov, &api);
    print_class_coverage_table(&results, filter_opt);

    0
}

/// Generate extended coverage reports
#[no_mangle]
pub extern "C" fn coverage_generate(
    llvm_cov_ptr: *const c_char,
    api_ptr: *const c_char,
    output_dir_ptr: *const c_char,
    report_type_ptr: *const c_char,
) -> i64 {
    let llvm_cov = unsafe { cstr_to_str(llvm_cov_ptr) };
    let api = unsafe { cstr_to_str(api_ptr) };
    let output_dir = unsafe { cstr_to_str(output_dir_ptr) };
    let report_type = unsafe { cstr_to_str(report_type_ptr) };

    let llvm_cov_path = Path::new(llvm_cov);
    let api_path = Path::new(api);
    let output_path = Path::new(output_dir);

    let analyzer = match CoverageAnalyzer::from_files(llvm_cov_path, api_path) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("Error loading coverage data: {}", e);
            return 1;
        }
    };

    if let Err(e) = std::fs::create_dir_all(output_path) {
        eprintln!("Error creating output directory: {}", e);
        return 1;
    }

    match report_type {
        "system" => {
            let report = analyzer.generate_system_report();
            let path = output_path.join("coverage_system.json");
            if let Err(e) = report.write_json(&path) {
                eprintln!("Error writing report: {}", e);
                return 1;
            }
            println!("System report written to {:?}", path);
            print_coverage_summary(&report);
        }
        "integration" => {
            let report = analyzer.generate_integration_report();
            let path = output_path.join("coverage_integration.json");
            if let Err(e) = report.write_json(&path) {
                eprintln!("Error writing report: {}", e);
                return 1;
            }
            println!("Integration report written to {:?}", path);
            print_coverage_summary(&report);
        }
        "merged" => {
            let report = analyzer.generate_merged_report();
            let path = output_path.join("coverage_merged.json");
            if let Err(e) = report.write_json(&path) {
                eprintln!("Error writing report: {}", e);
                return 1;
            }
            println!("Merged report written to {:?}", path);
            print_coverage_summary(&report);
        }
        "service" => {
            let report = analyzer.generate_service_report();
            let path = output_path.join("coverage_service.json");
            if let Err(e) = report.write_json(&path) {
                eprintln!("Error writing report: {}", e);
                return 1;
            }
            println!("Service report written to {:?}", path);
            print_coverage_summary(&report);
        }
        "all" => {
            let (system, service, integration, merged) = analyzer.generate_all_reports();

            let system_path = output_path.join("coverage_system.json");
            if let Err(e) = system.write_json(&system_path) {
                eprintln!("Error writing system report: {}", e);
                return 1;
            }
            println!("System report written to {:?}", system_path);

            let service_path = output_path.join("coverage_service.json");
            if let Err(e) = service.write_json(&service_path) {
                eprintln!("Error writing service report: {}", e);
                return 1;
            }
            println!("Service report written to {:?}", service_path);

            let integration_path = output_path.join("coverage_integration.json");
            if let Err(e) = integration.write_json(&integration_path) {
                eprintln!("Error writing integration report: {}", e);
                return 1;
            }
            println!("Integration report written to {:?}", integration_path);

            let merged_path = output_path.join("coverage_merged.json");
            if let Err(e) = merged.write_json(&merged_path) {
                eprintln!("Error writing merged report: {}", e);
                return 1;
            }
            println!("Merged report written to {:?}", merged_path);

            println!();
            println!("=== System Coverage ===");
            print_coverage_summary(&system);
            println!();
            println!("=== Service Coverage ===");
            print_coverage_summary(&service);
            println!();
            println!("=== Integration Coverage ===");
            print_coverage_summary(&integration);
            println!();
            println!("=== Merged Coverage ===");
            print_coverage_summary(&merged);
        }
        _ => {
            eprintln!(
                "Unknown report type: {}. Use: system, service, integration, merged, all",
                report_type
            );
            return 1;
        }
    }

    0
}

/// Check coverage against threshold
#[no_mangle]
pub extern "C" fn coverage_check(coverage_ptr: *const c_char, threshold: f64) -> i64 {
    use crate::coverage_extended::CoverageType;

    let coverage = unsafe { cstr_to_str(coverage_ptr) };
    let coverage_path = Path::new(coverage);

    let json = match std::fs::read_to_string(coverage_path) {
        Ok(j) => j,
        Err(e) => {
            eprintln!("Error reading coverage file: {}", e);
            return 1;
        }
    };

    let report: ExtendedCoverageReport = match serde_json::from_str(&json) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Error parsing coverage JSON: {}", e);
            return 1;
        }
    };

    print_coverage_summary(&report);
    println!();

    let percent = match report.coverage_type {
        CoverageType::System => report.summary.method_coverage_percent,
        CoverageType::Service => report
            .summary
            .interface_coverage_percent
            .min(report.summary.external_lib_coverage_percent),
        CoverageType::Integration => report
            .summary
            .function_coverage_percent
            .min(report.summary.neighbor_coverage_percent),
        CoverageType::Merged => report.summary.line_coverage_percent,
    };

    if report.meets_threshold(threshold) {
        println!("PASS: Coverage {:.1}% meets threshold {:.1}%", percent, threshold);
        0
    } else {
        println!("FAIL: Coverage {:.1}% below threshold {:.1}%", percent, threshold);
        1
    }
}

/// Print coverage summary
#[no_mangle]
pub extern "C" fn coverage_summary(coverage_ptr: *const c_char) -> i64 {
    let coverage = unsafe { cstr_to_str(coverage_ptr) };
    let coverage_path = Path::new(coverage);

    let json = match std::fs::read_to_string(coverage_path) {
        Ok(j) => j,
        Err(e) => {
            eprintln!("Error reading coverage file: {}", e);
            return 1;
        }
    };

    let report: ExtendedCoverageReport = match serde_json::from_str(&json) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Error parsing coverage JSON: {}", e);
            return 1;
        }
    };

    print_coverage_summary(&report);

    0
}
