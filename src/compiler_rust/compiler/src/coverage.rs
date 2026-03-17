// Coverage module — full implementation
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Mutex;

#[derive(Debug, Clone, Default)]
pub struct SourceLoc {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

#[derive(Debug, Clone, Default)]
pub struct Condition {
    pub id: u64,
    pub loc: SourceLoc,
    pub true_count: u64,
    pub false_count: u64,
}

#[derive(Debug, Clone, Default)]
pub struct Decision {
    pub id: u64,
    pub conditions: Vec<Condition>,
}

#[derive(Debug, Clone, Default)]
pub struct ExecutionPath {
    pub id: u64,
    pub blocks: Vec<u64>,
    pub count: u64,
}

#[derive(Debug, Clone, Default)]
pub struct FunctionCoverage {
    pub name: String,
    pub lines_hit: u64,
    pub lines_total: u64,
    pub branches_hit: u64,
    pub branches_total: u64,
}

#[derive(Debug, Clone, Default)]
pub struct ModuleCoverage {
    pub name: String,
    pub functions: Vec<FunctionCoverage>,
}

#[derive(Debug, Clone, Default)]
pub struct CoverageStats {
    pub lines_hit: u64,
    pub lines_total: u64,
    pub total_lines: u64,
    pub branches_hit: u64,
    pub branches_total: u64,
    pub functions_hit: u64,
    pub functions_total: u64,
    pub total_functions: u64,
    pub total_files: u64,
    pub total_ffi_calls: u64,
}

#[derive(Debug, Clone, Default)]
pub struct CoverageReport {
    pub modules: Vec<ModuleCoverage>,
    pub stats: CoverageStats,
}

#[derive(Debug, Clone, Default)]
pub struct CoverageSummary {
    pub stats: CoverageStats,
}

pub struct CoverageCollector {
    test_name: Option<String>,
    lines: HashMap<String, HashSet<usize>>,
    function_calls: HashMap<String, u64>,
    ffi_calls: HashMap<String, u64>,
}

impl Default for CoverageCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl CoverageCollector {
    pub fn new() -> Self {
        Self {
            test_name: None,
            lines: HashMap::new(),
            function_calls: HashMap::new(),
            ffi_calls: HashMap::new(),
        }
    }

    pub fn new_for_test(name: String) -> Self {
        Self { test_name: Some(name), ..Self::new() }
    }

    pub fn has_data(&self) -> bool {
        !self.lines.is_empty() || !self.function_calls.is_empty() || !self.ffi_calls.is_empty()
    }

    // ---- Line coverage ----

    pub fn record_line(&mut self, file: impl AsRef<Path>, line: usize) {
        let path = file.as_ref().display().to_string();
        self.lines.entry(path).or_default().insert(line);
    }

    pub fn lines_for_file(&self, file: &Path) -> Option<Vec<usize>> {
        let key = file.display().to_string();
        self.lines.get(&key).map(|set| {
            let mut v: Vec<usize> = set.iter().copied().collect();
            v.sort();
            v
        })
    }

    pub fn is_line_executed(&self, file: &Path, line: usize) -> bool {
        let key = file.display().to_string();
        self.lines.get(&key).map_or(false, |set| set.contains(&line))
    }

    pub fn was_file_executed(&self, file: &Path) -> bool {
        let key = file.display().to_string();
        self.lines.contains_key(&key)
    }

    pub fn executed_files(&self) -> Vec<String> {
        self.lines.keys().cloned().collect()
    }

    pub fn file_coverage_percentage(&self, file: &Path, total_lines: u64) -> f64 {
        let key = file.display().to_string();
        let covered = self.lines.get(&key).map_or(0, |s| s.len()) as u64;
        if total_lines == 0 { return 100.0; }
        (covered as f64 / total_lines as f64) * 100.0
    }

    // ---- Function coverage ----

    pub fn record_function_call(&mut self, name: &str) {
        *self.function_calls.entry(name.to_string()).or_insert(0) += 1;
    }

    pub fn was_function_called(&self, name: &str) -> bool {
        self.function_calls.get(name).map_or(false, |&c| c > 0)
    }

    pub fn function_call_count(&self, name: &str) -> u64 {
        self.function_calls.get(name).copied().unwrap_or(0)
    }

    pub fn called_functions(&self) -> Vec<String> {
        self.function_calls.iter().filter(|(_, &c)| c > 0).map(|(n, _)| n.clone()).collect()
    }

    // ---- FFI call coverage ----

    pub fn record_ffi_call(&mut self, name: &str) {
        *self.ffi_calls.entry(name.to_string()).or_insert(0) += 1;
    }

    pub fn ffi_call_count(&self, name: &str) -> u64 {
        self.ffi_calls.get(name).copied().unwrap_or(0)
    }

    // ---- Merge ----

    pub fn merge(&mut self, other: &CoverageCollector) {
        for (file, lines) in &other.lines {
            self.lines.entry(file.clone()).or_default().extend(lines);
        }
        for (name, &count) in &other.function_calls {
            *self.function_calls.entry(name.clone()).or_insert(0) += count;
        }
        for (name, &count) in &other.ffi_calls {
            *self.ffi_calls.entry(name.clone()).or_insert(0) += count;
        }
    }

    // ---- Validation ----

    pub fn validate_minimum_coverage(&self, min_lines: u64, min_functions: u64) -> Result<(), String> {
        let stats = self.stats();
        if stats.total_lines < min_lines {
            return Err(format!("Insufficient line coverage: {} < {} required", stats.total_lines, min_lines));
        }
        if stats.functions_hit < min_functions {
            return Err(format!("Insufficient function coverage: {} < {} required", stats.functions_hit, min_functions));
        }
        Ok(())
    }

    // ---- Stats ----

    pub fn stats(&self) -> CoverageStats {
        let total_lines: u64 = self.lines.values().map(|s| s.len() as u64).sum();
        let total_functions = self.function_calls.len() as u64;
        let functions_hit = self.function_calls.values().filter(|&&c| c > 0).count() as u64;
        let total_files = self.lines.len() as u64;
        let total_ffi_calls: u64 = self.ffi_calls.values().sum();
        CoverageStats {
            total_lines,
            lines_hit: total_lines,
            lines_total: total_lines,
            total_functions,
            functions_hit,
            functions_total: total_functions,
            total_files,
            total_ffi_calls,
            ..CoverageStats::default()
        }
    }

    // ---- Clear ----

    pub fn clear(&mut self) {
        self.lines.clear();
        self.function_calls.clear();
        self.ffi_calls.clear();
    }

    // ---- Summary ----

    pub fn summary_report(&self) -> String {
        let stats = self.stats();
        format!(
            "Coverage: {} lines in {} files, {} functions ({} called), {} FFI calls",
            stats.total_lines, stats.total_files, stats.total_functions,
            stats.functions_hit, stats.total_ffi_calls
        )
    }

    // ---- SDN output (delegates to runtime for decision/condition data) ----

    pub fn to_sdn(&self) -> String {
        let sdn = unsafe {
            let ptr = simple_runtime::rt_coverage_dump_sdn();
            if ptr.is_null() { return String::new(); }
            let s = std::ffi::CStr::from_ptr(ptr).to_string_lossy().to_string();
            simple_runtime::rt_coverage_free_sdn(ptr);
            s
        };
        sdn
    }
}

static GLOBAL_COVERAGE: std::sync::OnceLock<Mutex<CoverageCollector>> = std::sync::OnceLock::new();

pub fn get_global_coverage() -> Option<&'static Mutex<CoverageCollector>> {
    GLOBAL_COVERAGE.get()
}

pub fn init_global_coverage() {
    let _ = GLOBAL_COVERAGE.set(Mutex::new(CoverageCollector::new()));
}

pub fn init_coverage() {
    init_global_coverage();
}

/// Initialize coverage if environment variable is set
pub fn init_coverage_from_env() {
    if std::env::var("SIMPLE_COVERAGE").is_ok() {
        init_global_coverage();
    }
}

pub fn is_coverage_enabled() -> bool {
    GLOBAL_COVERAGE.get().is_some()
}

pub fn save_global_coverage() -> Result<(), String> {
    // Dump coverage SDN from the runtime and write to file
    let sdn = unsafe {
        let ptr = simple_runtime::rt_coverage_dump_sdn();
        if ptr.is_null() {
            return Err("Failed to dump coverage SDN".to_string());
        }
        let s = std::ffi::CStr::from_ptr(ptr).to_string_lossy().to_string();
        simple_runtime::rt_coverage_free_sdn(ptr);
        s
    };
    if sdn.is_empty() {
        return Ok(());
    }
    let output_dir = "build/coverage";
    std::fs::create_dir_all(output_dir).map_err(|e| format!("Failed to create {}: {}", output_dir, e))?;
    let output_path = format!("{}/coverage.sdn", output_dir);
    std::fs::write(&output_path, &sdn).map_err(|e| format!("Failed to write {}: {}", output_path, e))?;
    Ok(())
}

pub fn get_coverage_output_path() -> Option<String> {
    if is_coverage_enabled() {
        Some("build/coverage/coverage.sdn".to_string())
    } else {
        None
    }
}
