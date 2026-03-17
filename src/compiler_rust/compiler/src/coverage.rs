// Coverage module stub - provides API surface for compilation
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
    lines: std::collections::HashMap<String, std::collections::HashSet<usize>>,
    function_calls: std::collections::HashMap<String, u64>,
}

impl Default for CoverageCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl CoverageCollector {
    pub fn new() -> Self {
        Self {
            lines: std::collections::HashMap::new(),
            function_calls: std::collections::HashMap::new(),
        }
    }
    pub fn to_sdn(&self) -> String {
        // Delegate to runtime's real coverage data
        let sdn = unsafe {
            let ptr = simple_runtime::rt_coverage_dump_sdn();
            if ptr.is_null() {
                return String::new();
            }
            let s = std::ffi::CStr::from_ptr(ptr).to_string_lossy().to_string();
            simple_runtime::rt_coverage_free_sdn(ptr);
            s
        };
        sdn
    }
    pub fn record_line(&mut self, file: impl AsRef<std::path::Path>, line: usize) {
        let path = file.as_ref().display().to_string();
        self.lines.entry(path).or_default().insert(line);
    }
    pub fn record_function_call(&mut self, name: &str) {
        *self.function_calls.entry(name.to_string()).or_insert(0) += 1;
    }
    pub fn clear(&mut self) {
        self.lines.clear();
        self.function_calls.clear();
    }
    pub fn stats(&self) -> CoverageStats {
        let total_lines: u64 = self.lines.values().map(|s| s.len() as u64).sum();
        let total_functions = self.function_calls.len() as u64;
        let functions_hit = self.function_calls.values().filter(|&&c| c > 0).count() as u64;
        CoverageStats {
            total_lines,
            lines_hit: total_lines, // all recorded lines are covered
            lines_total: total_lines,
            total_functions,
            functions_hit,
            functions_total: total_functions,
            ..CoverageStats::default()
        }
    }
    pub fn was_function_called(&self, name: &str) -> bool {
        self.function_calls.get(name).map_or(false, |&c| c > 0)
    }
    pub fn executed_files(&self) -> Vec<String> {
        self.lines.keys().cloned().collect()
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
