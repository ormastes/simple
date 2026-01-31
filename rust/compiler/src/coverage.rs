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
    _data: Vec<(String, u64)>,
}

impl CoverageCollector {
    pub fn new() -> Self {
        Self { _data: Vec::new() }
    }
    pub fn to_sdn(&self) -> String {
        String::new()
    }
    pub fn record_line(&mut self, _file: impl AsRef<std::path::Path>, _line: usize) {}
    pub fn record_function_call(&mut self, _name: &str) {}
    pub fn clear(&mut self) {
        self._data.clear();
    }
    pub fn stats(&self) -> CoverageStats {
        CoverageStats::default()
    }
    pub fn was_function_called(&self, _name: &str) -> bool {
        false
    }
    pub fn executed_files(&self) -> Vec<String> {
        Vec::new()
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

pub fn is_coverage_enabled() -> bool {
    GLOBAL_COVERAGE.get().is_some()
}

pub fn save_global_coverage() -> Result<(), String> {
    Ok(())
}

pub fn get_coverage_output_path() -> Option<String> {
    None
}
