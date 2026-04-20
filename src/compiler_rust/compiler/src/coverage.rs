// Coverage collection for interpreted and compiled Simple execution.
//
// The interpreter records line/function data in this collector. Runtime
// decision/condition probes live in simple_runtime and are merged when saving.
// Keep the output SDN-shaped so the existing dashboard and stats tools can read
// it without a separate adapter.
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
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
    pub total_files: u64,
    pub branches_hit: u64,
    pub branches_total: u64,
    pub functions_hit: u64,
    pub functions_total: u64,
    pub total_functions: u64,
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
    line_hits: BTreeMap<String, BTreeSet<usize>>,
    function_calls: BTreeMap<String, u64>,
    ffi_calls: BTreeMap<String, u64>,
    label: Option<String>,
}

impl Default for CoverageCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl CoverageCollector {
    pub fn new() -> Self {
        Self {
            line_hits: BTreeMap::new(),
            function_calls: BTreeMap::new(),
            ffi_calls: BTreeMap::new(),
            label: None,
        }
    }

    pub fn new_for_test(label: String) -> Self {
        Self {
            label: Some(label),
            ..Self::new()
        }
    }

    pub fn to_sdn(&self) -> String {
        let mut out = String::new();
        out.push_str("# Coverage Report\n");
        out.push_str("version: 1.0\n\n");

        if let Some(label) = &self.label {
            out.push_str(&format!("label: {}\n\n", label));
        }

        out.push_str("lines |file, line, hit_count|\n");
        for (file, lines) in &self.line_hits {
            for line in lines {
                out.push_str(&format!("    {}, {}, 1\n", file, line));
            }
        }
        out.push('\n');

        out.push_str("functions |name, call_count|\n");
        for (name, count) in &self.function_calls {
            out.push_str(&format!("    {}, {}\n", name, count));
        }
        out.push('\n');

        if !self.ffi_calls.is_empty() {
            out.push_str("ffi_calls |name, call_count|\n");
            for (name, count) in &self.ffi_calls {
                out.push_str(&format!("    {}, {}\n", name, count));
            }
            out.push('\n');
        }

        let stats = self.stats();
        out.push_str("summary:\n");
        out.push_str(&format!("    total_files: {}\n", stats.total_files));
        out.push_str(&format!("    total_lines: {}\n", stats.total_lines));
        out.push_str(&format!("    covered_lines: {}\n", stats.lines_hit));
        out.push_str(&format!("    total_functions: {}\n", stats.total_functions));
        out.push_str(&format!("    covered_functions: {}\n", stats.functions_hit));
        out.push_str(&format!("    total_ffi_calls: {}\n", stats.total_ffi_calls));
        out
    }

    pub fn record_line(&mut self, file: impl AsRef<Path>, line: usize) {
        let file = file.as_ref().to_string_lossy().to_string();
        self.line_hits.entry(file).or_default().insert(line);
    }

    pub fn record_function_call(&mut self, name: &str) {
        *self.function_calls.entry(name.to_string()).or_insert(0) += 1;
    }

    pub fn record_ffi_call(&mut self, name: &str) {
        *self.ffi_calls.entry(name.to_string()).or_insert(0) += 1;
    }

    pub fn clear(&mut self) {
        self.line_hits.clear();
        self.function_calls.clear();
        self.ffi_calls.clear();
    }

    pub fn stats(&self) -> CoverageStats {
        let total_lines = self.line_hits.values().map(|lines| lines.len() as u64).sum();
        let total_functions = self.function_calls.len() as u64;
        CoverageStats {
            lines_hit: total_lines,
            lines_total: total_lines,
            total_lines,
            total_files: self.line_hits.len() as u64,
            branches_hit: 0,
            branches_total: 0,
            functions_hit: total_functions,
            functions_total: total_functions,
            total_functions,
            total_ffi_calls: self.ffi_calls.len() as u64,
        }
    }

    pub fn has_data(&self) -> bool {
        !self.line_hits.is_empty() || !self.function_calls.is_empty() || !self.ffi_calls.is_empty()
    }

    pub fn function_call_count(&self, name: &str) -> u64 {
        self.function_calls.get(name).copied().unwrap_or(0)
    }

    pub fn ffi_call_count(&self, name: &str) -> u64 {
        self.ffi_calls.get(name).copied().unwrap_or(0)
    }

    pub fn merge(&mut self, other: &CoverageCollector) {
        for (file, lines) in &other.line_hits {
            self.line_hits
                .entry(file.clone())
                .or_default()
                .extend(lines.iter().copied());
        }
        for (name, count) in &other.function_calls {
            *self.function_calls.entry(name.clone()).or_insert(0) += count;
        }
        for (name, count) in &other.ffi_calls {
            *self.ffi_calls.entry(name.clone()).or_insert(0) += count;
        }
    }

    pub fn lines_for_file(&self, file: impl AsRef<Path>) -> Option<&BTreeSet<usize>> {
        let file = file.as_ref().to_string_lossy().to_string();
        self.line_hits.get(&file)
    }

    pub fn is_line_executed(&self, file: impl AsRef<Path>, line: usize) -> bool {
        self.lines_for_file(file)
            .map(|lines| lines.contains(&line))
            .unwrap_or(false)
    }

    pub fn was_file_executed(&self, file: impl AsRef<Path>) -> bool {
        let file = file.as_ref().to_string_lossy().to_string();
        self.line_hits.contains_key(&file)
    }

    pub fn executed_files(&self) -> Vec<String> {
        self.line_hits.keys().cloned().collect()
    }

    pub fn called_functions(&self) -> Vec<String> {
        self.function_calls.keys().cloned().collect()
    }

    pub fn file_coverage_percentage(&self, file: impl AsRef<Path>, total_lines: u64) -> f64 {
        if total_lines == 0 {
            return 100.0;
        }
        let hit = self
            .lines_for_file(file)
            .map(|lines| lines.len() as f64)
            .unwrap_or(0.0);
        (hit / total_lines as f64) * 100.0
    }

    pub fn validate_minimum_coverage(&self, min_lines: u64, min_functions: u64) -> Result<(), String> {
        let stats = self.stats();
        if stats.total_lines < min_lines {
            return Err(format!(
                "Insufficient line coverage: {} < {}",
                stats.total_lines, min_lines
            ));
        }
        if stats.total_functions < min_functions {
            return Err(format!(
                "Insufficient function coverage: {} < {}",
                stats.total_functions, min_functions
            ));
        }
        Ok(())
    }

    pub fn was_function_called(&self, name: &str) -> bool {
        self.function_call_count(name) > 0
    }

    pub fn summary_report(&self) -> String {
        let mut out = String::from("=== Coverage Summary ===\n");
        out.push_str("Functions called:\n");
        for (name, count) in &self.function_calls {
            out.push_str(&format!("  {}: {}\n", name, count));
        }
        out.push_str("FFI calls:\n");
        for (name, count) in &self.ffi_calls {
            out.push_str(&format!("  {}: {}\n", name, count));
        }
        out
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
    let mut sdn = String::new();
    if let Some(cov) = get_global_coverage() {
        let guard = cov
            .lock()
            .map_err(|_| "coverage collector lock poisoned".to_string())?;
        sdn.push_str(&guard.to_sdn());
    }

    let runtime_sdn = dump_runtime_coverage_sdn();
    if !runtime_sdn.trim().is_empty() {
        if !sdn.ends_with('\n') {
            sdn.push('\n');
        }
        sdn.push_str("\n# Runtime decision/condition coverage\n");
        sdn.push_str(&runtime_sdn);
    }

    if sdn.trim().is_empty() {
        sdn = "# Coverage Report\nversion: 1.0\n\nsummary:\n    total_files: 0\n    total_lines: 0\n    covered_lines: 0\n    total_functions: 0\n    covered_functions: 0\n".to_string();
    }

    let primary = coverage_output_path_buf();
    write_coverage_file(&primary, &sdn)?;

    // Compatibility mirrors: older docs point at .coverage, while repo stats
    // aggregation reads build/coverage.
    let build_path = PathBuf::from("build/coverage/coverage.sdn");
    if primary != build_path {
        write_coverage_file(&build_path, &sdn)?;
    }
    let dot_path = PathBuf::from(".coverage/coverage.sdn");
    if primary != dot_path {
        write_coverage_file(&dot_path, &sdn)?;
    }

    Ok(())
}

pub fn get_coverage_output_path() -> Option<String> {
    Some(coverage_output_path_buf().to_string_lossy().to_string())
}

fn coverage_output_path_buf() -> PathBuf {
    std::env::var("SIMPLE_COVERAGE_OUTPUT")
        .ok()
        .filter(|s| !s.trim().is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("build/coverage/coverage.sdn"))
}

fn write_coverage_file(path: &Path, content: &str) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|e| format!("failed to create {}: {}", parent.display(), e))?;
    }
    std::fs::write(path, content).map_err(|e| format!("failed to write {}: {}", path.display(), e))
}

fn dump_runtime_coverage_sdn() -> String {
    unsafe {
        let ptr = simple_runtime::rt_coverage_dump_sdn();
        if ptr.is_null() {
            return String::new();
        }
        let sdn = std::ffi::CStr::from_ptr(ptr)
            .to_string_lossy()
            .into_owned();
        simple_runtime::rt_coverage_free_sdn(ptr);
        sdn
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn collector_records_lines_functions_and_ffi_calls() {
        let mut cov = CoverageCollector::new();
        cov.record_line(Path::new("test.spl"), 10);
        cov.record_line(Path::new("test.spl"), 10);
        cov.record_function_call("main");
        cov.record_function_call("main");
        cov.record_ffi_call("rt_print");

        assert!(cov.has_data());
        assert_eq!(cov.stats().total_lines, 1);
        assert_eq!(cov.stats().total_files, 1);
        assert_eq!(cov.function_call_count("main"), 2);
        assert_eq!(cov.ffi_call_count("rt_print"), 1);
        assert!(cov.was_line_executed_compat("test.spl", 10));
    }

    #[test]
    fn collector_renders_sdn() {
        let mut cov = CoverageCollector::new_for_test("unit".to_string());
        cov.record_line(Path::new("a.spl"), 1);
        cov.record_function_call("main");
        let sdn = cov.to_sdn();
        assert!(sdn.contains("# Coverage Report"));
        assert!(sdn.contains("lines |file, line, hit_count|"));
        assert!(sdn.contains("functions |name, call_count|"));
        assert!(sdn.contains("main, 1"));
    }

    #[test]
    fn collector_merges_counts() {
        let mut a = CoverageCollector::new();
        a.record_line(Path::new("a.spl"), 1);
        a.record_function_call("main");
        let mut b = CoverageCollector::new();
        b.record_line(Path::new("a.spl"), 2);
        b.record_function_call("main");
        b.record_ffi_call("rt_print");

        a.merge(&b);
        assert_eq!(a.stats().total_lines, 2);
        assert_eq!(a.function_call_count("main"), 2);
        assert_eq!(a.ffi_call_count("rt_print"), 1);
    }
}

#[cfg(test)]
impl CoverageCollector {
    fn was_line_executed_compat(&self, file: &str, line: usize) -> bool {
        self.is_line_executed(Path::new(file), line)
    }
}
