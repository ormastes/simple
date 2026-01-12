//! Compile Options (#824)
//!
//! Configuration for compilation including parallelization, profiling, and coverage.

use simple_common::file_reader::ReadStrategy;
use std::num::NonZeroUsize;
use std::path::PathBuf;

/// Compilation options for build optimization.
#[derive(Debug, Clone)]
pub struct CompileOptions {
    /// Number of threads for parallel compilation.
    /// None means use all available cores.
    pub parallel_threads: Option<NonZeroUsize>,

    /// Whether parallel compilation is enabled.
    pub parallel: bool,

    /// Whether to show profiling information.
    pub profile: bool,

    /// File reading strategy.
    pub read_strategy: ReadStrategy,

    /// Enable verbose output.
    pub verbose: bool,

    /// Enable coverage instrumentation.
    pub coverage: bool,

    /// Output path for coverage report (default: coverage.sdn).
    pub coverage_output: Option<PathBuf>,

    /// Emit AST as JSON to file or stdout.
    pub emit_ast: Option<Option<PathBuf>>,

    /// Emit HIR as JSON to file or stdout.
    pub emit_hir: Option<Option<PathBuf>>,

    /// Emit MIR as JSON to file or stdout.
    pub emit_mir: Option<Option<PathBuf>>,

    /// Enable deterministic build mode (reproducible binaries).
    pub deterministic: bool,

    /// Override build timestamp for deterministic builds (ISO 8601 format).
    pub build_timestamp: Option<String>,

    /// Build log output path for replay and debugging.
    pub log_path: Option<PathBuf>,

    /// Allow deprecated syntax without warnings (e.g., [] for generics).
    pub allow_deprecated: bool,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            parallel_threads: None,
            parallel: false,
            profile: false,
            read_strategy: ReadStrategy::Auto,
            verbose: false,
            coverage: false,
            coverage_output: None,
            emit_ast: None,
            emit_hir: None,
            emit_mir: None,
            deterministic: false,
            build_timestamp: None,
            log_path: None,
            allow_deprecated: false,
        }
    }
}

impl CompileOptions {
    /// Create new compile options with defaults.
    pub fn new() -> Self {
        Self::default()
    }

    /// Enable parallel compilation with all available cores.
    pub fn with_parallel(mut self) -> Self {
        self.parallel = true;
        self
    }

    /// Set the number of parallel threads.
    pub fn with_threads(mut self, threads: usize) -> Self {
        self.parallel = true;
        self.parallel_threads = NonZeroUsize::new(threads);
        self
    }

    /// Enable profiling output.
    pub fn with_profile(mut self) -> Self {
        self.profile = true;
        self
    }

    /// Force memory-mapped file reading.
    pub fn with_mmap(mut self) -> Self {
        self.read_strategy = ReadStrategy::Mmap;
        self
    }

    /// Disable memory-mapped file reading.
    pub fn without_mmap(mut self) -> Self {
        self.read_strategy = ReadStrategy::Regular;
        self
    }

    /// Enable verbose output.
    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Enable coverage instrumentation.
    pub fn with_coverage(mut self) -> Self {
        self.coverage = true;
        self
    }

    /// Set the coverage output path.
    pub fn with_coverage_output(mut self, path: PathBuf) -> Self {
        self.coverage = true;
        self.coverage_output = Some(path);
        self
    }

    /// Get the coverage output path (default: coverage.sdn).
    pub fn coverage_output_path(&self) -> PathBuf {
        self.coverage_output
            .clone()
            .unwrap_or_else(|| PathBuf::from("coverage.sdn"))
    }

    /// Enable AST emission to stdout.
    pub fn with_emit_ast(mut self) -> Self {
        self.emit_ast = Some(None);
        self
    }

    /// Enable AST emission to file.
    pub fn with_emit_ast_to(mut self, path: PathBuf) -> Self {
        self.emit_ast = Some(Some(path));
        self
    }

    /// Enable HIR emission to stdout.
    pub fn with_emit_hir(mut self) -> Self {
        self.emit_hir = Some(None);
        self
    }

    /// Enable HIR emission to file.
    pub fn with_emit_hir_to(mut self, path: PathBuf) -> Self {
        self.emit_hir = Some(Some(path));
        self
    }

    /// Enable MIR emission to stdout.
    pub fn with_emit_mir(mut self) -> Self {
        self.emit_mir = Some(None);
        self
    }

    /// Enable MIR emission to file.
    pub fn with_emit_mir_to(mut self, path: PathBuf) -> Self {
        self.emit_mir = Some(Some(path));
        self
    }

    /// Enable deterministic build mode.
    pub fn with_deterministic(mut self) -> Self {
        self.deterministic = true;
        self
    }

    /// Set the build timestamp for deterministic builds.
    pub fn with_build_timestamp(mut self, timestamp: String) -> Self {
        self.deterministic = true;
        self.build_timestamp = Some(timestamp);
        self
    }

    /// Set the build log output path.
    pub fn with_log(mut self, path: PathBuf) -> Self {
        self.log_path = Some(path);
        self
    }

    /// Allow deprecated syntax without warnings.
    pub fn with_allow_deprecated(mut self) -> Self {
        self.allow_deprecated = true;
        self
    }

    /// Get the number of threads to use for parallel compilation.
    /// Returns the configured number or all available cores.
    pub fn thread_count(&self) -> usize {
        self.parallel_threads.map(|n| n.get()).unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1)
        })
    }

    /// Parse compile options from CLI arguments.
    pub fn from_args(args: &[String]) -> Self {
        let mut opts = Self::default();

        for arg in args {
            if arg == "--parallel" {
                opts.parallel = true;
            } else if arg.starts_with("--parallel=") {
                opts.parallel = true;
                if let Some(n) = arg.strip_prefix("--parallel=") {
                    if let Ok(threads) = n.parse::<usize>() {
                        opts.parallel_threads = NonZeroUsize::new(threads);
                    }
                }
            } else if arg == "--profile" {
                opts.profile = true;
            } else if arg == "--mmap" {
                opts.read_strategy = ReadStrategy::Mmap;
            } else if arg == "--no-mmap" {
                opts.read_strategy = ReadStrategy::Regular;
            } else if arg == "--verbose" || arg == "-v" {
                opts.verbose = true;
            } else if arg == "--coverage" {
                opts.coverage = true;
            } else if arg.starts_with("--coverage-output=") {
                opts.coverage = true;
                if let Some(path) = arg.strip_prefix("--coverage-output=") {
                    opts.coverage_output = Some(PathBuf::from(path));
                }
            } else if arg == "--emit-ast" {
                opts.emit_ast = Some(None);
            } else if arg.starts_with("--emit-ast=") {
                if let Some(path) = arg.strip_prefix("--emit-ast=") {
                    opts.emit_ast = Some(Some(PathBuf::from(path)));
                }
            } else if arg == "--emit-hir" {
                opts.emit_hir = Some(None);
            } else if arg.starts_with("--emit-hir=") {
                if let Some(path) = arg.strip_prefix("--emit-hir=") {
                    opts.emit_hir = Some(Some(PathBuf::from(path)));
                }
            } else if arg == "--emit-mir" {
                opts.emit_mir = Some(None);
            } else if arg.starts_with("--emit-mir=") {
                if let Some(path) = arg.strip_prefix("--emit-mir=") {
                    opts.emit_mir = Some(Some(PathBuf::from(path)));
                }
            } else if arg == "--deterministic" {
                opts.deterministic = true;
            } else if arg.starts_with("--build-timestamp=") {
                opts.deterministic = true;
                if let Some(ts) = arg.strip_prefix("--build-timestamp=") {
                    opts.build_timestamp = Some(ts.to_string());
                }
            } else if arg.starts_with("--log=") {
                if let Some(path) = arg.strip_prefix("--log=") {
                    opts.log_path = Some(PathBuf::from(path));
                }
            } else if arg == "--allow-deprecated" {
                opts.allow_deprecated = true;
            }
        }

        opts
    }
}

/// Compilation profiler for measuring phase timings.
#[derive(Debug, Default)]
pub struct CompileProfiler {
    phases: Vec<(String, std::time::Duration)>,
    current_phase: Option<(String, std::time::Instant)>,
}

impl CompileProfiler {
    /// Create a new profiler.
    pub fn new() -> Self {
        Self::default()
    }

    /// Start timing a phase.
    pub fn start_phase(&mut self, name: &str) {
        self.end_current_phase();
        self.current_phase = Some((name.to_string(), std::time::Instant::now()));
    }

    /// End the current phase.
    pub fn end_current_phase(&mut self) {
        if let Some((name, start)) = self.current_phase.take() {
            self.phases.push((name, start.elapsed()));
        }
    }

    /// End profiling and return total duration.
    pub fn finish(&mut self) -> std::time::Duration {
        self.end_current_phase();
        self.phases.iter().map(|(_, d)| *d).sum()
    }

    /// Print profiling results to stderr.
    pub fn print_results(&self) {
        if self.phases.is_empty() {
            return;
        }

        let total: std::time::Duration = self.phases.iter().map(|(_, d)| *d).sum();

        eprintln!();
        eprintln!("Compilation Profile:");
        eprintln!("─────────────────────────────────────────────");

        for (name, duration) in &self.phases {
            let percent = (duration.as_secs_f64() / total.as_secs_f64()) * 100.0;
            eprintln!(
                "  {:<20} {:>8.2}ms ({:>5.1}%)",
                name,
                duration.as_secs_f64() * 1000.0,
                percent
            );
        }

        eprintln!("─────────────────────────────────────────────");
        eprintln!("  {:<20} {:>8.2}ms", "Total", total.as_secs_f64() * 1000.0);
        eprintln!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_options() {
        let opts = CompileOptions::default();
        assert!(!opts.parallel);
        assert!(!opts.profile);
        assert_eq!(opts.read_strategy, ReadStrategy::Auto);
    }

    #[test]
    fn test_parse_parallel() {
        let args = vec!["--parallel".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert!(opts.parallel);
        assert!(opts.parallel_threads.is_none());
    }

    #[test]
    fn test_parse_parallel_with_threads() {
        let args = vec!["--parallel=4".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert!(opts.parallel);
        assert_eq!(opts.parallel_threads.map(|n| n.get()), Some(4));
    }

    #[test]
    fn test_parse_profile() {
        let args = vec!["--profile".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert!(opts.profile);
    }

    #[test]
    fn test_parse_mmap() {
        let args = vec!["--mmap".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert_eq!(opts.read_strategy, ReadStrategy::Mmap);

        let args = vec!["--no-mmap".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert_eq!(opts.read_strategy, ReadStrategy::Regular);
    }

    #[test]
    fn test_profiler() {
        let mut profiler = CompileProfiler::new();

        profiler.start_phase("parse");
        std::thread::sleep(std::time::Duration::from_millis(10));

        profiler.start_phase("compile");
        std::thread::sleep(std::time::Duration::from_millis(10));

        let total = profiler.finish();
        assert!(total >= std::time::Duration::from_millis(20));
    }

    #[test]
    fn test_default_no_coverage() {
        let opts = CompileOptions::default();
        assert!(!opts.coverage);
        assert!(opts.coverage_output.is_none());
    }

    #[test]
    fn test_parse_coverage() {
        let args = vec!["--coverage".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert!(opts.coverage);
        assert!(opts.coverage_output.is_none());
    }

    #[test]
    fn test_parse_coverage_with_output() {
        let args = vec!["--coverage-output=my_report.sdn".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert!(opts.coverage);
        assert_eq!(opts.coverage_output, Some(PathBuf::from("my_report.sdn")));
    }

    #[test]
    fn test_coverage_output_path_default() {
        let opts = CompileOptions::default().with_coverage();
        assert_eq!(opts.coverage_output_path(), PathBuf::from("coverage.sdn"));
    }

    #[test]
    fn test_coverage_output_path_custom() {
        let opts = CompileOptions::default().with_coverage_output(PathBuf::from("custom.sdn"));
        assert_eq!(opts.coverage_output_path(), PathBuf::from("custom.sdn"));
    }

    #[test]
    fn test_with_coverage() {
        let opts = CompileOptions::new().with_coverage();
        assert!(opts.coverage);
    }

    #[test]
    fn test_emit_ast_stdout() {
        let args = vec!["--emit-ast".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert!(opts.emit_ast.is_some());
        assert!(opts.emit_ast.as_ref().unwrap().is_none());
    }

    #[test]
    fn test_emit_ast_file() {
        let args = vec!["--emit-ast=out.json".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert_eq!(opts.emit_ast, Some(Some(PathBuf::from("out.json"))));
    }

    #[test]
    fn test_emit_hir() {
        let args = vec!["--emit-hir".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert!(opts.emit_hir.is_some());
    }

    #[test]
    fn test_emit_mir() {
        let args = vec!["--emit-mir=mir.json".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert_eq!(opts.emit_mir, Some(Some(PathBuf::from("mir.json"))));
    }

    #[test]
    fn test_deterministic_flag() {
        let args = vec!["--deterministic".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert!(opts.deterministic);
        assert!(opts.build_timestamp.is_none());
    }

    #[test]
    fn test_build_timestamp() {
        let args = vec!["--build-timestamp=2025-01-15T10:00:00Z".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert!(opts.deterministic);
        assert_eq!(
            opts.build_timestamp,
            Some("2025-01-15T10:00:00Z".to_string())
        );
    }

    #[test]
    fn test_with_deterministic() {
        let opts = CompileOptions::new().with_deterministic();
        assert!(opts.deterministic);
    }

    #[test]
    fn test_with_build_timestamp() {
        let opts = CompileOptions::new().with_build_timestamp("2025-01-15T10:00:00Z".to_string());
        assert!(opts.deterministic);
        assert_eq!(
            opts.build_timestamp,
            Some("2025-01-15T10:00:00Z".to_string())
        );
    }

    #[test]
    fn test_log_path_flag() {
        let args = vec!["--log=build.json".to_string()];
        let opts = CompileOptions::from_args(&args);
        assert_eq!(opts.log_path, Some(PathBuf::from("build.json")));
    }

    #[test]
    fn test_with_log() {
        let opts = CompileOptions::new().with_log(PathBuf::from("test.json"));
        assert_eq!(opts.log_path, Some(PathBuf::from("test.json")));
    }
}
