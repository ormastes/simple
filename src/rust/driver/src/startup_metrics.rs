//! Startup timing metrics for performance analysis (#1997)
//!
//! Measures and reports startup phase durations to identify bottlenecks.

use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

/// Global flag to enable startup metrics collection
static METRICS_ENABLED: AtomicBool = AtomicBool::new(false);

/// Enable startup metrics collection
pub fn enable_metrics() {
    METRICS_ENABLED.store(true, Ordering::Relaxed);
}

/// Disable startup metrics collection
pub fn disable_metrics() {
    METRICS_ENABLED.store(false, Ordering::Relaxed);
}

/// Check if metrics are enabled
pub fn metrics_enabled() -> bool {
    METRICS_ENABLED.load(Ordering::Relaxed)
}

/// Startup phase identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StartupPhase {
    /// Early argument parsing
    EarlyArgParse,
    /// File prefetching
    FilePrefetch,
    /// Resource pre-allocation
    ResourceAllocation,
    /// GPU initialization (if GUI app)
    GpuInit,
    /// Logging initialization
    LoggingInit,
    /// Interpreter handler setup
    HandlerInit,
    /// Panic hook installation
    PanicHookInit,
    /// Signal handler setup (Ctrl-C)
    SignalHandlerInit,
    /// Execution limit initialization
    ExecutionLimitInit,
    /// Database cleanup (stale temp files)
    DbCleanup,
    /// Main argument parsing
    MainArgParse,
    /// Sandbox application
    SandboxSetup,
    /// Prefetch wait
    PrefetchWait,
    /// File execution
    FileExecution,
    /// Total startup time
    Total,
}

impl StartupPhase {
    /// Get human-readable name
    pub fn name(&self) -> &'static str {
        match self {
            Self::EarlyArgParse => "Early Argument Parsing",
            Self::FilePrefetch => "File Prefetching",
            Self::ResourceAllocation => "Resource Pre-Allocation",
            Self::GpuInit => "GPU Initialization",
            Self::LoggingInit => "Logging Init",
            Self::HandlerInit => "Handler Setup",
            Self::PanicHookInit => "Panic Hook Init",
            Self::SignalHandlerInit => "Signal Handler Init",
            Self::ExecutionLimitInit => "Execution Limit Init",
            Self::DbCleanup => "Database Cleanup",
            Self::MainArgParse => "Main Argument Parsing",
            Self::SandboxSetup => "Sandbox Setup",
            Self::PrefetchWait => "Prefetch Wait",
            Self::FileExecution => "File Execution",
            Self::Total => "Total Startup",
        }
    }
}

/// Timing measurement for a single phase
#[derive(Debug, Clone)]
pub struct PhaseTiming {
    pub phase: StartupPhase,
    pub duration: Duration,
    pub start_time: Instant,
}

/// Collection of startup timing measurements
#[derive(Debug, Default)]
pub struct StartupMetrics {
    timings: Vec<PhaseTiming>,
    start_time: Option<Instant>,
}

impl StartupMetrics {
    /// Create a new metrics collector
    pub fn new() -> Self {
        Self {
            timings: Vec::with_capacity(16),
            start_time: None,
        }
    }

    /// Start overall timing
    pub fn start(&mut self) {
        if metrics_enabled() {
            self.start_time = Some(Instant::now());
        }
    }

    /// Record a phase timing
    pub fn record(&mut self, phase: StartupPhase, duration: Duration) {
        if metrics_enabled() {
            self.timings.push(PhaseTiming {
                phase,
                duration,
                start_time: self.start_time.unwrap_or_else(Instant::now),
            });
        }
    }

    /// Get total startup time
    pub fn total_time(&self) -> Option<Duration> {
        self.start_time.map(|start| start.elapsed())
    }

    /// Get timing for a specific phase
    pub fn get_phase(&self, phase: StartupPhase) -> Option<Duration> {
        self.timings.iter().find(|t| t.phase == phase).map(|t| t.duration)
    }

    /// Get all timings
    pub fn timings(&self) -> &[PhaseTiming] {
        &self.timings
    }

    /// Print metrics report to stderr
    pub fn print_report(&self) {
        if !metrics_enabled() {
            return;
        }

        eprintln!("\n=== Startup Metrics ===");

        if let Some(total) = self.total_time() {
            eprintln!("Total: {:?}", total);
        }

        eprintln!("\nPhase Breakdown:");
        for timing in &self.timings {
            eprintln!(
                "  {:25} {:>10.2}ms",
                timing.phase.name(),
                timing.duration.as_secs_f64() * 1000.0
            );
        }

        if let Some(total) = self.total_time() {
            let sum: Duration = self.timings.iter().map(|t| t.duration).sum();
            let overhead = total.saturating_sub(sum);
            eprintln!("  {:25} {:>10.2}ms", "Overhead", overhead.as_secs_f64() * 1000.0);
        }

        eprintln!("======================\n");
    }

    /// Format metrics as JSON string
    pub fn to_json(&self) -> String {
        let mut parts = Vec::new();

        for timing in &self.timings {
            parts.push(format!(
                r#"{{"phase":"{}","duration_ms":{:.2}}}"#,
                timing.phase.name(),
                timing.duration.as_secs_f64() * 1000.0
            ));
        }

        if let Some(total) = self.total_time() {
            parts.push(format!(
                r#"{{"phase":"Total","duration_ms":{:.2}}}"#,
                total.as_secs_f64() * 1000.0
            ));
        }

        format!("[{}]", parts.join(","))
    }
}

/// RAII timer for automatic phase timing
pub struct PhaseTimer<'a> {
    metrics: &'a mut StartupMetrics,
    phase: StartupPhase,
    start: Instant,
    enabled: bool,
}

impl<'a> PhaseTimer<'a> {
    /// Create a new phase timer
    pub fn new(metrics: &'a mut StartupMetrics, phase: StartupPhase) -> Self {
        Self {
            metrics,
            phase,
            start: Instant::now(),
            enabled: metrics_enabled(),
        }
    }
}

impl<'a> Drop for PhaseTimer<'a> {
    fn drop(&mut self) {
        if self.enabled {
            let duration = self.start.elapsed();
            self.metrics.record(self.phase, duration);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    #[test]
    fn test_metrics_disabled_by_default() {
        // Reset state to isolate from other tests
        disable_metrics();
        assert!(!metrics_enabled());
    }

    #[test]
    fn test_enable_metrics() {
        enable_metrics();
        assert!(metrics_enabled());
    }

    #[test]
    fn test_startup_metrics_basic() {
        enable_metrics();
        let mut metrics = StartupMetrics::new();
        metrics.start();

        metrics.record(StartupPhase::EarlyArgParse, Duration::from_millis(10));
        metrics.record(StartupPhase::FilePrefetch, Duration::from_millis(50));

        assert_eq!(metrics.timings().len(), 2);
        assert_eq!(
            metrics.get_phase(StartupPhase::EarlyArgParse),
            Some(Duration::from_millis(10))
        );
        assert_eq!(
            metrics.get_phase(StartupPhase::FilePrefetch),
            Some(Duration::from_millis(50))
        );
    }

    #[test]
    fn test_phase_timer() {
        enable_metrics();
        let mut metrics = StartupMetrics::new();
        metrics.start();

        {
            let _timer = PhaseTimer::new(&mut metrics, StartupPhase::LoggingInit);
            thread::sleep(Duration::from_millis(10));
        }

        let duration = metrics.get_phase(StartupPhase::LoggingInit).unwrap();
        assert!(duration >= Duration::from_millis(10));
        assert!(duration < Duration::from_millis(20));
    }

    #[test]
    fn test_total_time() {
        enable_metrics();
        let mut metrics = StartupMetrics::new();
        metrics.start();

        thread::sleep(Duration::from_millis(10));

        let total = metrics.total_time().unwrap();
        assert!(total >= Duration::from_millis(10));
    }

    #[test]
    fn test_json_format() {
        enable_metrics();
        let mut metrics = StartupMetrics::new();
        metrics.start();

        metrics.record(StartupPhase::EarlyArgParse, Duration::from_millis(10));
        metrics.record(StartupPhase::FilePrefetch, Duration::from_millis(50));

        let json = metrics.to_json();
        assert!(json.contains("Early Argument Parsing"));
        assert!(json.contains("File Prefetching"));
        assert!(json.contains("duration_ms"));
    }

    #[test]
    fn test_phase_names() {
        assert_eq!(StartupPhase::EarlyArgParse.name(), "Early Argument Parsing");
        assert_eq!(StartupPhase::FilePrefetch.name(), "File Prefetching");
        assert_eq!(StartupPhase::GpuInit.name(), "GPU Initialization");
    }

    #[test]
    fn test_print_report() {
        enable_metrics();
        let mut metrics = StartupMetrics::new();
        metrics.start();

        metrics.record(StartupPhase::EarlyArgParse, Duration::from_millis(10));

        // Just ensure it doesn't panic
        metrics.print_report();
    }
}
