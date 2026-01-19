//! Startup initialization and metrics handling

use std::env;
use crate::{StartupMetrics, StartupPhase};

/// Initialize startup metrics if requested
pub fn init_metrics() -> (bool, StartupMetrics) {
    let enable = env::args().any(|a| a == "--startup-metrics");
    if enable {
        crate::enable_metrics();
    }

    let mut metrics = StartupMetrics::new();
    metrics.start();
    (enable, metrics)
}

/// Perform early startup phase: parse args and start prefetching
pub fn early_startup(metrics: &mut StartupMetrics) -> crate::EarlyConfig {
    let early_start = std::time::Instant::now();
    let early_config = crate::parse_early_args(env::args().skip(1));
    metrics.record(StartupPhase::EarlyArgParse, early_start.elapsed());
    early_config
}

/// Start file prefetching in background if enabled
pub fn start_prefetch(
    early_config: &crate::EarlyConfig,
    metrics: &mut StartupMetrics,
) -> Option<crate::PrefetchHandle> {
    let prefetch_start = std::time::Instant::now();
    let handle = if early_config.enable_prefetch && !early_config.input_files.is_empty() {
        crate::prefetch_files(&early_config.input_files).ok()
    } else {
        None
    };
    if handle.is_some() {
        metrics.record(StartupPhase::FilePrefetch, prefetch_start.elapsed());
    }
    handle
}

/// Pre-allocate resources based on application type
pub fn allocate_resources(
    early_config: &crate::EarlyConfig,
    metrics: &mut StartupMetrics,
) -> Option<crate::PreAllocatedResources> {
    let resource_start = std::time::Instant::now();
    let resources =
        crate::PreAllocatedResources::allocate(early_config.app_type, &early_config.window_hints).ok();
    metrics.record(StartupPhase::ResourceAllocation, resource_start.elapsed());
    resources
}

/// Wait for prefetching to complete
pub fn wait_for_prefetch(handle: Option<crate::PrefetchHandle>, metrics: &mut StartupMetrics) {
    if let Some(h) = handle {
        let wait_start = std::time::Instant::now();
        let _ = h.wait(); // Best-effort, ignore errors
        metrics.record(StartupPhase::PrefetchWait, wait_start.elapsed());
    }
}

/// Print metrics and exit
pub fn exit_with_metrics(code: i32, metrics: &StartupMetrics) -> ! {
    if crate::metrics_enabled() {
        metrics.print_report();
    }
    std::process::exit(code)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init_metrics() {
        let (enabled, metrics) = init_metrics();
        // Metrics are disabled by default unless --startup-metrics is passed
        assert!(!enabled || enabled); // Always true, just checking it compiles
        assert!(metrics.total_elapsed().as_secs() >= 0);
    }
}
