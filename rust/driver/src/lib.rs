pub mod auth_db;
pub mod bug_db;
pub mod cli;
// CLI FFI functions are in simple_runtime::value::cli_ffi
pub use simple_runtime::value::cli_ffi;
pub mod compile_options;
pub mod db_lock;
pub mod dependency_cache;
pub mod diagnostics_conversion;
pub mod doctest;
pub mod early_startup;
pub mod exec_core;
pub mod feature_db;
pub mod gpu_init;
pub mod interpreter;
pub mod jj;
pub mod jj_state;
pub mod lazy_init;
pub mod oauth_flow;
pub mod prefetch;
pub mod repl_runner_ffi;
pub mod resource_manager;
pub mod runner;
pub mod signature;
pub mod simple_test;
pub mod startup_metrics;
pub mod task_db;
pub mod test_db;
pub mod test_stats;
pub mod todo_db;
pub mod todo_parser;
pub mod unified_db;
pub mod watcher;

pub use compile_options::{CompileOptions, CompileProfiler};
pub use diagnostics_conversion::convert_parser_diagnostic;
pub use early_startup::{parse_early_args, AppType, EarlyConfig, WindowHints};
pub use gpu_init::{
    display_loading_indicator, start_gpu_init, GpuContext, GpuInitHandle, GpuInitPhase, GpuInitState, StartupEvent,
    StartupProgress, WindowConfig,
};
pub use interpreter::{run_code, run_jit, Interpreter, RunConfig, RunResult, RunningType};
pub use jj::{BuildEvent, BuildState, JJConnector, MessageFormatter, StateStore};
pub use jj_state::{BuildMetadata, BuildMode, JjStateManager, TestLevel, TestMetadata};
pub use lazy_init::{global_scheduler, DeferredTask, LazyInit, LazyScheduler};
pub use prefetch::{prefetch_file, prefetch_files, PrefetchHandle};
pub use resource_manager::{
    CliResources, GuiResources, PreAllocatedResources, ReplResources, ServiceResources, TuiResources,
};
pub use runner::Runner;
pub use simple_test::{
    discover_tests, run_all_tests, run_test_file, SimpleTestFile, SimpleTestResult, TestCategory, TestFailure,
};
pub use startup_metrics::{enable_metrics, metrics_enabled, PhaseTimer, StartupMetrics, StartupPhase};
pub use watcher::watch;

// Workaround for Wasmer probestack linker issue on stable Rust
// https://github.com/wasmerio/wasmer/issues/3857
// This provides a stub for __rust_probestack when compiler_builtins doesn't export it
#[cfg(all(feature = "wasm", not(windows)))]
#[no_mangle]
pub extern "C" fn __rust_probestack() {
    // No-op stub - wasmer's use of probestack is for stack overflow detection
    // which we don't need in the host runtime
}
