pub mod compile_options;
pub mod dependency_cache;
pub mod doctest;
pub mod early_startup;
pub mod exec_core;
pub mod gpu_init;
pub mod interpreter;
pub mod jj;
pub mod jj_state;
pub mod lazy_init;
pub mod prefetch;
pub mod repl_runner_ffi;
pub mod resource_manager;
pub mod runner;
pub mod simple_test;
pub mod startup_metrics;
pub mod watcher;

pub use compile_options::{CompileOptions, CompileProfiler};
pub use early_startup::{AppType, EarlyConfig, WindowHints, parse_early_args};
pub use gpu_init::{
    display_loading_indicator, start_gpu_init, GpuContext, GpuInitHandle, GpuInitPhase,
    GpuInitState, StartupEvent, StartupProgress, WindowConfig,
};
pub use interpreter::{run_code, run_jit, Interpreter, RunConfig, RunResult, RunningType};
pub use jj::{BuildEvent, BuildState, JJConnector, MessageFormatter, StateStore};
pub use jj_state::{BuildMetadata, BuildMode, JjStateManager, TestLevel, TestMetadata};
pub use lazy_init::{global_scheduler, DeferredTask, LazyInit, LazyScheduler};
pub use prefetch::{prefetch_file, prefetch_files, PrefetchHandle};
pub use resource_manager::{
    PreAllocatedResources, CliResources, TuiResources, GuiResources,
    ServiceResources, ReplResources,
};
pub use runner::Runner;
pub use simple_test::{
    discover_tests, run_all_tests, run_test_file, SimpleTestFile, SimpleTestResult, TestCategory,
    TestFailure,
};
pub use startup_metrics::{
    enable_metrics, metrics_enabled, PhaseTimer, StartupMetrics, StartupPhase,
};
pub use watcher::watch;
