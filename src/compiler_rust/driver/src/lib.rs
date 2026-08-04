pub mod auth_db;
pub mod bug_db;
pub mod cli;
// CLI SFFI functions are in simple_runtime::value::cli_sffi
pub use simple_runtime::value::cli_sffi;
pub mod compile_options;
pub mod db_lock;
pub mod dependency_cache;
pub mod doctest;
pub mod early_startup;
pub mod exec_core;
pub mod feature_db;
pub mod gpu_init;
pub mod interpreter;
pub mod jj;
pub mod jj_state;
pub mod lazy_init;
pub mod log;
#[cfg(feature = "oauth")]
pub mod oauth_flow;
pub mod prefetch;
pub mod repl_runner_sffi;
pub mod resource_manager;
pub mod runner;
pub mod seed_warning;
pub mod signature;
pub mod simple_test;
pub mod startup_metrics;
pub mod string_interner;
pub mod task_db;
pub mod test_db;
pub mod test_stats;
pub mod todo_db;
pub mod todo_parser;
pub mod unified_db;
pub mod watcher;

pub use compile_options::{CompileOptions, CompileProfiler, SimdMode};
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

// `__rust_probestack` for the `wasm` feature (wasmerio/wasmer#3857).
//
// `wasmer-vm` declares `extern "C" { fn __rust_probestack(); }` and publishes it
// as `LibCall::Probestack`, the routine cranelift-compiled *guest* code calls
// when a wasm function's frame is larger than a page. Rust used to export that
// symbol unmangled from `compiler_builtins`; since ~1.79 it is emitted into the
// mangled `__rustc` namespace instead (`_RNv...___rustc17___rust_probestack`), so
// linking wasmer against a modern stable toolchain fails with
// `rust-lld: error: undefined symbol: __rust_probestack`.
//
// Two earlier workarounds were removed in favour of this one:
//
//   * an explicit `compiler_builtins = "0.1"` dependency on the `wasm` feature.
//     That crate is nightly-only (`#![feature(repr_simd)]`), so it did not make
//     the feature link -- it made the feature impossible to compile at all on the
//     stable toolchain this project pins. That is how the WASI capability
//     enforcement sitting behind this feature was able to rot unobserved.
//
//   * a no-op `pub extern "C" fn __rust_probestack() {}` stub. That one did link,
//     which is worse: a probestack exists precisely so that a frame bigger than
//     the guard page cannot leap over it. Stubbing it out silently converts guest
//     stack overflow from a trap into memory corruption -- the Stack Clash class
//     of bug that wasmer's own `probestack.rs` header warns about. A sandbox
//     runtime is the last place to disable it.
//
// So the symbol is provided for real. The body is the ELF x86_64 routine from
// `compiler_builtins`: frame size arrives in `%rax`, every page between `%rsp+8`
// and `%rsp+8-%rax` is touched so an unmapped page faults, and neither `%rsp` nor
// `%rax` is modified on return.
//
// Deliberately x86_64-only. `wasmer-vm` references this symbol only on non-Windows
// x86/x86_64; every other architecture gets its own `empty_probestack`. Leaving
// 32-bit x86 undefined means it fails loudly at link time rather than silently
// re-introducing the no-op hazard above.
#[cfg(all(feature = "wasm", target_arch = "x86_64", unix))]
core::arch::global_asm!(
    "
    .pushsection .text.__rust_probestack
    .globl __rust_probestack
    .type  __rust_probestack, @function
    .hidden __rust_probestack
__rust_probestack:
    .cfi_startproc
    pushq  %rbp
    .cfi_adjust_cfa_offset 8
    .cfi_offset %rbp, -16
    movq   %rsp, %rbp
    .cfi_def_cfa_register %rbp

    mov    %rax,%r11

    cmp    $0x1000,%r11
    jna    3f
2:
    sub    $0x1000,%rsp
    test   %rsp,8(%rsp)
    sub    $0x1000,%r11
    cmp    $0x1000,%r11
    ja     2b

3:
    sub    %r11,%rsp
    test   %rsp,8(%rsp)

    add    %rax,%rsp

    leave
    .cfi_def_cfa_register %rsp
    .cfi_adjust_cfa_offset -8
    ret
    .cfi_endproc
    .size __rust_probestack, . - __rust_probestack
    .popsection
    ",
    options(att_syntax)
);
