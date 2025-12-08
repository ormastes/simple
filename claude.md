# Simple Language Project — Working Rules

## Overview
- Compile-to-SMF pipeline with JIT loading, safe-concurrency focus.
- Structure: `parser` (AST), `compiler` (SMF emit + type check), `loader` (SMF load), `runtime` (GC via Abfall), `driver` (run/watch), `log` (tracing init), `lib` (native stdlib), `plans`/`status` (tracking).

## System Tests (driver-first)
- Prefer end-to-end tests in `src/driver/tests` using the runner (`Runner`) or CLI via `shadow-terminal`; interpreter helpers remain for quick, non-CLI checks.
- GC visibility: `Runner::new_with_gc_logging()` or CLI `--gc-log` surfaces Abfall-backed `gc:start/gc:end` markers; `Runner::with_gc(GcRuntime::with_logger(...))` is best for in-memory assertions.

```rust
use simple_driver::runner::Runner;
use simple_runtime::gc::GcRuntime;

#[test]
fn match_and_gc_logs() {
    let events = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let logger = {
        let events = events.clone();
        move |ev: simple_runtime::gc::GcLogEvent| events.lock().unwrap().push(ev.to_string())
    };
    let runner = Runner::with_gc(GcRuntime::with_logger(logger));
    let exit = runner.run_source("let x = 2\nmatch x:\n    2 => main = 1\n    _ => main = 0").unwrap();
    assert_eq!(exit, 1);
    assert!(events.lock().unwrap().iter().any(|l| l.contains(\"gc:start\")));
}
```

### Quick patterns
- Arithmetic: `(5 + 3) * 4 - 10 / 2` → `27`
- Functions: `fn add(a, b): return a + b; main = add(5, 7)` → `12`
- Structs/enums: construct/sum fields; `Color::Red` vs `is` checks
- Loops: `for i in range(1, 5)` sum → `10`
- Classes: `Calculator.add(3, 4)` → `7`
- Match: literals, wildcard, guards, enum variants; keep runner coverage

## TDD Workflow
1. Add/extend status entry in `status/<feature>.md`.
2. Write a failing system test (runner/CLI) or interpreter helper when lighter weight.
3. Implement in parser/compiler/runtime; keep interfaces narrow via `common/`.
4. Run `cargo test -p simple_driver` (+ unit crates as needed).
5. Update status to COMPLETED/IN_PROGRESS.

## Logging / AOP-style guidance
- Rust has no runtime AOP; use compile-time weaving via proc macros. `#[tracing::instrument]` captures entry/exit/args with minimal boilerplate.
```rust
use tracing::instrument;

#[instrument] // closest to AspectJ pointcut weaving
fn process_order(id: u64, amount: f64) -> Result<(), Error> {
    // body
}
```
- Prefer span-based `tracing` over ad-hoc prints; keep logging opt-in for perf-sensitive paths. `log/` crate provides one-time init honoring `SIMPLE_LOG`/`RUST_LOG`.

## Module Boundaries
- `parser`: pure front-end, no runtime deps.
- `compiler`: parser + common; type checks via `simple-type` crate; targets ABIs defined in `common`.
- `runtime`: GC wrapper lives in `src/runtime/gc`, backed by Abfall; implements `common::gc::GcAllocator`.
- `driver`: orchestrates compile/load/run/watch; CLI flag `--gc-log` toggles verbose GC markers.
- `loader`/`native_loader`: dynamic loading only.
- `log`: centralized tracing setup.
- `lib`: native stdlib helpers; avoid compiler/runtime coupling.
