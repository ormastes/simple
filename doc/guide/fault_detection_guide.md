# Fault Detection Guide

The Simple interpreter includes built-in fault detection for common runtime issues.
All features are toggleable via environment variables, CLI flags, or Simple FFI calls.

## CLI Flags

```bash
simple --stack-overflow-detection script.spl
simple --max-recursion-depth=500 script.spl
simple --timeout=30 script.spl
simple --execution-limit=1000000 script.spl
```

## Simple FFI Functions

```simple
extern fn rt_fault_set_stack_overflow_detection(enabled: bool)
extern fn rt_fault_set_max_recursion_depth(depth: i64)
extern fn rt_fault_set_timeout(secs: i64)
extern fn rt_fault_set_execution_limit(limit: i64)
```

## Stack Overflow Detection

Detects infinite recursion by tracking call depth with an atomic counter and RAII guard.

```bash
# Enabled by default in debug builds
SIMPLE_STACK_OVERFLOW_DETECTION=1 ./target/debug/simple_old script.spl

# Custom limit (default: 1000)
SIMPLE_MAX_RECURSION_DEPTH=500 ./target/debug/simple_old script.spl

# Via CLI flag
simple --max-recursion-depth=500 script.spl
```

**Error message:**
```
stack overflow: recursion depth 1000 exceeded limit 1000 in function 'recurse'
```

**Overhead:** ~2 atomic ops per function call (Relaxed ordering, ~2 CPU cycles). Single flag check when disabled.

**Implementation:** `src/rust/compiler/src/interpreter_state.rs` (RAII `RecursionGuard`)

## Timeout Detection (Wall-Clock)

A watchdog thread monitors wall-clock time and sets an atomic flag when the deadline is exceeded.
Loop back-edges check this flag alongside existing interrupt and execution limit checks.

```bash
# Set timeout in seconds (0 = disabled, default)
SIMPLE_TIMEOUT_SECONDS=30 ./target/debug/simple_old script.spl

# Quick test for infinite loops
SIMPLE_TIMEOUT_SECONDS=1 ./target/debug/simple_old infinite_loop.spl
```

**Error message:**
```
timeout: execution exceeded 30 second limit
```

**Overhead:** Zero when disabled (single AtomicBool load). Background thread wakes every 100ms when enabled.

**Implementation:** `src/rust/compiler/src/watchdog.rs`

## Crash Detection

Top-level execution is wrapped in `std::panic::catch_unwind`. Panics are caught and reported
as errors instead of crashing the process.

```
fatal: interpreter crashed: index out of bounds
This is a bug in the Simple compiler. Please report it.
```

Exit code `101` indicates an internal crash.

A panic hook (debug builds) logs the full backtrace to stderr and tracing.

**Overhead:** Zero (only activates on panic).

**Implementation:** `src/rust/driver/src/cli/basic.rs`, `src/rust/driver/src/cli/init.rs`

## Memory Leak Detection

Tracks heap size after each GC cycle. If the heap grows more than 10% over 10 consecutive
GC cycles, emits a `tracing::warn!` diagnostic.

```bash
# Opt-in
SIMPLE_LEAK_DETECTION=1 ./target/debug/simple_old script.spl
```

**Warning output (via tracing):**
```
WARN: Possible memory leak: heap grew 15.2% over 10 GC cycles
```

**Overhead:** ~10 comparisons per GC cycle (already expensive path). Zero when disabled.

**Implementation:** `src/rust/runtime/src/memory/gc.rs` (`LeakDetector`)

## Execution Limit (Pre-existing)

Counts instructions and errors if limit exceeded. Prevents infinite loops at the instruction level.

```bash
SIMPLE_EXECUTION_LIMIT=1000000 ./target/debug/simple_old script.spl
SIMPLE_EXECUTION_LIMIT_ENABLED=false ./target/debug/simple_old script.spl
```

## Sanitizer Support

For deeper memory analysis, use Rust sanitizers or Valgrind:

```bash
# Address Sanitizer (requires nightly)
RUSTFLAGS="-Zsanitizer=address" cargo +nightly test -p simple-driver

# With Valgrind
valgrind --leak-check=full ./target/debug/simple_old script.spl
```

A `sanitizer` Cargo profile can be added for convenience:
```toml
[profile.sanitizer]
inherits = "dev"
# Use with: RUSTFLAGS="-Zsanitizer=address" cargo +nightly build --profile sanitizer
```

## Configuration Summary

| Env Variable | CLI Flag | Default | Purpose |
|---|---|---|---|
| `SIMPLE_STACK_OVERFLOW_DETECTION` | `--stack-overflow-detection` | debug=on, release=off | Recursion depth check |
| `SIMPLE_MAX_RECURSION_DEPTH` | `--max-recursion-depth=N` | 1000 | Max call depth |
| `SIMPLE_TIMEOUT_SECONDS` | `--timeout=N` | 0 (off) | Wall-clock timeout |
| `SIMPLE_EXECUTION_LIMIT` | `--execution-limit=N` | 10000000 | Instruction count limit |
| `SIMPLE_EXECUTION_LIMIT_ENABLED` | - | debug=on, release=off | Enable instruction limit |
| `SIMPLE_LEAK_DETECTION` | - | false | Heap growth heuristic |

## Verification

1. **Stack overflow:** `fn recurse(n): recurse(n+1)` -- errors at depth 1000
2. **Timeout:** `SIMPLE_TIMEOUT_SECONDS=1` with `while true: pass` -- errors after 1s
3. **Crash:** Trigger a panic path -- get error message instead of crash
4. **Leak:** Long-lived program -- check tracing output for leak warnings
5. **Existing tests:** `cargo test --workspace` still passes
