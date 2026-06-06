# Checking Simple: Compiler, Interpreter, Loader — Performance Guide

How to verify correctness and measure performance of Simple's three execution
modes, compared against bun, python, go, erlang, java, and C.

## Table of Contents

- **Execution modes:** [Execution Modes](#execution-modes)
- **Correctness gates:** [Correctness Checks](#correctness-checks)
- **Cross-language evidence:** [Cross-Language Benchmark](#cross-language-benchmark)
- **Result interpretation:** [Reading the Results](#reading-the-results)
- **Simple optimization:** [Optimizing Simple Code](#optimizing-simple-code)

## Execution Modes

Simple programs can run in three modes:

| Mode | Flag | What happens | Tradeoff |
|------|------|-------------|----------|
| **Interpreter** | (default) | Tree-walk evaluation by the Simple interpreter in the bootstrap binary | Fastest startup, slowest throughput |
| **SMF Loader** | `.smf` file | Compile to `.smf` bytecode, then execute via bytecode VM | Medium startup, ~2-5x faster dispatch |
| **Native** | `--native` | AOT compile via LLVM or Cranelift, standalone ELF/PE | Slowest compile step, fastest throughput |

```
# Run directly (interpreter)
bin/simple my_program.spl

# Compile to SMF bytecode, then run
bin/simple compile my_program.spl -o out.smf
bin/simple out.smf

# Compile to native binary, then run
bin/simple compile my_program.spl --native -o out
./out

# Run tests in each mode
bin/simple test path/to/spec.spl                     # interpreter
bin/simple test path/to/spec.spl --mode=smf          # SMF
bin/simple test path/to/spec.spl --compile            # native
```

## Correctness Checks

### Compiler self-verification

```bash
bin/simple build bootstrap          # 3-stage self-compilation (stage1→stage2→stage3 must match)
bin/simple build check              # lint + fmt --check + full test suite
bin/simple build lint               # linter for the bootstrap implementation
bin/simple build fmt --check        # format check
```

### Test suite across modes

```bash
# Full suite in each mode (verifies semantic parity)
bin/simple test --mode=interpreter
bin/simple test --mode=smf
bin/simple test --compile

# Single spec across all modes
for mode in interpreter smf native; do
    echo "=== $mode ==="
    bin/simple test path/to/spec.spl --mode=$mode
done
```

### Known caveats

- `--mode=native` specs can no-op or segfault before test bodies when generated BDD calls (`rt_bdd_*` / `std.spec`) are unresolved — verify semantic ground truth in interpreter mode, and use a direct native entrypoint with hard `rt_exit` oracles when validating native runtime ABI paths
- `--mode=smf` can swallow runtime errors and report PASSED — cross-check against interpreter
- See memory: `feedback_compile_mode_false_greens.md`

## Cross-Language Benchmark

### Quick run

```bash
sh scripts/check/check-cross-language-perf.shs
```

### Environment variables

| Variable | Default | Purpose |
|----------|---------|---------|
| `RUNS` | 20 | Measurement iterations per benchmark |
| `WARM_IN_PROCESS` | 10 | In-process warmup iterations (JIT reaches steady state) |
| `FIB_N` | 35 | Fibonacci depth for throughput test |
| `WORKERS` | 100 | Parallel worker count |
| `CPU_WORKERS` | `WORKERS` or 100 | Shared CPU-heavy worker count for semantic rows |
| `OS_THREAD_WORKERS` | `CPU_WORKERS` | Simple OS-thread worker count for `thread_spawn` rows |
| `COOPERATIVE_GREEN_WORKERS` | capped at 10 by default | Current single-carrier green queue worker count |
| `MULTICORE_GREEN_WORKERS` | `CPU_WORKERS` | Pool-backed `multicore_green_spawn` worker count |
| `FANOUT_WORKERS` | 1000 | Large fanout worker count for tiny-task scheduling overhead |
| `FANOUT_COOPERATIVE_GREEN_WORKERS` | capped at 200 by default | Cooperative green fanout count; capped to avoid oversized generated source |
| `FANOUT_MULTICORE_GREEN_WORKERS` | `FANOUT_WORKERS` | Pool-backed multicore-green fanout count |
| `FANOUT_ITERS` | 32 | Tiny per-task LCG iterations for the large fanout benchmark |
| `RUN_TIMEOUT` | 30 | Per-command timeout in seconds for measured commands and RSS probes |
| `SIMPLE_BINARY` | `bin/simple` | Path to Simple compiler |
| `BUILD_DIR` | `build/cross_lang_perf` | Workload compile output |
| `REPORT_PATH` | `doc/09_report/cross_language_perf_<date>.md` | Output report |

The harness deletes a Simple output before recording a failed compile, so a
failed native or SMF compile cannot leave a stale binary/bytecode file that is
then measured as if it belonged to the current run. Long-running measured
commands and Simple compile steps are bounded by `RUN_TIMEOUT`; set it higher
for full reports on slow hosts, or lower it for smoke evidence. The 1000-worker
Simple OS-thread fanout source is intentionally reported separately from Simple
green fanout and uses loop-based `thread_spawn` fork-join so the harness does not need
large unrolled source generation.
Generated Simple concurrency workloads compute an expected checksum and exit
nonzero on mismatch, so runtime-pool closure lookup failures or wrong joins are
classified as failed rows instead of performance wins.
The profile-report contract rejects numbered concurrency aliases such as
`thread_spawn2`, `spawn_isolated2`, and `spawn_limited2`; use the semantic API
names in reports, generated workloads, and profile-script comments.

### What it measures

| Dimension | Workload | What it shows |
|-----------|----------|---------------|
| **Size** | hello + fib source/binary | Deployment footprint |
| **Cold startup** | `hello world` (20 runs avg) | Time-to-first-output |
| **Warm throughput** | `fib(35)` recursive, in-process loop (10 warmup + 20 measured) | Steady-state single-thread perf (JIT reaches hotspot) |
| **Parallel** | 100 workers × LCG 100K iters. Simple native uses Pure Simple `thread_spawn` fork-join for the OS-thread baseline. Simple multicore green uses `multicore_green_spawn` and fails the row unless every handle reports `used_runtime_pool()`. | CPU-heavy worker throughput plus concurrency overhead |
| **Large fanout** | 1000 tiny workers × LCG 32 iters. Simple native uses loop-based `thread_spawn` fork-join; Simple cooperative green uses cooperative queue fanout; C uses one pthread per tiny task; Go uses one goroutine per tiny task; Erlang uses one BEAM process per tiny task. | Scheduling overhead where Go should usually beat C pthread creation; Simple native measures OS-thread fanout; Simple cooperative green measures queue fanout, not CPU parallelism |
| **Parallel binary size** | Binary/script sizes for parallel workloads across languages | Deployment footprint for concurrent programs |
| **Parallel peak RSS** | `/usr/bin/time -v` peak RSS with 100 workers, baseline subtracted, per-worker delta | Memory cost per concurrent task (baseline = hello world RSS for each language) |

### Languages compared

| Language | Execution model | Why included |
|----------|----------------|--------------|
| Simple (interpreter) | Tree-walk | Baseline — current default mode |
| Simple (SMF loader) | Bytecode VM | Shows bytecode dispatch win |
| Simple (native) | AOT (LLVM/Cranelift) | Shows AOT ceiling |
| Simple `cooperative_green_spawn` / `cooperative_green_spawn_value` | Cooperative queue on current OS thread | Implemented green-thread API, but not CPU-parallel or preemptive |
| Simple `multicore_green_spawn` | Bounded runtime worker pool through `rt_pool_*` | Current Pure Simple M:N candidate row for CPU-heavy comparisons; profile workloads fail if `used_runtime_pool()` is false |
| Simple `task_spawn` | Runtime worker pool when `rt_pool_*` links | Intended Simple path for Go-like parallel benchmark work |
| C (gcc -O2) | AOT native | Absolute performance floor |
| Go | AOT + goroutines | Low-overhead concurrency |
| Python | CPython bytecode | Common scripting baseline |
| Bun | JavaScriptCore JIT | Modern JS JIT comparison |
| Java | HotSpot C2 JIT | JVM warm-up / peak perf |
| Erlang | BEAM VM | Lightweight-process concurrency king |

### Size definition

- **AOT** (C, Go, Simple native): binary bytes — self-contained
- **VM/bytecode** (Java, Erlang, Simple SMF): `.class`/`.beam`/`.smf` bytes — requires runtime
- **Interpreted** (Python, Bun, Simple interp.): script bytes — requires interpreter binary

## Reading the Results

### Expected ranking (approximate)

**Cold startup:** C ≈ Simple-native < Go < Bun < Simple-interp ≈ Simple-SMF < Python < Java < Erlang

**Warm throughput (fib35):** C ≈ Simple-native < Go < Java (after JIT) < Bun < Simple-SMF < Erlang < Simple-interp < Python

**Parallel (100 workers):** Go and C are the current native baselines; the OS-thread Simple row uses Pure Simple `thread_spawn` fork-join. `thread_spawn_with_args` is tracked separately while its native ABI blocker is active, so it is not the profile baseline. The implemented `std.concurrent.cooperative_green` API is cooperative and single-OS-thread, so it is not a drop-in Go-goroutine benchmark row. The `std.concurrent.multicore_green` row uses `multicore_green_spawn` over `rt_pool_*` as the current Pure Simple M:N candidate until a scheduler-aware green runtime lands. The generated multicore-green workloads check every handle with `used_runtime_pool()` and fail the row if the runtime pool was unavailable.

### What matters per use case

| Use case | Key metric | Best Simple mode |
|----------|-----------|-----------------|
| CLI tools, scripts | Cold startup | Interpreter (instant start) |
| MCP servers, daemons | Warm throughput | SMF or native |
| Batch processing | Throughput + parallel | Native |
| Development iteration | Edit-run cycle | Interpreter |
| Deployment | Binary size | Native (single binary) |

## Optimizing Simple Code

All optimization in **pure Simple** (`.spl`) — do not modify Rust seed or C runtime.

### Mode escalation

```
Interpreter → SMF Loader → Native
   (dev)       (staging)    (production)
```

### Code-level optimizations

- **Immutable bindings:** prefer `val` over `var` to enable constant folding
- **Iterative control flow:** rewrite deep recursion as loops where practical because tail-call is not yet optimized
- **Typed collections:** use `List<i64>` to avoid boxing overhead vs untyped `List`
- **Hot-loop formatting:** pre-format strings outside hot loops
- **Benchmark harness:** use `std.testing.benchmark` for micro-benchmarks with warmup and outlier detection

### Built-in perf tools

```bash
# Lint for perf anti-patterns
bin/simple build lint                            # includes mcp_perf_lint

# Micro-benchmark with the stdlib
bin/simple test test/bench/my_bench_spec.spl     # BenchSuite in std.testing.benchmark

# Full audit (binary size + startup + GPU backends)
sh scripts/check/check-startup-size-performance-audit.shs
```

## GUI Performance Benchmarks

### GTK GUI Size & Speed Baseline

```bash
sh scripts/check/check-gtk-gui-size-speed-baseline.shs
```

Measures: frame time (us), binary size, cache hit rates, peak RSS, vector text determinism.
Compares Simple web renderer vs GTK widget loop.

### Startup & Size Audit

```bash
sh scripts/check/check-startup-size-performance-audit.shs
```

Measures: cold startup (20 runs avg), binary size, ELF sections, loaded library deps, peak RSS.
Covers: hello world, TUI, mmap, TCP/UDP/HTTP/HTTPS, CUDA/OpenCL/ROCm backends.

### Qt Size Baseline

```bash
sh scripts/check/check-qt-gui-size-baseline.shs
```

Measures: binary size only (Qt minimal widget vs Simple web artifact).

### Known GUI perf gaps

- **FPS measurement** — not yet implemented; scripts measure frame latency (us/iteration) not sustained FPS
- **User interaction latency** — scripts test static scenes only, not event-driven UI response time

### Benchmark template (pure Simple)

```simple
use std.nogc_sync_mut.src.testing.benchmark.{BenchSuite}

fn main():
    var suite = BenchSuite.create("my-benchmark")

    suite.run_bench("baseline", 1000, fn():
        # your hot loop here
        val x = some_computation()
    )

    suite.run_bench("optimized", 1000, fn():
        # optimized version
        val x = some_computation_v2()
    )

    val report = suite.summary()
    println(report)
```
