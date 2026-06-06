# Checking Simple: Compiler, Interpreter, Loader — Performance Guide

How to verify correctness and measure performance of Simple's three execution
modes, compared against bun, python, go, erlang, java, and C.

## Table of Contents

1. [Execution Modes](#execution-modes)
2. [Correctness Checks](#correctness-checks)
3. [Cross-Language Benchmark](#cross-language-benchmark)
4. [Reading the Results](#reading-the-results)
5. [Optimizing Simple Code](#optimizing-simple-code)

## Execution Modes

Simple programs can run in three modes:

| Mode | Flag | What happens | Tradeoff |
|------|------|-------------|----------|
| **Interpreter** | (default) | Tree-walk evaluation by the Rust seed binary | Fastest startup, slowest throughput |
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
bin/simple build lint               # clippy linter on Rust seed
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
| `FANOUT_WORKERS` | 1000 | Large fanout worker count for tiny-task scheduling overhead |
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
green fanout and uses loop-based `thread_spawn_with_args` so the harness does not need
large unrolled source generation.

### What it measures

| Dimension | Workload | What it shows |
|-----------|----------|---------------|
| **Size** | hello + fib source/binary | Deployment footprint |
| **Cold startup** | `hello world` (20 runs avg) | Time-to-first-output |
| **Warm throughput** | `fib(35)` recursive, in-process loop (10 warmup + 20 measured) | Steady-state single-thread perf (JIT reaches hotspot) |
| **Parallel** | 100 workers × LCG 100K iters via channel (`channel_new`/`channel_from_id`/`send`/`recv` from `std.concurrent.channel` — same semantic as Go's goroutine + chan). Simple native uses `thread_spawn_with_args(seed, channel_id, worker)` to pass scalar worker data explicitly. | CPU-heavy worker throughput plus concurrency overhead |
| **Large fanout** | 1000 tiny workers × LCG 32 iters. Simple native uses loop-based `thread_spawn_with_args`/channel; Simple green uses cooperative queue fanout; C uses one pthread per tiny task; Go uses one goroutine per tiny task; Erlang uses one BEAM process per tiny task. | Scheduling overhead where Go should usually beat C pthread creation; Simple native measures OS-thread fanout; Simple green measures queue fanout, not CPU parallelism |
| **Parallel binary size** | Binary/script sizes for parallel workloads across languages | Deployment footprint for concurrent programs |
| **Parallel peak RSS** | `/usr/bin/time -v` peak RSS with 100 workers, baseline subtracted, per-worker delta | Memory cost per concurrent task (baseline = hello world RSS for each language) |

### Languages compared

| Language | Execution model | Why included |
|----------|----------------|--------------|
| Simple (interpreter) | Tree-walk | Baseline — current default mode |
| Simple (SMF loader) | Bytecode VM | Shows bytecode dispatch win |
| Simple (native) | AOT (LLVM/Cranelift) | Shows AOT ceiling |
| Simple `green_spawn` / `green_spawn_value` | Cooperative queue on current OS thread | Implemented green-thread API, but not CPU-parallel or preemptive |
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

**Parallel (100 workers):** Go and C are the current native baselines; the current cross-language Simple row uses OS-thread `thread_spawn_with_args` plus `std.concurrent.channel`. The implemented `std.concurrent.green_thread` API is cooperative and single-OS-thread, so it is not a drop-in Go-goroutine benchmark row. Use `task_spawn`/`rt_pool_*` or future scheduler-aware green threads for Go-like CPU-parallel comparisons.

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

1. **`val` over `var`** — immutable bindings enable constant folding
2. **Iteration over recursion** — tail-call not yet optimized; rewrite deep recursion as loops
3. **Typed collections** — `List<i64>` avoids boxing overhead vs untyped `List`
4. **Avoid string interpolation in hot loops** — pre-format outside the loop
5. **Use `std.testing.benchmark`** for micro-benchmarks with warmup + outlier detection

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
