# Cross-Language Performance Profile

**Date:** 2026-06-06
**Machine:** x86_64 / Linux 6.8.0-117-generic
**CPU:** AMD Ryzen Threadripper 1950X 16-Core Processor
**Runs per measurement:** 1 | **Warmup (in-process):** 1 | **fib(N):** 35 | **Workers:** 2 | **Green workers:** 2 | **Fanout workers:** 4 | **Fanout iters:** 2 | **Per-run timeout:** 8s
**Profile script:** `scripts/check/check-cross-language-perf.shs`
**Report path:** `doc/09_report/cross_language_perf_2026-06-06.md`

> **Historical report:** this smoke predates the current split between
> `cooperative_green_spawn` and `multicore_green_spawn`. Rows named
> `Simple green` are cooperative queue evidence only and must not be cited as
> Go-like M:N CPU-parallel evidence. Use
> `doc/09_report/cross_language_perf_parallel_smoke.md` or
> `doc/09_report/cross_language_perf_parallel_large_2026-06-07.md` for current
> gated multicore-green profile evidence.

## Methodology

- Generates equivalent hello, recursive fib, in-process warm fib, worker, and fanout workloads for each supported runtime.
- Measures binary/script size, cold process startup, warm throughput, parallel worker latency, fanout latency, parallel binary size, and peak RSS where the runtime and compiler are available.
- Uses bounded commands so failed, missing, timed-out, or unavailable lanes are classified instead of silently treated as passing data.
- Warm throughput is measured in-process where the runtime can print `warm_ms`; interpreter and SMF rows use outer-process timing and are labeled that way.

## Environment

- Host: `dl`
- Shell: `/bin/bash`
- Simple binary: `bin/simple`

> Size for AOT = binary bytes. For VM/interpreted = script bytes (runtime not included).
> "Runtime dep" column shows runtime size where applicable.
> Warm throughput measured IN-PROCESS (JIT runtimes reach steady state).

## TUI startup scope

TUI startup speed is not measured by this cross-language profile. It is covered by
`scripts/check/check-startup-size-performance-audit.shs`, which builds and times
`Simple standalone TUI` and `Simple full TUI app` rows in
`doc/09_report/startup_size_performance_audit_2026-05-27.md`.

## 1. Binary / Script Size

| Language               |        Hello |          Fib |  Runtime dep |              |
|------------------------|--------------|--------------|--------------|--------------|
| Simple (interpreter)   |       38.0 B |      175.0 B |      42.9 MB |              |
| Simple (SMF loader)    |       3.0 KB |       3.7 KB |      42.9 MB |              |
| Simple (native)        |      38.3 KB |      40.0 KB |         none |              |
| C (gcc -O2)            |      15.6 KB |      15.6 KB |         libc |              |
| Go                     |       1.8 MB |       1.8 MB | none (static) |              |
| Python                 |      137.0 B |      137.0 B | /usr/bin/python3 |              |
| Bun                    |       97.0 B |       97.0 B | /home/ormastes/.bun/bin/bun |              |
| Java                   |      661.0 B |      661.0 B |          JRE |              |
| Erlang                 |      916.0 B |      916.0 B |      BEAM VM |              |

## 2. Cold Startup — hello world (1 runs avg)

| Language               |     Avg (ms) |         Mode |              |              |
|------------------------|--------------|--------------|--------------|--------------|
| Simple (interpreter)   |      206.575 |    interpret |              |              |
| Simple (SMF loader)    |      153.131 |          smf |              |              |
| Simple (native)        |       23.528 |       native |              |              |
| C (gcc -O2)            |       12.550 |       native |              |              |
| Go (compiled)          |       84.094 |       native |              |              |
| Python                 |       39.029 |    interpret |              |              |
| Bun                    |      201.595 |          JIT |              |              |
| Java                   |      205.215 |    JIT (JVM) |              |              |
| Erlang                 |     1854.397 |      BEAM VM |              |              |

## 3. Warm Throughput — fib(35) (in-process: 1 warmup + 1 measured)

| Language               |     Avg (ms) |                                    Notes |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |      126.778 | tree-walk (outer-process, no in-proc timing) |
| Simple (SMF loader)    |      131.411 | bytecode (outer-process, no in-proc timing) |
| Simple (native)        |       76.665 |           AOT via Cranelift (in-process) |
| C (gcc -O2)            |       26.135 |                             baseline AOT |
| Go                     |       69.069 |                                  SSA AOT |
| Python                 |     2425.749 |                         CPython bytecode |
| Bun                    |      131.339 |        JavaScriptCore JIT (steady-state) |
| Java                   |       66.505 |            HotSpot C2 JIT (steady-state) |
| Erlang                 |      194.125 |                    BEAM (single-process) |

## 4. Parallel — spawn 2 workers (1 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |         fail |              std thread_spawn (bytecode) |
| Simple (native)        |       11.366 | channel + OS threads (same as Go pattern) |
| Simple green (interp)  |       50.770 |      green_spawn_value cooperative queue |
| Simple green (SMF)     |         fail | green_spawn_value cooperative queue (SMF mutable-global runtime blocker) |
| Simple green (native)  |        7.904 |      green_spawn_value cooperative queue |
| C (pthreads)           |        5.787 |                               OS threads |
| Go                     |        9.634 |           goroutines + chan result (M:N) |
| Python                 |      123.446 |                          threading (GIL) |
| Bun                    |      101.781 |                           worker_threads |
| Java                   |      168.001 |                               ThreadPool |
| Erlang                 |     1752.195 |                    lightweight processes |

## 4a. Large Fanout — spawn 4 tiny workers (1 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |       24.169 |                  std thread_spawn fanout |
| Simple (native)        |         fail |    OS-thread fanout + channel (segfault) |
| Simple green (interp)  |       53.102 |                 cooperative queue fanout |
| Simple green (SMF)     |         fail | cooperative queue fanout (SMF mutable-global runtime blocker) |
| Simple green (native)  |        6.326 |                 cooperative queue fanout |
| C (pthreads)           |        9.200 |              one OS thread per tiny task |
| Go                     |       10.952 |        goroutine per tiny task + channel |
| Python                 |       45.892 |            threading per tiny task (GIL) |
| Bun                    |      131.437 |              worker_thread per tiny task |
| Java                   |      172.333 |   cached ThreadPool future per tiny task |
| Erlang                 |     1618.305 |               BEAM process per tiny task |

## 4b. Parallel Binary Sizes

| Language               |         Binary |     Per-thread |                Notes |
|------------------------|----------------|----------------|----------------------|
| Simple (native)        |        51.2 KB | OS default (8MB) |        Cranelift AOT |
| Simple (SMF)           |         8.4 KB | OS default (8MB) |    + runtime 42.9 MB |
| Simple green (native)  |        43.8 KB | current OS thread |    cooperative queue |
| Simple green (SMF)     |        11.6 KB | current OS thread |    + runtime 42.9 MB |
| C (pthreads)           |        15.8 KB | OS default (8MB) |              gcc -O2 |
| Go                     |         1.8 MB | goroutine (2-8KB) |        static binary |
| Python                 |        370.0 B | OS default (8MB) |        + interpreter |
| Bun                    |        533.0 B | worker (isolate) |            + runtime |
| Java                   |         2.7 KB |    JVM managed |                + JRE |
| Erlang                 |         1.5 KB |  process (2KB) |            + BEAM VM |

## 4c. Parallel Peak RSS (2 workers)

| Language               |       Peak RSS |   Baseline RSS |     Per-worker delta |
|------------------------|----------------|----------------|----------------------|
| Simple (native)        |         2.5 MB |         2.0 MB |               ~256KB |
| C (pthreads)           |         2.0 MB |         1.8 MB |               ~128KB |
| Go                     |         2.0 MB |         2.0 MB |                 ~0KB |
| Python                 |        10.2 MB |        10.0 MB |               ~128KB |
| Java                   |        47.8 MB |        43.0 MB |              ~2432KB |

> **Workload:** LCG (Linear Congruential Generator) with 100K iterations per worker.
> Each worker reads shared constants (LCG_A, LCG_C, LCG_M, ITERS).
> The large fanout section uses many tiny workers with `FANOUT_ITERS` iterations
> to expose scheduling overhead; this is the case where Go goroutines should
> usually beat one-pthread-per-task C. Simple reports both OS-thread fanout
> through `thread_spawn` and cooperative green-thread queue fanout separately.
>
> **Simple concurrency rows:** `Simple (native)` uses `thread_spawn`, which is
> the OS-thread API. `Simple green` uses `green_spawn_value`, which exercises the
> implemented cooperative green-thread queue on the current OS thread; it does
> not run in parallel and is not a Go M:N goroutine equivalent. The green row uses the
> `GREEN_WORKERS` count from the report header because the current cooperative
> seed is intentionally separate from the OS-thread/Goroutine worker count.
> Current direct-run blocker: SMF mutable globals can segfault before the
> cooperative queue runs, so the SMF green row is classified instead of treated
> as a scheduling result when that runtime failure appears.
>
> **Design comparison — Simple channels vs Go channels:**
> Both Simple and Go use the same pattern: workers send results through a channel,
> main collects via recv. Simple's `val` constants captured by closures add a
> **compile-time immutability guarantee** — the compiler rejects mutation of shared
> data. Go relies on convention (don't mutate shared vars) or channels for all data
> flow. C shares via globals with no safety guarantee.
> Same semantic, same safety for result collection; Simple adds compile-time
> enforcement for shared read-only data.
>
> **RSS note:** Per-worker delta = (parallel_RSS - hello_baseline_RSS) / worker count.
> Baseline measures the runtime's fixed overhead (startup, GC, stdlib).
> OS-thread languages (Simple, C) pay ~8MB default stack per thread but RSS
> reflects only committed pages, not reserved virtual memory.

## Reproducibility

Run the script from the repository root:

```sh
sh scripts/check/check-cross-language-perf.shs
```

Useful knobs: `RUNS`, `FIB_N`, `WORKERS`, `GREEN_WORKERS`, `FANOUT_WORKERS`,
`FANOUT_ITERS`, `WARM_IN_PROCESS`, `RUN_TIMEOUT`, `SIMPLE_BINARY`,
`BUILD_DIR`, and `REPORT_PATH`.

## Limitations

- Different runtimes have different startup and warmup models; the report labels
  in-process and outer-process timing separately.
- Missing compilers or runtimes are reported as unavailable and should not be
  read as slower-than-Simple data.
- OS scheduler load, CPU frequency scaling, thermal state, VM host load, and JIT
  warmup can move small timing deltas enough to require repeated runs before a
  release-blocking performance claim.

## Size Definition

| Category | What "size" means |
|----------|-------------------|
| AOT (C, Go, Simple native) | Binary bytes on disk — self-contained |
| VM/bytecode (Java, Erlang, Simple SMF) | `.class`/`.beam`/`.smf` bytes — requires runtime |
| Interpreted (Python, Bun, Simple interp.) | Script bytes — requires interpreter binary |

## How to Optimize Simple Performance

All optimization in **pure Simple** (`.spl`) — do not modify Rust seed or C runtime.

1. **Interpreter → SMF loader** — `simple compile file.spl -o file.smf` for ~2-5x dispatch speedup
2. **SMF → native** — `simple compile file.spl --native -o file` for AOT via Cranelift (~4x slower than gcc -O2 for recursive workloads; no tail-call opt yet)
3. **Use `val` over `var`** — immutable bindings enable more aggressive constant folding
4. **Avoid deep recursion** — rewrite as iteration where possible (tail-call not yet optimized)
5. **Use typed collections** — `List<i64>` avoids boxing overhead vs untyped `List`
6. **Profile with `std.testing.benchmark`** — warmup + outlier detection built in
7. **`bin/simple build check`** — lint catches perf anti-patterns (mcp_perf_lint)
