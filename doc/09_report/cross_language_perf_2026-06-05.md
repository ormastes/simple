# Cross-Language Performance Comparison

**Date:** 2026-06-05
**Machine:** x86_64 / Linux 6.8.0-117-generic
**CPU:** AMD Ryzen Threadripper 1950X 16-Core Processor
**Runs per measurement:** 20 | **Warmup (in-process):** 10 | **fib(N):** 35 | **Workers:** 100 | **Per-run timeout:** 30s

> Size for AOT = binary bytes. For VM/interpreted = script bytes (runtime not included).
> "Runtime dep" column shows runtime size where applicable.
> Warm throughput measured IN-PROCESS (JIT runtimes reach steady state).

## 1. Binary / Script Size

| Language               |        Hello |          Fib |  Runtime dep |              |
|------------------------|--------------|--------------|--------------|--------------|
| Simple (interpreter)   |       38.0 B |      175.0 B |      42.8 MB |              |
| Simple (SMF loader)    |       3.0 KB |       3.7 KB |      42.8 MB |              |
| Simple (native)        |      38.3 KB |      40.0 KB |         none |              |
| C (gcc -O2)            |      15.6 KB |      15.6 KB |         libc |              |
| Go                     |       1.8 MB |       1.8 MB | none (static) |              |
| Python                 |      137.0 B |      137.0 B | /usr/bin/python3 |              |
| Bun                    |       97.0 B |       97.0 B | /home/ormastes/.bun/bin/bun |              |
| Java                   |      661.0 B |      661.0 B |          JRE |              |
| Erlang                 |      892.0 B |      892.0 B |      BEAM VM |              |

## 2. Cold Startup — hello world (20 runs avg)

| Language               |     Avg (ms) |         Mode |              |              |
|------------------------|--------------|--------------|--------------|--------------|
| Simple (interpreter)   |       21.786 |    interpret |              |              |
| Simple (SMF loader)    |       16.289 |          smf |              |              |
| Simple (native)        |        4.131 |       native |              |              |
| C (gcc -O2)            |        4.226 |       native |              |              |
| Go (compiled)          |       60.569 |       native |              |              |
| Python                 |       24.519 |    interpret |              |              |
| Bun                    |      113.533 |          JIT |              |              |
| Java                   |      151.897 |    JIT (JVM) |              |              |
| Erlang                 |     1526.948 |      BEAM VM |              |              |

## 3. Warm Throughput — fib(35) (in-process: 10 warmup + 20 measured)

| Language               |     Avg (ms) |                                    Notes |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |       98.874 | tree-walk (outer-process, no in-proc timing) |
| Simple (SMF loader)    |       97.275 | bytecode (outer-process, no in-proc timing) |
| Simple (native)        |       72.242 |           AOT via Cranelift (in-process) |
| C (gcc -O2)            |       15.645 |                             baseline AOT |
| Go                     |       56.604 |                                  SSA AOT |
| Python                 |         fail |                         CPython bytecode |
| Bun                    |       65.052 |        JavaScriptCore JIT (steady-state) |
| Java                   |       50.877 |            HotSpot C2 JIT (steady-state) |
| Erlang                 |      119.931 |                    BEAM (single-process) |

## 4. Parallel — spawn 100 workers (20 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |         fail |              std thread_spawn (bytecode) |
| Simple (native)        |       12.863 | channel + OS threads (same as Go pattern) |
| C (pthreads)           |       10.402 |                               OS threads |
| Go                     |        8.321 |           goroutines + chan result (M:N) |
| Python                 |     2856.348 |                          threading (GIL) |
| Bun                    |      715.255 |                           worker_threads |
| Java                   |      177.851 |                               ThreadPool |
| Erlang                 |     1477.809 |                    lightweight processes |

### 4a. Thread Enhancement Follow-Up

The table above is the OS-thread/channel baseline captured before the runtime-owned
`task_spawn` pool path landed. On 2026-06-05, the new pool ABI was verified with a
focused native smoke rather than this cross-language harness:

- `rt_pool_submit`, `rt_pool_join`, and `rt_pool_is_done` resolve as native symbols in `build/thread_enhancement/task_spawn_runtime_pool_native`.
- `build/thread_enhancement/task_spawn_runtime_pool_native` exited `0` after joining four pool-backed LCG tasks.
- The harness still needs a dedicated `task_spawn` row before it can report the Tier 0 `<9ms` pool target.

## 4b. Parallel Binary Sizes

| Language               |         Binary |     Per-thread |                Notes |
|------------------------|----------------|----------------|----------------------|
| Simple (native)        |       146.3 KB | OS default (8MB) |        Cranelift AOT |
| Simple (SMF)           |       145.9 KB | OS default (8MB) |    + runtime 42.8 MB |
| C (pthreads)           |        15.8 KB | OS default (8MB) |              gcc -O2 |
| Go                     |         1.8 MB | goroutine (2-8KB) |        static binary |
| Python                 |        374.0 B | OS default (8MB) |        + interpreter |
| Bun                    |        535.0 B | worker (isolate) |            + runtime |
| Java                   |         2.7 KB |    JVM managed |                + JRE |
| Erlang                 |         1.5 KB |  process (2KB) |            + BEAM VM |

## 4c. Parallel Peak RSS (100 workers)

| Language               |       Peak RSS |   Baseline RSS |     Per-worker delta |
|------------------------|----------------|----------------|----------------------|
| Simple (native)        |         2.5 MB |         2.0 MB |                 ~5KB |
| C (pthreads)           |         2.0 MB |         2.0 MB |                 ~0KB |
| Go                     |         2.0 MB |         2.0 MB |                 ~0KB |
| Python                 |        10.2 MB |        10.2 MB |                 ~0KB |
| Java                   |        47.7 MB |        43.0 MB |                ~48KB |

> **Workload:** LCG (Linear Congruential Generator) with 100K iterations per worker.
> Each worker reads shared constants (LCG_A, LCG_C, LCG_M, ITERS).
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
> **RSS note:** Per-worker delta = (parallel_RSS - hello_baseline_RSS) / 100.
> Baseline measures the runtime's fixed overhead (startup, GC, stdlib).
> OS-thread languages (Simple, C) pay ~8MB default stack per thread but RSS
> reflects only committed pages, not reserved virtual memory.

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
