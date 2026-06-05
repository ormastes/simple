# Cross-Language Performance Comparison

**Date:** 2026-06-05
**Machine:** x86_64 / Linux 6.8.0-117-generic
**CPU:** AMD Ryzen Threadripper 1950X 16-Core Processor
**Runs per measurement:** 20 | **Warmup (in-process):** 10 | **fib(N):** 35 | **Workers:** 100

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
| Simple (interpreter)   |       26.378 |    interpret |              |              |
| Simple (SMF loader)    |       19.717 |          smf |              |              |
| Simple (native)        |        4.660 |       native |              |              |
| C (gcc -O2)            |        3.366 |       native |              |              |
| Go (compiled)          |       62.748 |       native |              |              |
| Python                 |       25.732 |    interpret |              |              |
| Bun                    |       91.925 |          JIT |              |              |
| Java                   |      133.677 |    JIT (JVM) |              |              |
| Erlang                 |     1496.866 |      BEAM VM |              |              |

## 3. Warm Throughput — fib(35) (in-process: 10 warmup + 20 measured)

| Language               |     Avg (ms) |                                    Notes |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |       92.425 | tree-walk (outer-process, no in-proc timing) |
| Simple (SMF loader)    |       89.876 | bytecode (outer-process, no in-proc timing) |
| Simple (native)        |       57.182 |           AOT via Cranelift (in-process) |
| C (gcc -O2)            |       12.261 |                             baseline AOT |
| Go                     |       49.810 |                                  SSA AOT |
| Python                 |     1643.529 |                         CPython bytecode |
| Bun                    |       60.349 |        JavaScriptCore JIT (steady-state) |
| Java                   |       47.164 |            HotSpot C2 JIT (steady-state) |
| Erlang                 |      139.121 |                    BEAM (single-process) |

## 4. Parallel — spawn 100 workers (20 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |         fail |              std thread_spawn (bytecode) |
| Simple (native)        |       12.424 | channel + OS threads (same as Go pattern) |
| C (pthreads)           |        9.077 |                               OS threads |
| Go                     |        6.786 |           goroutines + chan result (M:N) |
| Python                 |     2860.359 |                          threading (GIL) |
| Bun                    |      930.975 |                           worker_threads |
| Java                   |      167.486 |                               ThreadPool |
| Erlang                 |     1370.559 |                    lightweight processes |

## 4b. Parallel Binary Sizes

| Language               |         Binary |     Per-thread |                Notes |
|------------------------|----------------|----------------|----------------------|
| Simple (native)        |       131.8 KB | OS default (8MB) |        Cranelift AOT |
| Simple (SMF)           |       118.7 KB | OS default (8MB) |    + runtime 42.8 MB |
| C (pthreads)           |        15.8 KB | OS default (8MB) |              gcc -O2 |
| Go                     |         1.8 MB | goroutine (2-8KB) |        static binary |
| Python                 |        374.0 B | OS default (8MB) |        + interpreter |
| Bun                    |        535.0 B | worker (isolate) |            + runtime |
| Java                   |         2.7 KB |    JVM managed |                + JRE |
| Erlang                 |         1.5 KB |  process (2KB) |            + BEAM VM |

## 4c. Parallel Peak RSS (100 workers)

| Language               |       Peak RSS |         RSS / worker |
|------------------------|----------------|----------------------|
| Simple (native)        |         2.8 MB |                ~28KB |
| C (pthreads)           |         1.8 MB |                ~17KB |
| Go                     |         1.8 MB |                ~17KB |
| Python                 |        10.2 MB |               ~104KB |
| Java                   |        47.8 MB |               ~488KB |

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
> **RSS note:** Per-worker RSS is a rough proxy: (total_RSS - baseline) / 100.
> OS-thread languages (Simple, C) pay ~8MB default stack per thread.
> Go uses 2-8KB goroutine stacks — 1000x less memory per concurrent task.

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
