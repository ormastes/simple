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
| Simple (interpreter)   |       22.707 |    interpret |              |              |
| Simple (SMF loader)    |       20.362 |          smf |              |              |
| Simple (native)        |        2.977 |       native |              |              |
| C (gcc -O2)            |        2.773 |       native |              |              |
| Go (compiled)          |       60.222 |       native |              |              |
| Python                 |       25.767 |    interpret |              |              |
| Bun                    |       89.170 |          JIT |              |              |
| Java                   |      154.938 |    JIT (JVM) |              |              |
| Erlang                 |     1700.510 |      BEAM VM |              |              |

## 3. Warm Throughput — fib(35) (in-process: 10 warmup + 20 measured)

| Language               |     Avg (ms) |                                    Notes |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |       93.880 | tree-walk (outer-process, no in-proc timing) |
| Simple (SMF loader)    |       82.994 | bytecode (outer-process, no in-proc timing) |
| Simple (native)        |       74.506 |           AOT via Cranelift (in-process) |
| C (gcc -O2)            |       17.352 |                             baseline AOT |
| Go                     |       59.388 |                                  SSA AOT |
| Python                 |     1906.721 |                         CPython bytecode |
| Bun                    |       83.548 |        JavaScriptCore JIT (steady-state) |
| Java                   |       54.325 |            HotSpot C2 JIT (steady-state) |
| Erlang                 |      143.143 |                    BEAM (single-process) |

## 4. Parallel — spawn 100 workers (20 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |         fail |              std thread_spawn (bytecode) |
| Simple (native)        |       12.907 | channel + OS threads (same as Go pattern) |
| C (pthreads)           |       10.091 |                               OS threads |
| Go                     |        6.795 |           goroutines + chan result (M:N) |
| Python                 |     3114.279 |                          threading (GIL) |
| Bun                    |     1303.723 |                           worker_threads |
| Java                   |      169.305 |                               ThreadPool |
| Erlang                 |     1428.695 |                    lightweight processes |

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
