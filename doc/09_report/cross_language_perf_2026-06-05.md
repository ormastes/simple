# Cross-Language Performance Comparison

**Date:** 2026-06-05
**Machine:** x86_64 / Linux 6.8.0-117-generic
**CPU:** AMD Ryzen Threadripper 1950X 16-Core Processor
**Runs per measurement:** 20 | **Warmup (in-process):** 10 | **fib(N):** 35 | **Workers:** 100

> Size for AOT = binary bytes. For VM/interpreted = script bytes (runtime not included).
> "Runtime dep" column shows runtime size where applicable.
> Warm throughput measured IN-PROCESS (JIT runtimes reach steady state).

> Thread enhancement rerun note: the 2026-06-05 rerun attempted by
> `scripts/check/check-cross-language-perf.shs` reported Simple parallel
> compile failures for native and SMF, then stalled during the 100-worker
> parallel section before the full report completed. Treat the parallel section
> below as partial evidence until the harness completes cleanly.

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
| Simple (interpreter)   |       23.927 |    interpret |              |              |
| Simple (SMF loader)    |       20.256 |          smf |              |              |
| Simple (native)        |        2.352 |       native |              |              |
| C (gcc -O2)            |        1.714 |       native |              |              |
| Go (compiled)          |       62.336 |       native |              |              |
| Python                 |       26.043 |    interpret |              |              |
| Bun                    |       99.775 |          JIT |              |              |
| Java                   |      135.110 |    JIT (JVM) |              |              |
| Erlang                 |     1473.245 |      BEAM VM |              |              |

## 3. Warm Throughput — fib(35) (in-process: 10 warmup + 20 measured)

| Language               |     Avg (ms) |                                    Notes |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |       88.070 | tree-walk (outer-process, no in-proc timing) |
| Simple (SMF loader)    |       79.850 | bytecode (outer-process, no in-proc timing) |
| Simple (native)        |       57.701 |           AOT via Cranelift (in-process) |
| C (gcc -O2)            |       13.362 |                             baseline AOT |
| Go                     |       52.498 |                                  SSA AOT |
| Python                 |     1562.385 |                         CPython bytecode |
| Bun                    |       65.725 |        JavaScriptCore JIT (steady-state) |
| Java                   |       50.646 |            HotSpot C2 JIT (steady-state) |
| Erlang                 |      121.771 |                    BEAM (single-process) |

## 4. Parallel — spawn 100 workers (20 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |         fail |              std thread_spawn (bytecode) |
| Simple (native)        |       47.902 | channel + OS threads (same as Go pattern) |
| C (pthreads)           |       29.728 |                               OS threads |
| Go                     |       17.682 |           goroutines + chan result (M:N) |
| Python                 |     2978.362 |                          threading (GIL) |
| Bun                    |      858.814 |                           worker_threads |
| Java                   |      174.156 |                               ThreadPool |
