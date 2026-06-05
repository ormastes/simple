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
