# Cross-Language Performance Profile

**Date:** 2026-06-06
**Machine:** x86_64 / Linux 6.8.0-117-generic
**CPU:** AMD Ryzen Threadripper 1950X 16-Core Processor
**Runs per measurement:** 1 | **Warmup (in-process):** 10 | **fib(N):** 35 | **Workers:** 2 | **Green workers:** 2 | **Fanout workers:** 20 | **Fanout iters:** 32 | **Per-run timeout:** 20s
**Profile script:** `scripts/check/check-cross-language-perf.shs`
**Report path:** `doc/09_report/cross_language_perf_parallel_smoke.md`

## Methodology

- Generates equivalent hello, recursive fib, in-process warm fib, worker, and fanout workloads for each supported runtime.
- Measures binary/script size, cold process startup, warm throughput, parallel worker latency, fanout latency, parallel binary size, and peak RSS where the runtime and compiler are available.
- Uses bounded commands so failed, missing, timed-out, or unavailable lanes are classified instead of silently treated as passing data.
- Warm throughput is measured in-process where the runtime can print `warm_ms`; interpreter and SMF rows use outer-process timing and are labeled that way.

## Environment

- Host: `dl`
- Shell: `/bin/bash`
- Simple binary: `src/compiler_rust/target/debug/simple`

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
| Simple (interpreter)   |       38.0 B |      175.0 B |     435.3 MB |              |
| Simple (SMF loader)    |       3.0 KB |       3.7 KB |     435.3 MB |              |
| Simple (native)        |     531.9 KB |     534.7 KB |         none |              |
| C (gcc -O2)            |      15.6 KB |      15.6 KB |         libc |              |
| Go                     |       1.8 MB |       1.8 MB | none (static) |              |
| Python                 |      137.0 B |      137.0 B | /usr/bin/python3 |              |
| Bun                    |       97.0 B |       97.0 B | /home/ormastes/.bun/bin/bun |              |
| Java                   |      661.0 B |      661.0 B |          JRE |              |
| Erlang                 |      948.0 B |      948.0 B |      BEAM VM |              |

## 2. Cold Startup — hello world (1 runs avg)

| Language               |     Avg (ms) |         Mode |              |              |
|------------------------|--------------|--------------|--------------|--------------|
| Simple (interpreter)   |      110.954 |    interpret |              |              |
| Simple (SMF loader)    |       52.773 |          smf |              |              |
| Simple (native)        |        8.325 |       native |              |              |
| C (gcc -O2)            |        6.643 |       native |              |              |
| Go (compiled)          |       79.794 |       native |              |              |
| Python                 |       32.655 |    interpret |              |              |
| Bun                    |      180.366 |          JIT |              |              |
| Java                   |      201.804 |    JIT (JVM) |              |              |
| Erlang                 |     1847.459 |      BEAM VM |              |              |

## 3. Warm Throughput — fib(35) (in-process: 10 warmup + 1 measured)

| Language               |     Avg (ms) |                                    Notes |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |      159.460 | tree-walk (outer-process, no in-proc timing) |
| Simple (SMF loader)    |      137.043 | bytecode (outer-process, no in-proc timing) |
| Simple (native)        |       73.549 |           AOT via Cranelift (in-process) |
| C (gcc -O2)            |       27.604 |                             baseline AOT |
| Go                     |       71.354 |                                  SSA AOT |
| Python                 |         fail |                         CPython bytecode |
| Bun                    |      132.843 |        JavaScriptCore JIT (steady-state) |
| Java                   |       68.089 |            HotSpot C2 JIT (steady-state) |
| Erlang                 |      191.805 |                    BEAM (single-process) |

## 4. Parallel — spawn 2 workers (1 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |       51.435 |    std thread_spawn_with_args (bytecode) |
| Simple (native)        |       11.305 | channel + OS threads (same as Go pattern) |
| Simple green (interp)  |      220.625 |      green_spawn_value cooperative queue |
| Simple green (SMF)     |         fail | green_spawn_value cooperative queue (SMF mutable-global runtime blocker) |
| Simple green (native)  |        8.955 |      green_spawn_value cooperative queue |
| C (pthreads)           |        5.562 |                               OS threads |
| Go                     |       11.877 |           goroutines + chan result (M:N) |
| Python                 |      135.908 |                          threading (GIL) |
