# Cross-Language Performance Profile

**Date:** 2026-06-13
**Machine:** x86_64 / Linux 6.8.0-117-generic
**CPU:** AMD Ryzen Threadripper 1950X 16-Core Processor
**Runs per measurement:** 20 | **Warmup (in-process):** 10 | **fib(N):** 35 | **CPU workers:** 100 | **Go GOMAXPROCS:** 100 | **OS thread workers:** 100 | **Cooperative green workers:** 10 | **Multicore green workers:** 100 | **Fanout workers:** 1000 | **Fanout cooperative green workers:** 200 | **Fanout multicore green workers:** 1000 | **Fanout iters:** 32 | **Fanout stress workers:** 512 | **Fanout stress iters:** 1 | **Per-run timeout:** 20s
**Profile script:** `scripts/check/check-cross-language-perf.shs`
**Report path:** `doc/09_report/cross_language_perf_2026-06-13.md`
**Profile contract:** enforced by test/05_perf/profile_scripts/profile_report_contract_test.shs
**Docker isolation:** inside_container=0 | image=`simple-cross-language-perf:latest` | memory=2g | cpus=2.0

## Methodology

- Generates equivalent hello, recursive fib, in-process warm fib, worker, and fanout workloads for each supported runtime.
- Measures binary/script size, cold process startup, warm throughput, parallel worker latency, fanout latency, parallel binary size, and peak RSS where the runtime and compiler are available.
- Uses bounded commands so failed, missing, timed-out, or unavailable lanes are classified instead of silently treated as passing data.
- Supports `PROFILE_DOCKER_ISOLATION=1` to re-exec the same profile script in a Docker container with `--network=none`, a memory limit, a CPU limit, and the current UID/GID. Use this mode for crash-prone native and SMF profile runs. Build `simple-cross-language-perf:latest` with `docker build -t simple-cross-language-perf:latest -f tools/docker/Dockerfile.cross-language-perf tools/docker` for contract-gated C/Go comparison evidence. Unless `PROFILE_DOCKER_SIMPLE_BINARY` is explicitly set, the container run probes each auto-selected Simple binary with `--version`, prefers the release wrapper (`bin/simple` / `bin/release/simple`) when it is runnable, and only falls back to `src/compiler_rust/target/debug/simple` when the release path is unavailable or stale. The current debug binary still hits the Docker-native linker regression tracked in `doc/08_tracking/bug/docker_cross_language_profile_native_link_2026-06-08.md`, so auto mode must not prefer it over a runnable release path.
- Generated Simple concurrency workloads compute an expected checksum and exit nonzero on mismatch, so runtime-pool closure failures cannot be timed as valid M:N evidence.
- Go commands inherit `GOMAXPROCS=100`, defaulting to `CPU_WORKERS`. Contract-gated Go-like M:N evidence requires the recorded Go scheduler width to match `CPU_WORKERS`; caller overrides are exploratory unless they keep that equality.
- Warm throughput is measured in-process where the runtime can print `warm_ms`; interpreter and SMF rows use outer-process timing and are labeled that way.

## Environment

- Host: `dl`
- Shell: `/bin/bash`
- Simple binary: `bin/simple`
- Go runtime: `go version go1.22.2 linux/amd64`
- Go scheduler: `GOMAXPROCS=100 NumCPU=32`

> Size for AOT = binary bytes. For VM/interpreted = script bytes (runtime not included).
> "Runtime dep" column shows runtime size where applicable.
> Warm throughput measured IN-PROCESS (JIT runtimes reach steady state).

## TUI startup scope

TUI startup speed is not measured by this cross-language profile. It is covered by
`scripts/check/check-startup-size-performance-audit.shs`, which builds and times
`Simple standalone TUI` and `Simple full TUI app` rows in
`doc/09_report/startup_size_performance_audit_2026-05-27.md`.

## Artifact Footprint — hello and fib

| Language               |        Hello |          Fib |  Runtime dep |              |
|------------------------|--------------|--------------|--------------|--------------|
| Simple (interpreter)   |       38.0 B |      175.0 B |      14.1 MB |              |
| Simple (SMF loader)    |       3.0 KB |       3.7 KB |      14.1 MB |              |
| Simple (native)        |     451.4 KB |     452.6 KB |         none |              |
| C (gcc -O2)            |      15.6 KB |      15.6 KB |         libc |              |
| Go                     |       1.8 MB |       1.8 MB | none (static) |              |
| Python                 |      137.0 B |      137.0 B | /usr/bin/python3 |              |
| Bun                    |       97.0 B |       97.0 B | /home/ormastes/.bun/bin/bun |              |
| Java                   |      661.0 B |      661.0 B |          JRE |              |
| Erlang                 |      892.0 B |      892.0 B |      BEAM VM |              |

## Cold Startup — hello world (20 runs avg)

| Language               |     Avg (ms) |         Mode |              |              |
|------------------------|--------------|--------------|--------------|--------------|
| Simple (interpreter)   |       38.175 |    interpret |              |              |
| Simple (SMF loader)    |       33.412 |          smf |              |              |
| Simple (native)        |        4.087 |       native |              |              |
| C (gcc -O2)            |        4.028 |       native |              |              |
| Go (compiled)          |       61.853 |       native |              |              |
| Python                 |       27.080 |    interpret |              |              |
| Bun                    |      105.111 |          JIT |              |              |
| Java                   |      167.625 |    JIT (JVM) |              |              |
| Erlang                 |     1746.383 |      BEAM VM |              |              |

## Warm Throughput — fib(35) in process (10 warmup + 20 measured)

| Language               |     Avg (ms) |                                    Notes |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |      106.306 | tree-walk (outer-process, no in-proc timing) |
| Simple (SMF loader)    |      136.325 | bytecode (outer-process, no in-proc timing) |
| Simple (native)        |       76.738 |           AOT via Cranelift (in-process) |
| C (gcc -O2)            |       17.707 |                             baseline AOT |
| Go                     |       57.680 |                                  SSA AOT |
| Python                 |         fail |                         CPython bytecode |
| Bun                    |       93.033 |        JavaScriptCore JIT (steady-state) |
| Java                   |       54.662 |            HotSpot C2 JIT (steady-state) |
| Erlang                 |      151.086 |                    BEAM (single-process) |

## OS Thread Parallel Workers — spawn 100 workers (20 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |      137.602 |    std thread_spawn fork-join (bytecode) |
| Simple (native)        |       98.080 |        thread_spawn fork-join OS threads |
| Simple cooperative green (interp) |       69.251 | cooperative_green_spawn cooperative queue on current OS thread |
| Simple cooperative green (SMF) |       49.667 | cooperative_green_spawn cooperative queue on current OS thread |
| Simple cooperative green (native) |       22.685 | cooperative_green_spawn cooperative queue on current OS thread |
| Simple multicore green (SMF) |      128.783 | multicore_green runtime pool candidate (pool_used=100/100, parallelism=64/64, queue_model=work_stealing) |
| Simple multicore green (native) |       99.848 | multicore_green runtime pool candidate (pool_used=100/100, parallelism=64/64, queue_model=work_stealing) |
| C (pthreads)           |       11.778 |                               OS threads |
| Go                     |        9.816 |           goroutines + chan result (M:N) |
| Python                 |     2748.617 |                          threading (GIL) |
| Bun                    |      514.859 |                           worker_threads |
| Java                   |      197.034 |                               ThreadPool |
| Erlang                 |     1461.210 |                    lightweight processes |

## Large Fanout Scheduling — spawn 1000 tiny workers (20 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |      173.806 |                  std thread_spawn fanout |
| Simple (native)        |       87.933 |               OS-thread fork-join fanout |
| Simple cooperative green (interp) |       65.541 |                 cooperative queue fanout on current OS thread |
| Simple cooperative green (SMF) |       63.627 |                 cooperative queue fanout on current OS thread |
| Simple cooperative green (native) |       12.043 |                 cooperative queue fanout on current OS thread |
| Simple multicore green (SMF) |       47.988 | multicore_green runtime pool fanout (pool_used=1000/1000, parallelism=64/64, queue_model=work_stealing) |
| Simple multicore green (native) |       18.233 | multicore_green runtime pool fanout (pool_used=1000/1000, parallelism=64/64, queue_model=work_stealing) |
| C (pthreads)           |       72.757 |              one OS thread per tiny task |
| Go                     |        7.556 |        goroutine per tiny task + channel |
| Python                 |      155.623 |            threading per tiny task (GIL) |
