# Cross-Language Performance Profile

**Date:** 2026-06-07
**Machine:** x86_64 / Linux 6.8.0-117-generic
**CPU:** AMD Ryzen Threadripper 1950X 16-Core Processor
**Runs per measurement:** 1 | **Warmup (in-process):** 3 | **fib(N):** 35 | **CPU workers:** 4 | **OS thread workers:** 4 | **Cooperative green workers:** 4 | **Multicore green workers:** 4 | **Fanout workers:** 20 | **Fanout cooperative green workers:** 20 | **Fanout multicore green workers:** 20 | **Fanout iters:** 32 | **Fanout stress workers:** 128 | **Fanout stress iters:** 1 | **Per-run timeout:** 30s
**Profile script:** `scripts/check/check-cross-language-perf.shs`
**Report path:** `doc/09_report/cross_language_perf_parallel_smoke.md`
**Profile contract:** enforced by test/05_perf/profile_scripts/profile_report_contract_test.shs
**Docker isolation:** inside_container=0 | image=`simple-test-isolation:latest` | memory=2g | cpus=2.0

## Methodology

- Generates equivalent hello, recursive fib, in-process warm fib, worker, and fanout workloads for each supported runtime.
- Measures binary/script size, cold process startup, warm throughput, parallel worker latency, fanout latency, parallel binary size, and peak RSS where the runtime and compiler are available.
- Uses bounded commands so failed, missing, timed-out, or unavailable lanes are classified instead of silently treated as passing data.
- Supports `PROFILE_DOCKER_ISOLATION=1` to re-exec the same profile script in a Docker container with `--network=none`, a memory limit, a CPU limit, and the current UID/GID. Use this mode for crash-prone native and SMF profile runs; full contract-gated C/Go comparison reports require a Docker image with the cross-language toolchains installed.
- Generated Simple concurrency workloads compute an expected checksum and exit nonzero on mismatch, so runtime-pool closure failures cannot be timed as valid M:N evidence.
- Warm throughput is measured in-process where the runtime can print `warm_ms`; interpreter and SMF rows use outer-process timing and are labeled that way.

## Environment

- Host: `dl`
- Shell: `/bin/bash`
- Simple binary: `./src/compiler_rust/target/debug/simple`
- Go runtime: `go version go1.22.2 linux/amd64`
- Go scheduler: `GOMAXPROCS=32 NumCPU=32`

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
| Simple (interpreter)   |       38.0 B |      175.0 B |     436.8 MB |              |
| Simple (SMF loader)    |       3.0 KB |       3.7 KB |     436.8 MB |              |
| Simple (native)        |       6.1 MB |       6.1 MB |         none |              |
| C (gcc -O2)            |      15.6 KB |      15.6 KB |         libc |              |
| Go                     |       1.8 MB |       1.8 MB | none (static) |              |
| Python                 |      137.0 B |      137.0 B | /usr/bin/python3 |              |
| Bun                    |       97.0 B |       97.0 B | /home/ormastes/.bun/bin/bun |              |
| Java                   |      661.0 B |      661.0 B |          JRE |              |
| Erlang                 |      884.0 B |      884.0 B |      BEAM VM |              |

## Cold Startup — hello world (1 runs avg)

| Language               |     Avg (ms) |         Mode |              |              |
|------------------------|--------------|--------------|--------------|--------------|
| Simple (interpreter)   |       41.885 |    interpret |              |              |
| Simple (SMF loader)    |       31.022 |          smf |              |              |
| Simple (native)        |        6.068 |       native |              |              |
| C (gcc -O2)            |        5.415 |       native |              |              |
| Go (compiled)          |       66.778 |       native |              |              |
| Python                 |       31.799 |    interpret |              |              |
| Bun                    |       92.914 |          JIT |              |              |
| Java                   |      120.752 |    JIT (JVM) |              |              |
| Erlang                 |     1466.617 |      BEAM VM |              |              |

## Warm Throughput — fib(35) in process (3 warmup + 1 measured)

| Language               |     Avg (ms) |                                    Notes |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |      110.569 | tree-walk (outer-process, no in-proc timing) |
| Simple (SMF loader)    |       89.497 | bytecode (outer-process, no in-proc timing) |
| Simple (native)        |       59.693 |           AOT via Cranelift (in-process) |
| C (gcc -O2)            |       13.214 |                             baseline AOT |
| Go                     |       49.637 |                                  SSA AOT |
| Python                 |     1599.579 |                         CPython bytecode |
| Bun                    |       64.532 |        JavaScriptCore JIT (steady-state) |
| Java                   |       49.148 |            HotSpot C2 JIT (steady-state) |
| Erlang                 |      125.746 |                    BEAM (single-process) |

## OS Thread Parallel Workers — spawn 4 workers (1 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |       35.575 |    std thread_spawn fork-join (bytecode) |
| Simple (native)        |       11.988 |        thread_spawn fork-join OS threads |
| Simple cooperative green (interp) |      169.617 | cooperative_green_spawn_value cooperative queue |
| Simple cooperative green (SMF) |         fail | cooperative_green_spawn_value cooperative queue (SMF mutable-global runtime blocker) |
| Simple cooperative green (native) |       14.925 | cooperative_green_spawn_value cooperative queue |
| Simple multicore green (SMF) |       33.163 | multicore_green runtime pool candidate (pool_used=4/4, parallelism=4/4, queue_model=work_stealing) |
| Simple multicore green (native) |       11.151 | multicore_green runtime pool candidate (pool_used=4/4, parallelism=4/4, queue_model=work_stealing) |
| C (pthreads)           |        7.295 |                               OS threads |
| Go                     |        7.808 |           goroutines + chan result (M:N) |
| Python                 |      149.846 |                          threading (GIL) |
| Bun                    |       85.165 |                           worker_threads |
| Java                   |       91.243 |                               ThreadPool |
| Erlang                 |     1353.619 |                    lightweight processes |

## Large Fanout Scheduling — spawn 20 tiny workers (1 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |          extern thread FFI not supported |
| Simple (SMF loader)    |       27.214 |                  std thread_spawn fanout |
| Simple (native)        |        6.001 |               OS-thread fork-join fanout |
| Simple cooperative green (interp) |      139.052 |                 cooperative queue fanout |
| Simple cooperative green (SMF) |         fail | cooperative queue fanout (SMF mutable-global runtime blocker) |
| Simple cooperative green (native) |        7.153 |                 cooperative queue fanout |
| Simple multicore green (SMF) |       26.063 | multicore_green runtime pool fanout (pool_used=20/20, parallelism=4/4, queue_model=work_stealing) |
| Simple multicore green (native) |        4.953 | multicore_green runtime pool fanout (pool_used=20/20, parallelism=4/4, queue_model=work_stealing) |
| C (pthreads)           |        4.301 |              one OS thread per tiny task |
| Go                     |        4.294 |        goroutine per tiny task + channel |
| Python                 |       24.139 |            threading per tiny task (GIL) |
| Bun                    |      108.450 |              worker_thread per tiny task |
| Java                   |       90.213 |   cached ThreadPool future per tiny task |
| Erlang                 |     1316.616 |               BEAM process per tiny task |

## Simple vs Go vs C Large Fanout Stress — spawn 128 tiny workers (1 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| C (pthreads)           |       13.322 |                  pthread per stress task |
| Simple multicore green (native) |        6.545 | multicore_green stress fanout (pool_used=128/128, parallelism=4/4, queue_model=work_stealing) |
| Go                     |        7.392 |          goroutine per stress task (M:N) |

## Parallel Artifact Footprint

| Language               |         Binary |     Per-thread |                Notes |
|------------------------|----------------|----------------|----------------------|
| Simple (native)        |         6.1 MB | OS default (8MB) |        Cranelift AOT |
| Simple (SMF)           |         6.9 KB | OS default (8MB) |   + runtime 436.8 MB |
| Simple cooperative green (native) |         6.1 MB | current OS thread |    cooperative queue |
| Simple cooperative green (SMF) |        12.7 KB | current OS thread |   + runtime 436.8 MB |
| Simple multicore green (native) |         6.1 MB |   runtime pool |      multicore_green |
| Simple multicore green (SMF) |        10.3 KB |   runtime pool |   + runtime 436.8 MB |
| C (pthreads)           |        15.8 KB | OS default (8MB) |              gcc -O2 |
| Go                     |         1.8 MB | goroutine (2-8KB) |        static binary |
| Python                 |        370.0 B | OS default (8MB) |        + interpreter |
| Bun                    |        533.0 B | worker (isolate) |            + runtime |
| Java                   |         2.7 KB |    JVM managed |                + JRE |
| Erlang                 |         1.5 KB |  process (2KB) |            + BEAM VM |

## Parallel Peak RSS — 4 workers

| Language               |       Peak RSS |   Baseline RSS |     Per-worker delta |
|------------------------|----------------|----------------|----------------------|
| Simple (native)        |         6.2 MB |         5.8 MB |               ~128KB |
| Simple multicore green |         6.0 MB |         5.8 MB |                ~64KB |
| C (pthreads)           |         2.0 MB |         2.0 MB |                 ~0KB |
| Go                     |         2.0 MB |         2.0 MB |                 ~0KB |
| Python                 |        10.2 MB |        10.2 MB |                 ~0KB |
| Java                   |        47.2 MB |        43.0 MB |              ~1088KB |

> **Workload:** LCG (Linear Congruential Generator) with 100K iterations per worker.
> Generated Simple workers use a capture-free deterministic LCG kernel so
> checksum evidence does not depend on native/SMF global-load behavior or the
> separate native pool loop-closure capture blocker.
> The large fanout section uses many tiny workers with `FANOUT_ITERS` iterations
> to expose scheduling overhead; this is the case where Go goroutines should
> usually beat one-pthread-per-task C. Simple reports both OS-thread fanout
> through `thread_spawn`, cooperative green-thread queue fanout, and
> pool-backed `multicore_green_spawn` fanout separately. Generated
> multicore-green workloads call `multicore_green_set_parallelism(CPU_WORKERS)`
> before spawning tasks and print `multicore_green_parallelism=requested/actual`
> evidence so the hosted pool limit is explicit.
> The Simple-vs-Go-vs-C large fanout stress section repeats the stress shape at
> `FANOUT_STRESS_WORKERS` workers and includes a Simple multicore-green native
> row with `pool_used=N/N` evidence. It exists so the pthread-per-task baseline
> cannot be mistaken for Go-style M:N scheduling when fanout grows.
>
> **Simple concurrency rows:** `Simple (native)` uses `thread_spawn`, which is
> the OS-thread API. `thread_spawn_with_args` remains tracked separately by
> `scripts/check/check-thread-spawn-with-args-native.shs` as an ABI smoke, so
> the perf rows stay focused on scheduler behavior.
> `Simple cooperative green` uses
> `cooperative_green_spawn_value`, which exercises the
> implemented cooperative green-thread queue on the current OS thread; it does
> not run in parallel and is not a Go M:N goroutine equivalent. `Simple multicore
> green` is the Pure Simple `multicore_green_spawn`/`rt_pool_*` candidate row for bounded
> worker-pool scheduling with a hosted parallelism limit; generated multicore-green workloads require every
> handle to report `used_runtime_pool()` so inline fallback cannot masquerade as
> M:N evidence. The large-fanout multicore-green generated source keeps compact
> handle-array joins and a capture-free worker kernel so the profile measures
> scheduler fanout rather than the separate native closure-capture blocker. It
> is not yet the final scheduler-aware green API.
> The cooperative-green row uses the `COOPERATIVE_GREEN_WORKERS` count from the
> report header because the current cooperative Simple implementation is intentionally separate
> from the OS-thread/Goroutine worker count.
> Current direct-run blocker: SMF mutable globals can segfault before the
> cooperative queue runs, so the SMF cooperative-green row is classified instead
> of treated as a scheduling result when that runtime failure appears.
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

For crash isolation, run the same entrypoint through Docker:

```sh
PROFILE_DOCKER_ISOLATION=1 sh scripts/check/check-cross-language-perf.shs
```

Useful knobs: `RUNS`, `FIB_N`, `CPU_WORKERS`, `OS_THREAD_WORKERS`,
`COOPERATIVE_GREEN_WORKERS`, `MULTICORE_GREEN_WORKERS`, `GREEN_WORKERS`
(compatibility alias), `FANOUT_WORKERS`, `FANOUT_COOPERATIVE_GREEN_WORKERS`,
`FANOUT_MULTICORE_GREEN_WORKERS`, `FANOUT_ITERS`, `FANOUT_STRESS_WORKERS`,
`FANOUT_STRESS_ITERS`, `WARM_IN_PROCESS`, `RUN_TIMEOUT`, `SIMPLE_BINARY`,
`BUILD_DIR`, `REPORT_PATH`, `PROFILE_DOCKER_ISOLATION`,
`PROFILE_DOCKER_IMAGE`, `PROFILE_DOCKER_MEMORY`, `PROFILE_DOCKER_CPUS`, and
`PROFILE_DOCKER_SIMPLE_BINARY`.

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

- **Interpreter to SMF loader** — `simple compile file.spl -o file.smf` for ~2-5x dispatch speedup
- **SMF to native** — `simple compile file.spl --native -o file` for AOT via Cranelift (~4x slower than gcc -O2 for recursive workloads; no tail-call opt yet)
- **Immutable bindings** — prefer `val` over `var` so constant folding can be more aggressive
- **Iterative control flow** — avoid deep recursion where a loop is practical (tail-call not yet optimized)
- **Typed collections** — `List<i64>` avoids boxing overhead vs untyped `List`
- **Benchmark harness** — use `std.testing.benchmark` for warmup and outlier detection
- **Build checks** — `bin/simple build check` catches perf anti-patterns such as `mcp_perf_lint`
