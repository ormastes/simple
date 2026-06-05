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
| Simple (interpreter)   |       25.636 |    interpret |              |              |
| Simple (SMF loader)    |       25.155 |          smf |              |              |
| Simple (native)        |        2.710 |       native |              |              |
| C (gcc -O2)            |        2.879 |       native |              |              |
| Go (compiled)          |       68.741 |       native |              |              |
| Python                 |       24.578 |    interpret |              |              |
| Bun                    |       86.271 |          JIT |              |              |
| Java                   |      129.713 |    JIT (JVM) |              |              |
| Erlang                 |         fail |      BEAM VM |              |              |

## 3. Warm Throughput — fib(35) (in-process: 10 warmup + 20 measured)

| Language               |     Avg (ms) |                                    Notes |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |       84.431 | tree-walk (outer-process, no in-proc timing) |
| Simple (SMF loader)    |       79.157 | bytecode (outer-process, no in-proc timing) |
| Simple (native)        |       55.379 |      AOT via LLVM/Cranelift (in-process) |
| C (gcc -O2)            |       12.457 |                             baseline AOT |
| Go                     |       50.872 |                                  SSA AOT |
| Python                 |     1510.354 |                         CPython bytecode |
| Bun                    |       59.364 |        JavaScriptCore JIT (steady-state) |
| Java                   |       46.182 |            HotSpot C2 JIT (steady-state) |
| Erlang                 |         fail |                    BEAM (single-process) |

## 4. Parallel — spawn 100 workers (20 runs avg)

| Language               |     Avg (ms) |                        Concurrency model |
|------------------------|--------------|------------------------------------------|
| Simple (interpreter)   |          n/a |       extern FFI segfault in interpreter |
| Simple (SMF loader)    |         fail |              std thread_spawn (bytecode) |
| Simple (native)        |          n/a |    codegen bug: rt_thread_join undefined |
| C (pthreads)           |       10.123 |                               OS threads |
| Go                     |        4.153 |                         goroutines (M:N) |
| Python                 |       40.949 |                          threading (GIL) |
| Bun                    |    13694.158 |                           worker_threads |
| Java                   |       96.476 |                               ThreadPool |
| Erlang                 |         fail |                    lightweight processes |

## Size Definition

| Category | What "size" means |
|----------|-------------------|
| AOT (C, Go, Simple native) | Binary bytes on disk — self-contained |
| VM/bytecode (Java, Erlang, Simple SMF) | `.class`/`.beam`/`.smf` bytes — requires runtime |
| Interpreted (Python, Bun, Simple interp.) | Script bytes — requires interpreter binary |

## How to Optimize Simple Performance

All optimization in **pure Simple** (`.spl`) — do not modify Rust seed or C runtime.

1. **Interpreter → SMF loader** — `simple compile file.spl -o file.smf` for ~2-5x dispatch speedup
2. **SMF → native** — `simple compile file.spl --native -o file` for AOT code approaching C-level numeric perf
3. **Use `val` over `var`** — immutable bindings enable more aggressive constant folding
4. **Avoid deep recursion** — rewrite as iteration where possible (tail-call not yet optimized)
5. **Use typed collections** — `List<i64>` avoids boxing overhead vs untyped `List`
6. **Profile with `std.testing.benchmark`** — warmup + outlier detection built in
7. **`bin/simple build check`** — lint catches perf anti-patterns (mcp_perf_lint)
