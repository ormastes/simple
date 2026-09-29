# Simple, Python, and Bun Interpreter CPU Benchmark — 2026-09-02

## Status

Measured comparison on one local Apple M4 host. Simple is substantially faster
than CPython on these integer workloads, but 2.3–5.0x slower than Bun's JIT at
steady state. This supports the earlier 2–4x estimate only approximately: the
exact ratio depends on workload, and the integer loop measured 5x.

The available Simple executable identifies itself as a bootstrap seed at
runtime. Therefore these rows characterize the available Simple interpreter,
not an admitted current pure-Simple Stage4 CLI. They must not be used as a
release qualification result.

## Host and Runtimes

- Host: Apple M4, arm64, macOS 26.5 (25F71)
- Repository revision: `c846dc3c074d03392b7f2041fa7e74290a67a925`
- Simple executable: `bin/release/aarch64-apple-darwin-macho/simple.bak-2026-07-25-cli`
- Simple executable SHA-256: `dcfe9a0dacfb0e4d7344162a524b9b2d154162a96792264fccd0d639abc023e5`
- Python: CPython 3.14.3
- Bun: 1.3.14, JavaScriptCore JIT

## Method

Three programs used equivalent integer semantics and fixed inputs:

1. Integer loop/reduction: 2,000,000 iterations.
2. Function-call workload: 1,000,000 calls.
3. Branch-heavy state machine: 2,000,000 transitions.

All runtimes produced the exact checksum tuple
`1007993832,32745229621,17428573`. Each startup-inclusive row uses 11 fresh
processes. Each steady row is the paired slope `(ten-workload process time -
one-workload process time) / 9`, which removes estimated process startup without
requiring runtime-specific clocks. Times came from macOS `/usr/bin/time -lp`.
The timer's 10 ms resolution limits precision for Bun and the shortest Simple
runs. RSS is the maximum observed process RSS across both run sizes.

## Results

| Runtime | Workload | Startup p50/p95 | Steady p50/p95 | Max RSS |
|---|---|---:|---:|---:|
| Simple interpreter | loop | 40/60 ms | 5.56/5.56 ms | 18.45 MiB |
| Python | loop | 80/120 ms | 74.44/83.33 ms | 14.69 MiB |
| Bun JIT | loop | 10/10 ms | 1.11/2.22 ms | 32.56 MiB |
| Simple interpreter | calls | 40/40 ms | 4.44/14.44 ms | 18.45 MiB |
| Python | calls | 60/70 ms | 56.67/62.22 ms | 14.70 MiB |
| Bun JIT | calls | 10/10 ms | 1.11/1.11 ms | 33.92 MiB |
| Simple interpreter | branches | 50/50 ms | 7.78/8.89 ms | 18.45 MiB |
| Python | branches | 120/130 ms | 111.11/121.11 ms | 14.70 MiB |
| Bun JIT | branches | 10/10 ms | 3.33/4.44 ms | 34.09 MiB |

## Interpretation

- Simple steady execution is about 13–14x faster than CPython here.
- Simple steady execution is about 5.0x Bun for the loop, 4.0x for calls, and
  2.3x for branches.
- Simple startup is 4–5x Bun, but 1.5–2.4x faster than Python.
- Bun spends more memory to obtain its JIT performance; its observed RSS is
  about 1.8x Simple. Python has the lowest observed RSS.
- These CPU results do not explain compile latency. Compilation bottlenecks are
  separately attributed to package reuse, semantic/MIR retention,
  monomorphization, LLVM code generation, and linking.

## Limitations and Next Gate

Repeat with the admitted Stage4 pure-Simple CLI when available, retain raw
machine-readable samples, use a sub-millisecond monotonic timer, pin power and
background-load conditions, and add native Simple rows. Until then, classify
this report as comparative development evidence rather than a release gate.
