# JIT string append is quadratic (100k appends = 259s)

- **Date:** 2026-08-18  - **Status:** OPEN
- **Symptom:** the cross-language compute benchmark
  (`doc/10_metrics/startup/cross_language_compute_compile_benchmark_2026-08-18.md`)
  measured 100k string appends under `bin/simple run` (Cranelift JIT, seed
  2026-08-18 06:12) at **259.3s** vs Bun 0.054s, Go 0.022s, CPython 28.8s.
  Loop/array benches are within ~10x of Go — this axis is ~10,000x off, the
  signature of a quadratic (full copy per append, no amortized growth).
- **Repro:** scratchpad xbench2 str bench: build a string by `s = s + piece`
  100k times; time `bin/simple run`.
- **Suspect:** runtime text concat allocates a fresh buffer per append (no
  capacity doubling / rope); check `rt_string_*` concat path and any
  string-builder lowering (`string_builder_opt` MIR pass may not fire on
  this shape).
- **Unblock:** amortized growth in the concat fast path, or make the
  string-builder optimization catch `s = s + x` loops; add a differential
  perf budget once fixed.
