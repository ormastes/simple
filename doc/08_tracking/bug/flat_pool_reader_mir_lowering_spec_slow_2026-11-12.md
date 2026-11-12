# Perf: `flat_pool_reader_mir_lowering_spec` takes 367 s CPU-bound (seed-run)

**Status:** open. **Class:** performance, not a hang. **Evidence:** seed-run only (Rust seed
`pinned-bfe789dd4118` `test`, 12G cap, idle-ish shared host, about 55 GB free).

## Measurement
- `test/01_unit/compiler/50.mir/flat_pool_reader_mir_lowering_spec.spl` alone gives `3 total, 3 passed`
  in **367 s** wall. Inside a 21-file chunk it hit the chunk's 1800 s timeout.
- The child process sat at 100 % of one core with a **flat RSS of about 1.1 GB** for minutes. That
  looks like compute, not allocation growth or a lock wait.
- Split runs: the two HIR-only tests and the one codec-MIR test each finish under a 300 s cap,
  so no single test spins forever.

## Profile hint (cheap)
With `SIMPLE_PARSE_PHASE_PROFILE=1`, each of the 3 tests re-parses the real
`src/compiler/10.frontend/core/flat_pool_codec.spl` (1030 lines):

```
PARSEPHASE parse_module_body 28388809 ... bridge 617689 path src/compiler/10.frontend/core/flat_pool_codec.spl
PARSEPHASE parse_module_body 76366    ... path app/main.spl
```

So about **28 s per parse × 3 ≈ 85 s** (23 %) is the interpreted parser on one 1030-line
file. The remaining ~280 s is HIR lowering, plus MIR lowering of the whole codec for test 2,
in the seed interpreter. `SIMPLE_HIR_PHASE_PROFILE` / `SIMPLE_COMPILER_PHASE_PROFILE`
printed no totals on this path. `perf` and `gdb` attach are blocked on this host
(`perf_event_paranoid=4`, `ptrace_scope=1`).

## Cheap mitigations to consider
1. Parse the codec once per spec file (a module-level cached `codec_ast`) instead of once per `it`.
   That saves about 57 s without changing coverage.
2. The parse of a 1030-line file costing 28 s interpreted is about 27 ms/line. Compare it with
   other parse-heavy specs to see whether `parse_module_body` has a superlinear term.
3. Re-measure on the pure-Simple native CLI once one is deployed. Interpreter cost does not
   predict native cost.
