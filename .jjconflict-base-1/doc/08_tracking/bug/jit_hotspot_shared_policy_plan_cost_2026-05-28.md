# JIT hotspot shared-policy plan cost

Date: 2026-05-28
Status: Fixed

## Summary

`jit_hotspot_optimization_plan` must stay aligned with the shared MIR pass and backend plugin budget planners, but a direct generic-planner implementation regressed pure planning cost to about 12.5 ms per optimization-plan build in the debug interpreter benchmark.

The fast hotspot snapshot was restored and guarded by a consistency regression against the shared planners. The hotspot path now builds the backend plan directly from the guarded snapshot for the common Cranelift medium and LLVM high-cost rebuild cases. Current debug-driver evidence after the fast path:

- `jit_hotspot_cranelift_medium_optimization_plan`: p50 537,610 ns
- `jit_hotspot_llvm_high_optimization_plan`: p50 701,387 ns

This is below the sub-millisecond evidence target while preserving the shared-policy guard.

## Repro

```bash
src/compiler_rust/target/debug/simple run test/perf/compiler/jit_hotspot_plan_bench.spl
```

## Expected

Hotspot optimization-plan construction should remain below 1 ms in the debug interpreter benchmark while preserving exact shared-policy pass/plugin semantics.
