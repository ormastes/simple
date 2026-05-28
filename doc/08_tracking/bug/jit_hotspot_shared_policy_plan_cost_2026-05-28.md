# JIT hotspot shared-policy plan cost

Date: 2026-05-28
Status: Open

## Summary

`jit_hotspot_optimization_plan` must stay aligned with the shared MIR pass and backend plugin budget planners, but a direct generic-planner implementation regressed pure planning cost to about 12.5 ms per optimization-plan build in the debug interpreter benchmark.

The fast hotspot snapshot was restored and guarded by a consistency regression against the shared planners. Current debug-driver evidence after restoration:

- `jit_hotspot_cranelift_medium_optimization_plan`: p50 1,380,822 ns
- `jit_hotspot_llvm_high_optimization_plan`: p50 1,344,413 ns

This is much better than the generic-planner regression, but still above the earlier sub-millisecond evidence target. Keep this tracked until the shared policy can provide a cached/static plan path with the same semantics and lower cost.

## Repro

```bash
src/compiler_rust/target/debug/simple run test/perf/compiler/jit_hotspot_plan_bench.spl
```

## Expected

Hotspot optimization-plan construction should remain below 1 ms in the debug interpreter benchmark while preserving exact shared-policy pass/plugin semantics.
