# JIT hotspot optimization plan interpreter cost

## Status

Fixed.

## Reproduction

```bash
bin/simple run test/05_perf/compiler/jit_hotspot_plan_bench.spl --mode=interpreter
```

Observed on 2026-05-28 with 500 iterations: initial basic hotspot fact planning
cost about 66-87 us per plan in interpreter mode, while full backend-aware
`jit_hotspot_optimization_plan` construction cost about 40-45 ms per plan.
After adding batched backend plan helpers, direct policy checks, pass-name
reuse, and direct Aggressive-level hotspot plans for common rebuild cases, the
full plan rows improved to about 0.26-0.29 ms per plan:

- `jit_hotspot_cranelift_medium_optimization_plan`
- `jit_hotspot_llvm_high_optimization_plan`

## Impact

The current benchmark is a smoke/evidence check, not a runtime hot request path,
but the measured full-plan construction cost is now below the 1 ms acceptance
target. Future backend/cost combinations should either use the direct policy
path when they become hot or keep using the generic metadata path for cold
inspection flows.

## Acceptance

- Backend-aware hotspot optimization plan construction is measured below 1 ms
  per plan in interpreter mode on this benchmark.
- The benchmark keeps checksum-bearing rows for Cranelift medium budget, LLVM
  high budget, and medium-budget Cranelift fallback.

## Verification

2026-05-28:

```text
jit_hotspot_cranelift_medium_optimization_plan_checksum_15000,500,264322,264322,264322,264322,264322,132161455,3
jit_hotspot_llvm_high_optimization_plan_checksum_12500,500,289753,289753,289753,289753,289753,144876932,3
```
