# Optimization Plugin JIT Hotspot Performance Evidence

Date: 2026-05-24

## Scope

This report records representative benchmarks for the JIT hotspot planning
boundary. It measures pure Simple plan construction, runtime fact extraction,
eligibility checks, invalidation bookkeeping, specialization provider
compile-decision overhead, and backend-aware optimization plan selection. It
does not measure native JIT code emission or claim end-to-end program speedup.

## Command

```bash
bin/simple run test/05_perf/compiler/jit_hotspot_plan_bench.spl --mode=interpreter
```

## Result

Status: PASS

```text
label,iters,p50_ns,p99_ns,p99_9_ns,min_ns,max_ns,total_ns,kops_per_s
jit_hotspot_cold_plan_checksum_1000,500,38246,38246,38246,38246,38246,19123104,26
jit_hotspot_ready_plan_checksum_2000,500,40876,40876,40876,40876,40876,20438191,24
jit_hotspot_invalidated_plan_checksum_2000,500,52174,52174,52174,52174,52174,26087263,19
jit_hotspot_specialized_decision_checksum_21000,500,52861,52861,52861,52861,52861,26430999,18
jit_hotspot_cranelift_medium_optimization_plan_checksum_15000,500,264322,264322,264322,264322,264322,132161455,3
jit_hotspot_llvm_high_optimization_plan_checksum_12500,500,289753,289753,289753,289753,289753,144876932,3
jit_hotspot_medium_budget_backend_choice_checksum_33500,500,153641,153641,153641,153641,153641,76820822,6
```

## Interpretation

The benchmark proves that hotspot planning has a runnable measurement harness and
stable checksums for cold, ready, invalidated, and specialization-provider
decision paths. The 2026-05-28 update adds checksum-bearing backend plan rows:
Cranelift under a medium compile-cost budget, LLVM under a high compile-cost
budget, and medium-budget fallback to Cranelift when LLVM is too expensive.

The backend choice helper remains cheap enough for policy checks. Full
backend-aware optimization plan construction improved from about 40-45 ms to
about 0.26-0.29 ms in interpreter mode after adding batched backend plan
helpers, direct policy checks, pass-name reuse, and direct Aggressive-level
hotspot plans for the common Cranelift and LLVM rebuild cases. This clears the
below-1 ms acceptance target tracked in
`doc/08_tracking/bug/jit_hotspot_optimization_plan_interpreter_cost_2026-05-28.md`.
The numbers are interpreter-mode planning costs only; native code emission and
end-to-end runtime speedup require separate backend benchmarks.

## 2026-05-29 Refresh

Command:

```bash
bin/simple run test/05_perf/compiler/jit_hotspot_plan_bench.spl --mode=interpreter
```

Status: PASS

The run used the refreshed local `bin/simple` artifact after the stale artifact
was replaced with the guarded runtime.

```text
label,iters,p50_ns,p99_ns,p99_9_ns,min_ns,max_ns,total_ns,kops_per_s
jit_hotspot_cold_plan_checksum_1000,500,203614,203614,203614,203614,203614,101807113,4
jit_hotspot_ready_plan_checksum_2000,500,237598,237598,237598,237598,237598,118799288,4
jit_hotspot_invalidated_plan_checksum_2000,500,278845,278845,278845,278845,278845,139422930,3
jit_hotspot_specialized_decision_checksum_21000,500,292779,292779,292779,292779,292779,146389752,3
jit_hotspot_cranelift_medium_optimization_plan_checksum_18000,500,27446571,27446571,27446571,27446571,27446571,13723285649,0
jit_hotspot_llvm_high_optimization_plan_checksum_15500,500,24421016,24421016,24421016,24421016,24421016,12210508295,0
jit_hotspot_medium_budget_backend_choice_checksum_33500,500,305105,305105,305105,305105,305105,152552645,3
```

After splitting SSA transform helpers into `var_reassign_ssa.spl`, the
benchmark was rerun with `bin/simple` and remained PASS:

```text
label,iters,p50_ns,p99_ns,p99_9_ns,min_ns,max_ns,total_ns,kops_per_s
jit_hotspot_cold_plan_checksum_1000,500,208448,208448,208448,208448,208448,104224069,4
jit_hotspot_ready_plan_checksum_2000,500,222374,222374,222374,222374,222374,111187261,4
jit_hotspot_invalidated_plan_checksum_2000,500,284426,284426,284426,284426,284426,142213106,3
jit_hotspot_specialized_decision_checksum_21000,500,282714,282714,282714,282714,282714,141357231,3
jit_hotspot_cranelift_medium_optimization_plan_checksum_18000,500,26264531,26264531,26264531,26264531,26264531,13132265983,0
jit_hotspot_llvm_high_optimization_plan_checksum_15500,500,24479569,24479569,24479569,24479569,24479569,12239784845,0
jit_hotspot_medium_budget_backend_choice_checksum_33500,500,311257,311257,311257,311257,311257,155628660,3
```
