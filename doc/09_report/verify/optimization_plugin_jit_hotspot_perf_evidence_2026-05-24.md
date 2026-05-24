# Optimization Plugin JIT Hotspot Performance Evidence

Date: 2026-05-24

## Scope

This report records the first representative benchmark for the JIT hotspot
planning boundary. It measures pure Simple plan construction, runtime fact
extraction, eligibility checks, and invalidation bookkeeping. It does not measure
native JIT code emission or claim end-to-end program speedup.

## Command

```bash
bin/simple run test/perf/compiler/jit_hotspot_plan_bench.spl --mode=interpreter
```

## Result

Status: PASS

```text
label,iters,p50_ns,p99_ns,p99_9_ns,min_ns,max_ns,total_ns,kops_per_s
jit_hotspot_cold_plan_checksum_100000,50000,59013,59013,59013,59013,59013,2950653776,16
jit_hotspot_ready_plan_checksum_200000,50000,62554,62554,62554,62554,62554,3127737425,15
jit_hotspot_invalidated_plan_checksum_200000,50000,81131,81131,81131,81131,81131,4056599026,12
```

## Interpretation

The benchmark proves that hotspot planning has a runnable measurement harness and
stable checksums for cold, ready, and invalidated plans. The numbers are
interpreter-mode planning costs only; native runtime specialization still needs a
separate benchmark after `JitHotspotPlan` is consumed by an execution backend.
