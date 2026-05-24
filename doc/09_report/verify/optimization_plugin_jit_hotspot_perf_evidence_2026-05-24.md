# Optimization Plugin JIT Hotspot Performance Evidence

Date: 2026-05-24

## Scope

This report records the first representative benchmark for the JIT hotspot
planning boundary. It measures pure Simple plan construction, runtime fact
extraction, eligibility checks, invalidation bookkeeping, and specialization
provider compile-decision overhead. It does not measure native JIT code emission
or claim end-to-end program speedup.

## Command

```bash
bin/simple run test/perf/compiler/jit_hotspot_plan_bench.spl --mode=interpreter
```

## Result

Status: PASS

```text
label,iters,p50_ns,p99_ns,p99_9_ns,min_ns,max_ns,total_ns,kops_per_s
jit_hotspot_cold_plan_checksum_100000,50000,55631,55631,55631,55631,55631,2781570688,17
jit_hotspot_ready_plan_checksum_200000,50000,60469,60469,60469,60469,60469,3023457507,16
jit_hotspot_invalidated_plan_checksum_200000,50000,76241,76241,76241,76241,76241,3812093451,13
jit_hotspot_specialized_decision_checksum_2100000,50000,77698,77698,77698,77698,77698,3884946714,12
```

## Interpretation

The benchmark proves that hotspot planning has a runnable measurement harness and
stable checksums for cold, ready, invalidated, and specialization-provider
decision paths. The numbers are interpreter-mode planning costs only; native code
emission and end-to-end runtime speedup require separate backend benchmarks.
