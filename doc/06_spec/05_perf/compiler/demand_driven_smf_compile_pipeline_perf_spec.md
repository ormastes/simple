# Demand-Driven SMF Compile Performance

**Evidence class:** expected-red measured performance contract
**Executable source:** `test/05_perf/compiler/demand_driven_smf_compile_pipeline_perf_spec.spl`

## Manual flow

1. Pin host, compiler, fixture, Go toolchain, command, environment, and SCV identities.
2. Verify Simple and Go execute equivalent workloads before timing.
3. Collect 100 samples and retain raw timings plus p50/p95/p99/mean/standard deviation/confidence interval.
4. Record source opens, bytes read, mapped bytes, page faults, CPU counters, and peak RSS.
5. Prove warm decision `<=100 ms` with zero source opens.
6. Prove warm command `<=500 ms`, ordinary edit `<=3 s`, broad edit `<=15 s`, and clean build `<=2x` matched Go.
7. Kill the daemon between equivalent requests and prove only latency changes.
8. Evaluate parent-program gates F, S, V, A, Q, J, and R independently.

## Requirement map

- `DDSM-NFR-001`: warm unchanged package decision.
- `DDSM-NFR-002`: warm unchanged command.
- `DDSM-NFR-003`: ordinary package edit.
- `DDSM-NFR-004`: broad dependent edit.
- `DDSM-NFR-005`: matched clean Go ratio.
- `DDSM-NFR-006`: daemon-loss correctness.
- `PERF-GATE-F/S/V/A/Q/J/R`: parent compiler/interpreter performance-program admission gates.

## Current status

The production wrapper and static umbrella mapping gate exist. Performance and native rows remain expected red until `scripts/check/check-demand-driven-smf-compile-performance.shs` admits complete, non-synthetic retained evidence. Anything other than exactly 100 samples, matched semantics, retained raw samples, complete statistics, and bound provenance is a failure.
