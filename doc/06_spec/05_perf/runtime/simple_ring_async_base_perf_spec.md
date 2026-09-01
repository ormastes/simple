# simple_ring_async_base_perf_spec

> Measured hosted-reference performance evidence for SimpleRing V1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_ring_async_base_perf_spec

Measured hosted-reference performance evidence for SimpleRing V1.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/05_perf/runtime/simple_ring_async_base_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Measured hosted-reference performance evidence for SimpleRing V1.

This spec exercises the real SimpleRing and SoftwareRingProvider. It records
wall-clock p50/p99/p99.9 and throughput without declaring an unmeasured speed
target. It does not prove allocation behavior, RSS bounds, a native provider,
or mission qualification. A retained baseline from an admitted pure-Simple
self-hosted runtime is required before regression thresholds may be selected.

## Scenarios

### SimpleRing async base measured performance

#### records real single-cycle latency, throughput, and bounded telemetry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records real single-cycle latency, throughput, and bounded telemetry
- Measure repeated fixed-capacity ring cycles
   - Expected: metrics.operations equals `SINGLE_ITERATIONS.to_u64()`
   - Expected: metrics.high_water equals `1u64`
   - Expected: metrics.full_events equals `0u64`
   - Expected: metrics.provider_kicks equals `metrics.operations`
   - Expected: metrics.latency_samples equals `metrics.operations`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("records real single-cycle latency, throughput, and bounded telemetry")
step("Measure repeated fixed-capacity ring cycles")
val metrics = run_single_cycle_measurement()
print_measurement("single", metrics)
expect(metrics.operations).to_equal(SINGLE_ITERATIONS.to_u64())
expect(metrics.elapsed_us).to_be_greater_than(0)
expect(metrics.throughput_ops_per_second).to_be_greater_than(0)
expect(metrics.p50_us).to_be_less_than(metrics.p99_us + 1)
expect(metrics.p99_us).to_be_less_than(metrics.p99_9_us + 1)
expect(metrics.high_water).to_equal(1u64)
expect(metrics.full_events).to_equal(0u64)
expect(metrics.provider_kicks).to_equal(metrics.operations)
expect(metrics.latency_samples).to_equal(metrics.operations)
expect(metrics.checksum).to_be_greater_than(0)
```

</details>

#### records full-depth batch latency, throughput, and backpressure telemetry

- records full-depth batch latency, throughput, and backpressure telemetry
- Measure repeated all-or-nothing batch cycles
   - Expected: metrics.operations equals `(BATCH_ITERATIONS * BATCH_DEPTH).to_u64()`
   - Expected: metrics.high_water equals `BATCH_DEPTH.to_u64()`
   - Expected: metrics.full_events equals `BATCH_ITERATIONS.to_u64()`
   - Expected: metrics.batches equals `BATCH_ITERATIONS.to_u64()`
   - Expected: metrics.batch_items equals `metrics.operations`
   - Expected: metrics.provider_kicks equals `metrics.operations`
   - Expected: metrics.latency_samples equals `metrics.operations`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("records full-depth batch latency, throughput, and backpressure telemetry")
step("Measure repeated all-or-nothing batch cycles")
val metrics = run_batch_cycle_measurement()
print_measurement("batch", metrics)
expect(metrics.operations).to_equal((BATCH_ITERATIONS * BATCH_DEPTH).to_u64())
expect(metrics.elapsed_us).to_be_greater_than(0)
expect(metrics.throughput_ops_per_second).to_be_greater_than(0)
expect(metrics.p50_us).to_be_less_than(metrics.p99_us + 1)
expect(metrics.p99_us).to_be_less_than(metrics.p99_9_us + 1)
expect(metrics.high_water).to_equal(BATCH_DEPTH.to_u64())
expect(metrics.full_events).to_equal(BATCH_ITERATIONS.to_u64())
expect(metrics.batches).to_equal(BATCH_ITERATIONS.to_u64())
expect(metrics.batch_items).to_equal(metrics.operations)
expect(metrics.provider_kicks).to_equal(metrics.operations)
expect(metrics.latency_samples).to_equal(metrics.operations)
expect(metrics.checksum).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d984b1e8a3e648acacc7f8443347c130f36ed7ea79f598f16e01fdc3094a3bd0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d984b1e8a3e648acacc7f8443347c130f36ed7ea79f598f16e01fdc3094a3bd0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d984b1e8a3e648acacc7f8443347c130f36ed7ea79f598f16e01fdc3094a3bd0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/05_perf/runtime/simple_ring_async_base_perf_spec.spl
mirror: doc/06_spec/05_perf/runtime/simple_ring_async_base_perf_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/runtime/simple_ring_async_base_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/runtime/simple_ring_async_base_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/runtime/simple_ring_async_base_perf_spec.spl:215:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records real single-cycle latency, throughput, and bounded telemetry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/runtime/simple_ring_async_base_perf_spec.spl:234:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records full-depth batch latency, throughput, and backpressure telemetry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
