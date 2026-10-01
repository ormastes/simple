# Timing Facade Specification

> Tests covering gc_sync_mut timing facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Timing Facade Specification

## Scenarios

### gc_sync_mut timing facade

#### re-exports timing record types without depending on wall-clock assertions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports timing record types without depending on wall-clock assertions
   - Expected: start.micros equals `1000`
   - Expected: profile.elapsed_ms equals `2`
   - Expected: profile.elapsed_micros equals `2500`
   - Expected: bench.iterations equals `3`
   - Expected: bench.avg_ms equals `3.0`
   - Expected: bench.max_ms equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports timing record types without depending on wall-clock assertions")
val start = Instant(micros: 1000)
expect(start.micros).to_equal(1000)

val profile = ProfileResult(elapsed_ms: 2, elapsed_micros: 2500)
expect(profile.elapsed_ms).to_equal(2)
expect(profile.elapsed_micros).to_equal(2500)

val bench = BenchmarkResult(iterations: 3, total_ms: 9, avg_ms: 3.0, min_ms: 2, max_ms: 4)
expect(bench.iterations).to_equal(3)
expect(bench.avg_ms).to_equal(3.0)
expect(bench.max_ms).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_sync_mut/timing_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_sync_mut timing facade.
- gc_sync_mut timing facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `50ab8ee76c1d572a926df39eb4f170b86e662077362fb6bdb751be0adb063dd3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `50ab8ee76c1d572a926df39eb4f170b86e662077362fb6bdb751be0adb063dd3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `50ab8ee76c1d572a926df39eb4f170b86e662077362fb6bdb751be0adb063dd3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_sync_mut/timing_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_sync_mut/timing_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_sync_mut/timing_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_sync_mut/timing_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_sync_mut/timing_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_sync_mut/timing_facade_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports timing record types without depending on wall-clock assertions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
