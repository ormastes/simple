# Gc Stats Specification

> Tests covering nogc_async_mut GC stats.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Stats Specification

## Scenarios

### nogc_async_mut GC stats

#### returns zero survival rate for empty stats

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns zero survival rate for empty stats
   - Expected: GcStats.new().survival_rate() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns zero survival rate for empty stats")
expect(GcStats.new().survival_rate()).to_equal(0.0)
```

</details>

#### guards freed count above allocated count

- guards freed count above allocated count
   - Expected: stats.survival_rate() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("guards freed count above allocated count")
val stats = GcStats(
    collections: 0,
    objects_allocated: 1,
    objects_freed: 2,
    bytes_allocated: 0,
    bytes_freed: 0,
    young_collections: 0,
    full_collections: 0,
    total_pause_time: 0,
    last_pause_time: 0
)
expect(stats.survival_rate()).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gc_stats_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut GC stats.
- nogc_async_mut GC stats

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `59adb67278266b4592ed20d8e30d228ab4f666ad4429679e011870ac45054cbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59adb67278266b4592ed20d8e30d228ab4f666ad4429679e011870ac45054cbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59adb67278266b4592ed20d8e30d228ab4f666ad4429679e011870ac45054cbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_async_mut/gc_stats_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gc_stats_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gc_stats_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gc_stats_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gc_stats_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/gc_stats_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero survival rate for empty stats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gc_stats_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards freed count above allocated count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
