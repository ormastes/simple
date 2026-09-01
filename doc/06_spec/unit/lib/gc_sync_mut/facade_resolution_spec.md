# Facade Resolution Specification

> Tests covering gc_sync_mut facade resolution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Facade Resolution Specification

## Scenarios

### gc_sync_mut facade resolution

#### resolves pure helpers through the gc_async_mut backing family

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves pure helpers through the gc_async_mut backing family
   - Expected: idx equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves pure helpers through the gc_async_mut backing family")
val idx = array_position([10, 20, 30], _1 == 20)
expect(idx).to_equal(1)
```

</details>

#### preserves pure helper behavior through the sync facade

- preserves pure helper behavior through the sync facade
   - Expected: found equals `99`
   - Expected: prefix equals `[2, 4]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves pure helper behavior through the sync facade")
val found = array_find_or([1, 3, 5], _1 > 10, 99)
expect(found).to_equal(99)

val prefix = array_take_while([2, 4, 5, 6], _1 % 2 == 0)
expect(prefix).to_equal([2, 4])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_sync_mut/facade_resolution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_sync_mut facade resolution.
- gc_sync_mut facade resolution

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f9c050400cb02bd03e3d3eb75b08bd4cd335bd89fcdc838b6aadee3696890111`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f9c050400cb02bd03e3d3eb75b08bd4cd335bd89fcdc838b6aadee3696890111`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f9c050400cb02bd03e3d3eb75b08bd4cd335bd89fcdc838b6aadee3696890111`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/gc_sync_mut/facade_resolution_spec.spl
mirror: doc/06_spec/unit/lib/gc_sync_mut/facade_resolution_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_sync_mut/facade_resolution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_sync_mut/facade_resolution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_sync_mut/facade_resolution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_sync_mut/facade_resolution_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves pure helpers through the gc_async_mut backing family' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_sync_mut/facade_resolution_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves pure helper behavior through the sync facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
