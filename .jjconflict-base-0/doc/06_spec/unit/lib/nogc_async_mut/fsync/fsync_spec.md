# Fsync Specification

> Tests covering fsync mutex/condvar.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fsync Specification

## Scenarios

### fsync mutex/condvar

#### lock and unlock on address 0 complete without error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lock and unlock on address 0 complete without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lock and unlock on address 0 complete without error")
val addr: u32 = 0
fsync_mutex_lock(addr)
fsync_mutex_unlock(addr)
assert_equal(1, 1)
```

</details>

#### lock and unlock on non-zero address complete without error

- lock and unlock on non-zero address complete without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lock and unlock on non-zero address complete without error")
val addr: u32 = 42
fsync_mutex_lock(addr)
fsync_mutex_unlock(addr)
assert_equal(1, 1)
```

</details>

#### multiple lock/unlock pairs on different addresses do not interfere

- multiple lock/unlock pairs on different addresses do not interfere


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple lock/unlock pairs on different addresses do not interfere")
val a: u32 = 1
val b: u32 = 2
fsync_mutex_lock(a)
fsync_mutex_lock(b)
fsync_mutex_unlock(b)
fsync_mutex_unlock(a)
assert_equal(1, 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/fsync/fsync_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering fsync mutex/condvar.
- fsync mutex/condvar

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `48896e8ddcb2ba617b861055ff063ef7514df5add67c1767c291381f92543228`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48896e8ddcb2ba617b861055ff063ef7514df5add67c1767c291381f92543228`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48896e8ddcb2ba617b861055ff063ef7514df5add67c1767c291381f92543228`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/nogc_async_mut/fsync/fsync_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/fsync/fsync_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/fsync/fsync_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/fsync/fsync_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/fsync/fsync_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/lib/nogc_async_mut/fsync/fsync_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lock and unlock on address 0 complete without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/fsync/fsync_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lock and unlock on non-zero address complete without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/fsync/fsync_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple lock/unlock pairs on different addresses do not interfere' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
