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
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lock and unlock on address 0 complete without error")
val addr: u32 = 0
fsync_mutex_lock(addr)
fsync_mutex_unlock(addr)
expect(1).to_equal(1)
```

</details>

#### lock and unlock on non-zero address complete without error

- lock and unlock on non-zero address complete without error
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lock and unlock on non-zero address complete without error")
val addr: u32 = 42
fsync_mutex_lock(addr)
fsync_mutex_unlock(addr)
expect(1).to_equal(1)
```

</details>

#### multiple lock/unlock pairs on different addresses do not interfere

- multiple lock/unlock pairs on different addresses do not interfere
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("multiple lock/unlock pairs on different addresses do not interfere")
val a: u32 = 1
val b: u32 = 2
fsync_mutex_lock(a)
fsync_mutex_lock(b)
fsync_mutex_unlock(b)
fsync_mutex_unlock(a)
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl` |
| Updated | 2026-08-26 |
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
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `90d32b54832750702dee82fceee7cb1935d9c275854f3553d4743e51a3eb610e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90d32b54832750702dee82fceee7cb1935d9c275854f3553d4743e51a3eb610e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90d32b54832750702dee82fceee7cb1935d9c275854f3553d4743e51a3eb610e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **66/100**; effective score: **49/100**; blockers: **3**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/fsync/fsync_spec.md (current)
findings: 9 blockers: 3
  narrative=100 structure=100 oracle=0
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=66; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_async_mut/fsync/fsync_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/fsync/fsync_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lock and unlock on address 0 complete without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lock and unlock on non-zero address complete without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple lock/unlock pairs on different addresses do not interfere' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
