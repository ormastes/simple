# Concurrent Thread Lifecycle Specification

> Tests covering nogc sync thread lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrent Thread Lifecycle Specification

## Scenarios

### nogc sync thread lifecycle

#### treats repeated terminal cleanup as safe no-ops

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats repeated terminal cleanup as safe no-ops
- Spawn and join a public OS thread
   - Expected: handle.join() equals `29`
- Verify the consumed handle stays terminal
   - Expected: handle.join() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats repeated terminal cleanup as safe no-ops")
step("Spawn and join a public OS thread")
val handle = thread_spawn(\: 29)
expect(handle.join()).to_equal(29)

step("Verify the consumed handle stays terminal")
expect(handle.is_done()).to_be(true)
# `ThreadHandle.join()` is declared `-> i64`, so a consumed handle can
# never answer nil; the terminal no-op value is 0.
expect(handle.join()).to_equal(0)
handle.free()
handle.free()
expect(handle.is_done()).to_be(true)
```

</details>

#### treats free-before-join terminal cleanup as a safe no-op

- treats free-before-join terminal cleanup as a safe no-op
- Spawn and free a public OS thread handle before join
- Verify the freed handle stays terminal
   - Expected: handle.join() equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats free-before-join terminal cleanup as a safe no-op")
step("Spawn and free a public OS thread handle before join")
val handle = thread_spawn(\: 41)
handle.free()

step("Verify the freed handle stays terminal")
expect(handle.is_done()).to_be(true)
expect(handle.join()).to_equal(41)
handle.free()
handle.free()
expect(handle.is_done()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc sync thread lifecycle.
- nogc sync thread lifecycle

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

- Canonical SPipe generation for source `bf38c58712919beeea153a6b17385e992b2e4698517f86e6a8e7875835f6adc5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf38c58712919beeea153a6b17385e992b2e4698517f86e6a8e7875835f6adc5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf38c58712919beeea153a6b17385e992b2e4698517f86e6a8e7875835f6adc5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats repeated terminal cleanup as safe no-ops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats free-before-join terminal cleanup as a safe no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
