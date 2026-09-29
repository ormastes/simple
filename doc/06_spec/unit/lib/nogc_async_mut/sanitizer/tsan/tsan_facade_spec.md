# Tsan Facade Specification

> Tests covering nogc_async_mut sanitizer tsan facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tsan Facade Specification

## Scenarios

### nogc_async_mut sanitizer tsan facade

#### re-exports thread sanitizer race checks and records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports thread sanitizer race checks and records
   - Expected: tsan_is_enabled() is false
   - Expected: tsan_error_count() equals `0`
   - Expected: tsan_is_enabled() is true
   - Expected: tsan_error_count() equals `1`
   - Expected: tsan_get_events()[0].kind equals `tsan`
   - Expected: race.var_id equals `counter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports thread sanitizer race checks and records")
tsan_reset()
expect(tsan_is_enabled()).to_equal(false)
tsan_set_thread(1)
tsan_write("counter", "disabled")
expect(tsan_error_count()).to_equal(0)

tsan_enable()
expect(tsan_is_enabled()).to_equal(true)
tsan_write("counter", "main.spl:10")
tsan_set_thread(2)
tsan_read("counter", "worker.spl:20")
expect(tsan_error_count()).to_equal(1)
expect(tsan_get_events()[0].kind).to_equal("tsan")

val race = data_race("counter", 1, 2, "worker.spl:20")
expect(race.var_id).to_equal("counter")
```

</details>

#### re-exports lock order checks

- re-exports lock order checks
   - Expected: tsan_error_count() equals `1`
   - Expected: tsan_get_events()[0].kind equals `tsan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports lock order checks")
tsan_reset()
tsan_enable()
tsan_set_thread(1)
tsan_lock_acquire("a")
tsan_lock_acquire("b")
tsan_set_thread(2)
tsan_lock_acquire("b")
tsan_lock_acquire("a")
expect(tsan_error_count()).to_equal(1)
expect(tsan_get_events()[0].kind).to_equal("tsan")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/sanitizer/tsan/tsan_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut sanitizer tsan facade.
- nogc_async_mut sanitizer tsan facade

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

- Canonical SPipe generation for source `14ca6abfa31dba76c5e5464eb9f671091cd89b14093e0d75a07099af402ec26b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14ca6abfa31dba76c5e5464eb9f671091cd89b14093e0d75a07099af402ec26b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14ca6abfa31dba76c5e5464eb9f671091cd89b14093e0d75a07099af402ec26b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/sanitizer/tsan/tsan_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/sanitizer/tsan/tsan_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/sanitizer/tsan/tsan_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/sanitizer/tsan/tsan_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/sanitizer/tsan/tsan_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/sanitizer/tsan/tsan_facade_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports thread sanitizer race checks and records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/sanitizer/tsan/tsan_facade_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports lock order checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
