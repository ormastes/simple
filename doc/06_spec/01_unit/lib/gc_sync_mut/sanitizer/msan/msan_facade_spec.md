# Msan Facade Specification

> Tests covering gc_sync_mut sanitizer msan facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Msan Facade Specification

## Scenarios

### gc_sync_mut sanitizer msan facade

#### re-exports memory sanitizer state checks and records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports memory sanitizer state checks and records
   - Expected: msan_is_enabled() is false
   - Expected: package_msan_is_enabled() is false
   - Expected: msan_check_init("buffer") is true
   - Expected: msan_is_enabled() is true
   - Expected: msan_check_init("buffer") is false
   - Expected: msan_check_init("buffer") is true
   - Expected: msan_check_not_freed("buffer") is false
   - Expected: msan_error_count() equals `2`
   - Expected: msan_get_events()[0].kind equals `msan`
   - Expected: region.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports memory sanitizer state checks and records")
msan_reset()
expect(msan_is_enabled()).to_equal(false)
expect(package_msan_is_enabled()).to_equal(false)
expect(msan_check_init("buffer")).to_equal(true)

msan_enable()
expect(msan_is_enabled()).to_equal(true)
msan_alloc_uninit("buffer", 64)
expect(msan_check_init("buffer")).to_equal(false)
msan_init("buffer")
expect(msan_check_init("buffer")).to_equal(true)
msan_free_region("buffer")
expect(msan_check_not_freed("buffer")).to_equal(false)
expect(msan_error_count()).to_equal(2)
expect(msan_get_events()[0].kind).to_equal("msan")

val region = mem_region("buffer", 64)
expect(region.initialized).to_equal(false)
```

</details>

#### re-exports overlap checks

- re-exports overlap checks
   - Expected: msan_check_overlap("buffer", 0, "buffer", 8, 16) is false
   - Expected: msan_check_overlap("left", 0, "right", 8, 16) is true
   - Expected: msan_error_count() equals `1`
   - Expected: msan_get_events()[0].kind equals `msan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports overlap checks")
msan_reset()
msan_enable()
msan_alloc_init("buffer", 64)
expect(msan_check_overlap("buffer", 0, "buffer", 8, 16)).to_equal(false)
expect(msan_check_overlap("left", 0, "right", 8, 16)).to_equal(true)
expect(msan_error_count()).to_equal(1)
expect(msan_get_events()[0].kind).to_equal("msan")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_sync_mut/sanitizer/msan/msan_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_sync_mut sanitizer msan facade.
- gc_sync_mut sanitizer msan facade

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

- Canonical SPipe generation for source `0e6d2b2da630fafc718bc7a2754dca299dabd69b6eef7fbac5b88f31c4ff2a22`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e6d2b2da630fafc718bc7a2754dca299dabd69b6eef7fbac5b88f31c4ff2a22`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e6d2b2da630fafc718bc7a2754dca299dabd69b6eef7fbac5b88f31c4ff2a22`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_sync_mut/sanitizer/msan/msan_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_sync_mut/sanitizer/msan/msan_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_sync_mut/sanitizer/msan/msan_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_sync_mut/sanitizer/msan/msan_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_sync_mut/sanitizer/msan/msan_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_sync_mut/sanitizer/msan/msan_facade_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports memory sanitizer state checks and records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_sync_mut/sanitizer/msan/msan_facade_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports overlap checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
