# Lsan Facade Specification

> Tests covering gc_async_mut sanitizer lsan facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsan Facade Specification

## Scenarios

### gc_async_mut sanitizer lsan facade

#### re-exports leak sanitizer disabled-state checks and records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports leak sanitizer disabled-state checks and records
   - Expected: lsan_is_enabled() is false
   - Expected: lsan_check_since("missing") equals `0`
   - Expected: lsan_bytes_since("missing") equals `0`
   - Expected: lsan_error_count() equals `0`
   - Expected: checkpoint.name equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports leak sanitizer disabled-state checks and records")
lsan_reset()
expect(lsan_is_enabled()).to_equal(false)
expect(lsan_check_since("missing")).to_equal(0)
expect(lsan_bytes_since("missing")).to_equal(0)
expect(lsan_error_count()).to_equal(0)

val checkpoint = leak_checkpoint("before", 7)
expect(checkpoint.name).to_equal("before")
```

</details>

#### re-exports suppression tags

- re-exports suppression tags
   - Expected: lsan_is_suppressed("fixture") is false
   - Expected: lsan_is_suppressed("fixture") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports suppression tags")
lsan_reset()
expect(lsan_is_suppressed("fixture")).to_equal(false)
lsan_suppress_tag("fixture")
expect(lsan_is_suppressed("fixture")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/sanitizer/lsan/lsan_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut sanitizer lsan facade.
- gc_async_mut sanitizer lsan facade

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

- Canonical SPipe generation for source `874fcad043ce46f19325d518df747d0bf6ee728bcfbdc5161fe77bf288700310`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `874fcad043ce46f19325d518df747d0bf6ee728bcfbdc5161fe77bf288700310`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `874fcad043ce46f19325d518df747d0bf6ee728bcfbdc5161fe77bf288700310`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/gc_async_mut/sanitizer/lsan/lsan_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/sanitizer/lsan/lsan_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/sanitizer/lsan/lsan_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/sanitizer/lsan/lsan_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/sanitizer/lsan/lsan_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/sanitizer/lsan/lsan_facade_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports leak sanitizer disabled-state checks and records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/sanitizer/lsan/lsan_facade_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports suppression tags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
