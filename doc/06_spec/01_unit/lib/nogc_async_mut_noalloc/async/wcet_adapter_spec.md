# Wcet Adapter Specification

> Tests covering ObservedMaxTracker observed-maximum measurement (WP-18).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wcet Adapter Specification

## Scenarios

### ObservedMaxTracker observed-maximum measurement (WP-18)

#### reports the maximum elapsed ticks across three runs of known, controlled duration

- reports the maximum elapsed ticks across three runs of known, controlled duration
   - Expected: r1 equals `3`
   - Expected: r2 equals `6`
   - Expected: r3 equals `2`
   - Expected: tracker.sample_count() equals `3`
   - Expected: tracker.observed_max_ticks() equals `6`
   - Expected: tracker.observed_min_ticks() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the maximum elapsed ticks across three runs of known, controlled duration")
val tracker = ObservedMaxTracker.new()

# Run 1: 2 extra timer_now() calls inside the closure -> 3 elapsed
# ticks (N + 1, see file header).
val r1 = tracker.record_run(fn():
    timer_now()
    timer_now()
)
expect(r1).to_equal(3)

# Run 2: 5 extra timer_now() calls -> 6 elapsed ticks (the max).
val r2 = tracker.record_run(fn():
    timer_now()
    timer_now()
    timer_now()
    timer_now()
    timer_now()
)
expect(r2).to_equal(6)

# Run 3: 1 extra timer_now() call -> 2 elapsed ticks (the min).
val r3 = tracker.record_run(fn():
    timer_now()
)
expect(r3).to_equal(2)

expect(tracker.sample_count()).to_equal(3)
expect(tracker.observed_max_ticks()).to_equal(6)
expect(tracker.observed_min_ticks()).to_equal(2)
```

</details>

#### reports 0 for an empty tracker (no data, not a zero-duration claim)

- reports 0 for an empty tracker (no data, not a zero-duration claim)
   - Expected: tracker.sample_count() equals `0`
   - Expected: tracker.observed_max_ticks() equals `0`
   - Expected: tracker.observed_min_ticks() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports 0 for an empty tracker (no data, not a zero-duration claim)")
val tracker = ObservedMaxTracker.new()
expect(tracker.sample_count()).to_equal(0)
expect(tracker.observed_max_ticks()).to_equal(0)
expect(tracker.observed_min_ticks()).to_equal(0)
```

</details>

#### accepts pre-measured samples directly via record_sample

- accepts pre-measured samples directly via record_sample
   - Expected: tracker.sample_count() equals `3`
   - Expected: tracker.observed_max_ticks() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts pre-measured samples directly via record_sample")
val tracker = ObservedMaxTracker.new()
tracker.record_sample(10)
tracker.record_sample(42)
tracker.record_sample(7)
expect(tracker.sample_count()).to_equal(3)
expect(tracker.observed_max_ticks()).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ObservedMaxTracker observed-maximum measurement (WP-18).
- ObservedMaxTracker observed-maximum measurement (WP-18)

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `62e50fcacec34fbb1c1be6a6c98ead7c92cf31f38cbc050c5054341a5cfc143c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62e50fcacec34fbb1c1be6a6c98ead7c92cf31f38cbc050c5054341a5cfc143c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62e50fcacec34fbb1c1be6a6c98ead7c92cf31f38cbc050c5054341a5cfc143c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the maximum elapsed ticks across three runs of known, controlled duration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports 0 for an empty tracker (no data, not a zero-duration claim)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts pre-measured samples directly via record_sample' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
