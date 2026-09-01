# Builtin Min Max Abs Specification

> Tests covering builtin min/max/abs (bare-function form).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Builtin Min Max Abs Specification

## Scenarios

### builtin min/max/abs (bare-function form)

#### min returns the smaller of two ints, either order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- min returns the smaller of two ints, either order


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("min returns the smaller of two ints, either order")
assert_equal(min(3, 7), 3)
assert_equal(min(7, 3), 3)
```

</details>

#### min handles negatives and ties

- min handles negatives and ties


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("min handles negatives and ties")
assert_equal(min(-5, 5), -5)
assert_equal(min(5, 5), 5)
```

</details>

#### max returns the larger of two ints, either order

- max returns the larger of two ints, either order


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("max returns the larger of two ints, either order")
assert_equal(max(3, 7), 7)
assert_equal(max(7, 3), 7)
```

</details>

#### max handles negatives and ties

- max handles negatives and ties


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("max handles negatives and ties")
assert_equal(max(-5, 5), 5)
assert_equal(max(5, 5), 5)
```

</details>

#### abs returns the magnitude, zero and large values included

- abs returns the magnitude, zero and large values included


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abs returns the magnitude, zero and large values included")
assert_equal(abs(5), 5)
assert_equal(abs(-5), 5)
assert_equal(abs(0), 0)
assert_equal(abs(-9223372036854775807), 9223372036854775807)
```

</details>

#### matches the exact site that motivated this fix: clamping to a deadline

- matches the exact site that motivated this fix: clamping to a deadline


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the exact site that motivated this fix: clamping to a deadline")
val current_time_ms = 1000
val end_ms = 1010
assert_equal(min(current_time_ms + 16, end_ms), 1010)
val current_time_ms2 = 1000
val end_ms2 = 2000
assert_equal(min(current_time_ms2 + 16, end_ms2), 1016)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/language/builtin_min_max_abs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering builtin min/max/abs (bare-function form).
- builtin min/max/abs (bare-function form)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `8419b11c04a05356bc15ae85de0f934c459351321472cd119e31058201e187d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8419b11c04a05356bc15ae85de0f934c459351321472cd119e31058201e187d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8419b11c04a05356bc15ae85de0f934c459351321472cd119e31058201e187d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/language/builtin_min_max_abs_spec.spl
mirror: doc/06_spec/01_unit/lib/language/builtin_min_max_abs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/language/builtin_min_max_abs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/language/builtin_min_max_abs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/language/builtin_min_max_abs_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'min returns the smaller of two ints, either order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/language/builtin_min_max_abs_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'min handles negatives and ties' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/language/builtin_min_max_abs_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'max returns the larger of two ints, either order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
