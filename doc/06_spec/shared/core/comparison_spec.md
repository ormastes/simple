# Comparison Specification

> Tests covering Comparisons, equality, less than, greater than, less than or equal, greater than or equal, logical operators.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comparison Specification

## Scenarios

### Comparisons

### equality

#### equal values are equal

- equal values are equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("equal values are equal")
expect 5 == 5
```

</details>

#### unequal values are not equal

- unequal values are not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("unequal values are not equal")
expect 5 != 6
```

</details>

### less than

#### smaller is less

- smaller is less


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("smaller is less")
expect 3 < 5
```

</details>

#### equal is not less

- equal is not less


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("equal is not less")
expect (not (5 < 5))
```

</details>

### greater than

#### larger is greater

- larger is greater


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("larger is greater")
expect 5 > 3
```

</details>

#### equal is not greater

- equal is not greater


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("equal is not greater")
expect (not (5 > 5))
```

</details>

### less than or equal

#### smaller is less or equal

- smaller is less or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("smaller is less or equal")
expect 3 <= 5
```

</details>

#### equal is less or equal

- equal is less or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("equal is less or equal")
expect 5 <= 5
```

</details>

### greater than or equal

#### larger is greater or equal

- larger is greater or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("larger is greater or equal")
expect 5 >= 3
```

</details>

#### equal is greater or equal

- equal is greater or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("equal is greater or equal")
expect 5 >= 5
```

</details>

### logical operators

#### and requires both

- and requires both


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("and requires both")
expect (true and true)
```

</details>

#### and fails if one false

- and fails if one false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("and fails if one false")
expect (not (true and false))
```

</details>

#### or requires one

- or requires one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("or requires one")
expect (true or false)
```

</details>

#### or fails if both false

- or fails if both false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("or fails if both false")
expect (not (false or false))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/core/comparison_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Comparisons, equality, less than, greater than, less than or equal, greater than or equal, logical operators.
- Comparisons
- equality
- less than
- greater than
- less than or equal
- greater than or equal
- logical operators

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SHARED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9219646e326b0859c4ce12cdb05799a0313b7becd35aa11148d113ebd3147a1c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9219646e326b0859c4ce12cdb05799a0313b7becd35aa11148d113ebd3147a1c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9219646e326b0859c4ce12cdb05799a0313b7becd35aa11148d113ebd3147a1c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/shared/core/comparison_spec.spl
mirror: doc/06_spec/shared/core/comparison_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/core/comparison_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/core/comparison_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/core/comparison_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'equal values are equal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/core/comparison_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unequal values are not equal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/core/comparison_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'smaller is less' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
