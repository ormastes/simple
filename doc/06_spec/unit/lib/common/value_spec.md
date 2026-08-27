# Value Specification

> Tests covering SDN Value.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Value Specification

## Scenarios

### SDN Value

#### type checking

#### identifies null values

- identifies null values
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies null values")
val result = parse("v: null")
expect(result).to_equal(nil)
```

</details>

#### identifies boolean values

- identifies boolean values
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies boolean values")
val result = parse("v: true")
expect(result).to_equal(nil)
```

</details>

#### identifies integer values

- identifies integer values
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies integer values")
val result = parse("v: 42")
expect(result).to_equal(nil)
```

</details>

#### identifies float values

- identifies float values
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies float values")
val result = parse("v: 3.14")
expect(result).to_equal(nil)
```

</details>

#### identifies string values

- identifies string values
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies string values")
val result = parse("v: hello")
expect(result).to_equal(nil)
```

</details>

#### identifies dict values

- identifies dict values
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies dict values")
val result = parse("v:\n    a: 1")
expect(result).to_equal(nil)
```

</details>

#### identifies array values

- identifies array values
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies array values")
val result = parse("v = [1, 2, 3]")
expect(result).to_equal(nil)
```

</details>

#### type conversions

#### converts to bool

- converts to bool
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to bool")
val result = parse("v: true")
expect(result).to_equal(nil)
```

</details>

#### converts to i64

- converts to i64
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to i64")
val result = parse("v: 42")
expect(result).to_equal(nil)
```

</details>

#### converts to f64

- converts to f64
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to f64")
val result = parse("v: 3.14")
expect(result).to_equal(nil)
```

</details>

#### converts to string

- converts to string
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to string")
val result = parse("v: hello")
expect(result).to_equal(nil)
```

</details>

#### returns None for invalid conversions

- returns None for invalid conversions
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for invalid conversions")
val result = parse("v: null")
expect(result).to_equal(nil)
```

</details>

#### value methods

#### checks null value

- checks null value
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks null value")
val result = parse("v: null")
expect(result).to_equal(nil)
```

</details>

#### gets bool value

- gets bool value
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets bool value")
val result = parse("v: false")
expect(result).to_equal(nil)
```

</details>

#### gets int value

- gets int value
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets int value")
val result = parse("v: 100")
expect(result).to_equal(nil)
```

</details>

#### gets string value

- gets string value
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets string value")
val result = parse("v: test")
expect(result).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/value_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDN Value.
- SDN Value

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `a79a9527f7f86c888ae45bdeebb72c9b1b0f8b217678ac856c00753a53921edd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a79a9527f7f86c888ae45bdeebb72c9b1b0f8b217678ac856c00753a53921edd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a79a9527f7f86c888ae45bdeebb72c9b1b0f8b217678ac856c00753a53921edd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/value_spec.spl
mirror: doc/06_spec/unit/lib/common/value_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/value_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/value_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/value_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies null values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/value_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies boolean values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/value_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies integer values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
