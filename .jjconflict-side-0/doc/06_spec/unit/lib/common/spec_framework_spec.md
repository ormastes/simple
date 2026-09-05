# Spec Framework Specification

> Tests covering SPipe Framework.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spec Framework Specification

## Scenarios

### SPipe Framework

#### describe and context nesting

#### runs basic test

- runs basic test
   - Expected: 1 + 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs basic test")
expect(1 + 1).to_equal(2)
```

</details>

#### supports nested context

- supports nested context
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports nested context")
expect(true).to_equal(true)
```

</details>

#### expect() matchers

#### to_equal checks equality

- to_equal checks equality
   - Expected: 42 equals `42`
   - Expected: "hello" equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_equal checks equality")
expect(42).to_equal(42)
expect("hello").to_equal("hello")
```

</details>

#### to_be is alias for to_equal

- to_be is alias for to_equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_be is alias for to_equal")
expect(10).to_be(10)
```

</details>

#### to_equal true checks boolean true

- to_equal true checks boolean true
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_equal true checks boolean true")
expect(true).to_equal(true)
```

</details>

#### to_equal false checks boolean false

- to_equal false checks boolean false
   - Expected: false is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_equal false checks boolean false")
expect(false).to_equal(false)
```

</details>

#### to_be_nil checks nil

- to_be_nil checks nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_be_nil checks nil")
expect(nil).to_be_nil()
```

</details>

#### to_contain checks string membership

- to_contain checks string membership


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_contain checks string membership")
expect("hello world").to_contain("world")
```

</details>

#### to_contain checks array membership

- to_contain checks array membership


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_contain checks array membership")
expect([1, 2, 3]).to_contain(2)
```

</details>

#### to_start_with checks prefix

- to_start_with checks prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_start_with checks prefix")
expect("hello").to_start_with("hel")
```

</details>

#### to_end_with checks suffix

- to_end_with checks suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_end_with checks suffix")
expect("hello").to_end_with("llo")
```

</details>

#### to_be_greater_than compares

- to_be_greater_than compares


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_be_greater_than compares")
expect(10).to_be_greater_than(5)
```

</details>

#### to_be_less_than compares

- to_be_less_than compares


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_be_less_than compares")
expect(5).to_be_less_than(10)
```

</details>

#### value comparisons

#### equality with strings

- equality with strings
   - Expected: "abc" equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equality with strings")
expect("abc").to_equal("abc")
```

</details>

#### equality with arrays

- equality with arrays
   - Expected: [1, 2] equals `[1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equality with arrays")
expect([1, 2]).to_equal([1, 2])
```

</details>

#### nil equality

- nil equality
   - Expected: nil equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil equality")
expect(nil).to_be_nil()
expect(nil).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/spec_framework_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe Framework.
- SPipe Framework

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

- Canonical SPipe generation for source `9fd995e62e47dd2d3c854a1c6c5149128ebd7376c9540c877e14e3252648eedc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fd995e62e47dd2d3c854a1c6c5149128ebd7376c9540c877e14e3252648eedc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fd995e62e47dd2d3c854a1c6c5149128ebd7376c9540c877e14e3252648eedc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/spec_framework_spec.spl
mirror: doc/06_spec/unit/lib/common/spec_framework_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/spec_framework_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/spec_framework_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/spec_framework_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/spec_framework_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs basic test' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/spec_framework_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports nested context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/spec_framework_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'to_equal checks equality' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
