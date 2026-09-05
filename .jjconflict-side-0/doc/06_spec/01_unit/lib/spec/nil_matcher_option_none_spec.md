# Nil Matcher Option None Specification

> Tests covering assert_nil accepts both nil representations, assert_nil stays strict about non-nil values, assert_not_nil is the exact mirror of assert_nil, nil-vs-nil comparison yields a strict boolean, not nil, the matcher never coerces nil to a boolean, a failed assertion does not hide later examples in the file.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nil Matcher Option None Specification

## Scenarios

### assert_nil accepts both nil representations

#### accepts the bare nil literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts the bare nil literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the bare nil literal")
assert_nil(bare_nil())
```

</details>

#### accepts a typed Option::None

- accepts a typed Option::None


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a typed Option::None")
assert_nil(none_i64())
```

</details>

#### agrees with == nil on Option::None

- agrees with == nil on Option::None


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with == nil on Option::None")
val v = none_i64()
assert_true(v == nil)
```

</details>

#### agrees with expect(...).to_be_nil() on Option::None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with expect(...).to_be_nil() on Option::None")
expect(none_i64()).to_be_nil()
```

</details>

### assert_nil stays strict about non-nil values

#### does not treat Some(_) as nil

- does not treat Some(_) as nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat Some(_) as nil")
assert_true(some_i64() != nil)
```

</details>

#### does not treat zero as nil

- does not treat zero as nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat zero as nil")
assert_true(0 != nil)
```

</details>

#### does not treat false as nil

- does not treat false as nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat false as nil")
assert_true(false != nil)
```

</details>

#### does not treat the empty string as nil

- does not treat the empty string as nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat the empty string as nil")
assert_true("" != nil)
```

</details>

### assert_not_nil is the exact mirror of assert_nil

#### accepts a present Some(_)

- accepts a present Some(_)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a present Some(_)")
assert_not_nil(some_i64())
```

</details>

#### accepts zero (zero is present, not absent)

- accepts zero (zero is present, not absent)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts zero (zero is present, not absent)")
assert_not_nil(0)
```

</details>

#### accepts the empty string

- accepts the empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the empty string")
assert_not_nil("")
```

</details>

### nil-vs-nil comparison yields a strict boolean, not nil

#### Option::None != nil is boolean false

- Option::None != nil is boolean false
   - Expected: v != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option::None != nil is boolean false")
val v = none_i64()
expect(v != nil).to_equal(false)
```

</details>

#### Option::None == nil is boolean true

- Option::None == nil is boolean true
   - Expected: v == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option::None == nil is boolean true")
val v = none_i64()
expect(v == nil).to_equal(true)
```

</details>

#### the bare nil literal != nil is boolean false

- the bare nil literal != nil is boolean false
   - Expected: v != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the bare nil literal != nil is boolean false")
val v = bare_nil()
expect(v != nil).to_equal(false)
```

</details>

#### Some(_) != nil is boolean true (the passing sibling case)

- Some(_) != nil is boolean true (the passing sibling case)
   - Expected: v != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Some(_) != nil is boolean true (the passing sibling case)")
val v = some_i64()
expect(v != nil).to_equal(true)
```

</details>

### the matcher never coerces nil to a boolean

#### Option::None is not equal to false

- Option::None is not equal to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option::None is not equal to false")
expect(none_i64()).to_not_equal(false)
```

</details>

#### Option::None is not equal to true

- Option::None is not equal to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option::None is not equal to true")
expect(none_i64()).to_not_equal(true)
```

</details>

#### Option::None is not equal to zero

- Option::None is not equal to zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Option::None is not equal to zero")
expect(none_i64()).to_not_equal(0)
```

</details>

#### false is not equal to zero

- false is not equal to zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false is not equal to zero")
expect(false).to_not_equal(0)
```

</details>

### a failed assertion does not hide later examples in the file

#### later example 1 is still observed

- later example 1 is still observed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("later example 1 is still observed")
assert_equal(1, 1)
```

</details>

#### later example 2 is still observed

- later example 2 is still observed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("later example 2 is still observed")
assert_equal(2, 2)
```

</details>

#### later example 3 is still observed

- later example 3 is still observed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("later example 3 is still observed")
assert_equal(3, 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/spec/nil_matcher_option_none_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering assert_nil accepts both nil representations, assert_nil stays strict about non-nil values, assert_not_nil is the exact mirror of assert_nil, nil-vs-nil comparison yields a strict boolean, not nil, the matcher never coerces nil to a boolean, a failed assertion does not hide later examples in the file.
- assert_nil accepts both nil representations
- assert_nil stays strict about non-nil values
- assert_not_nil is the exact mirror of assert_nil
- nil-vs-nil comparison yields a strict boolean, not nil
- the matcher never coerces nil to a boolean
- a failed assertion does not hide later examples in the file

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `5527ec6e171f739e27eb90bd40f2c1319f87582a87006d48d8100e6209428d0b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5527ec6e171f739e27eb90bd40f2c1319f87582a87006d48d8100e6209428d0b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5527ec6e171f739e27eb90bd40f2c1319f87582a87006d48d8100e6209428d0b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/spec/nil_matcher_option_none_spec.spl
mirror: doc/06_spec/01_unit/lib/spec/nil_matcher_option_none_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/spec/nil_matcher_option_none_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/spec/nil_matcher_option_none_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/spec/nil_matcher_option_none_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the bare nil literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/spec/nil_matcher_option_none_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a typed Option::None' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/spec/nil_matcher_option_none_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with == nil on Option::None' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
