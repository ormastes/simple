# Newtype Auto-Derived Operators Specification

> Purpose: Prove that newtype i64 operators.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Newtype Auto-Derived Operators Specification

Purpose: Prove that newtype i64 operators.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-043 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/compiler/newtype_ops_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that newtype i64 operators.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### newtype i64 operators

### arithmetic

#### supports addition

- supports addition
- Verify: supports addition
   - Expected: c.value equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports addition")
step("Verify: supports addition")
# @req: REQ-COMP-NEWTYPE-I64-OPERATORS-001
val a = Width(value: 3)
val b = Width(value: 4)
val c = a + b
expect(c.value).to_equal(7)
```

</details>

#### supports subtraction

- supports subtraction
- Verify: supports subtraction
   - Expected: c.value equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports subtraction")
step("Verify: supports subtraction")
val a = Width(value: 10)
val b = Width(value: 3)
val c = a - b
expect(c.value).to_equal(7)
```

</details>

#### supports multiplication

- supports multiplication
- Verify: supports multiplication
   - Expected: c.value equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports multiplication")
step("Verify: supports multiplication")
val a = Width(value: 3)
val b = Width(value: 4)
val c = a * b
expect(c.value).to_equal(12)
```

</details>

#### supports division

- supports division
- Verify: supports division
   - Expected: c.value equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports division")
step("Verify: supports division")
val a = Width(value: 12)
val b = Width(value: 4)
val c = a / b
expect(c.value).to_equal(3)
```

</details>

### comparison

#### supports equality when equal

- supports equality when equal
- Verify: supports equality when equal
   - Expected: a equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports equality when equal")
step("Verify: supports equality when equal")
val a = Width(value: 5)
val b = Width(value: 5)
expect(a).to_equal(b)
```

</details>

#### supports equality when not equal

- supports equality when not equal
- Verify: supports equality when not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports equality when not equal")
step("Verify: supports equality when not equal")
val a = Width(value: 5)
val b = Width(value: 3)
expect(a).to_not_equal(b)
```

</details>

#### supports less than

- supports less than
- Verify: supports less than
   - Expected: a < b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports less than")
step("Verify: supports less than")
val a = Width(value: 3)
val b = Width(value: 5)
expect(a < b).to_equal(true)
```

</details>

#### supports less than when not less

- supports less than when not less
- Verify: supports less than when not less
   - Expected: a < b is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports less than when not less")
step("Verify: supports less than when not less")
val a = Width(value: 5)
val b = Width(value: 3)
expect(a < b).to_equal(false)
```

</details>

#### supports greater than

- supports greater than
- Verify: supports greater than
   - Expected: a > b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports greater than")
step("Verify: supports greater than")
val a = Width(value: 5)
val b = Width(value: 3)
expect(a > b).to_equal(true)
```

</details>

#### supports greater than when not greater

- supports greater than when not greater
- Verify: supports greater than when not greater
   - Expected: a > b is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports greater than when not greater")
step("Verify: supports greater than when not greater")
val a = Width(value: 3)
val b = Width(value: 5)
expect(a > b).to_equal(false)
```

</details>

### edge cases

#### handles zero values

- handles zero values
- Verify: handles zero values
   - Expected: c.value equals `0`
   - Expected: a equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero values")
step("Verify: handles zero values")
val a = Width(value: 0)
val b = Width(value: 0)
val c = a + b
expect(c.value).to_equal(0)
expect(a).to_equal(b)
```

</details>

#### handles negative values

- handles negative values
- Verify: handles negative values
   - Expected: c.value equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles negative values")
step("Verify: handles negative values")
val a = Width(value: -3)
val b = Width(value: 2)
val c = a + b
expect(c.value).to_equal(-1)
```

</details>

#### handles subtraction resulting in negative

- handles subtraction resulting in negative
- Verify: handles subtraction resulting in negative
   - Expected: c.value equals `-7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles subtraction resulting in negative")
step("Verify: handles subtraction resulting in negative")
val a = Width(value: 3)
val b = Width(value: 10)
val c = a - b
expect(c.value).to_equal(-7)
```

</details>

### newtype f64 operators

### arithmetic

#### supports addition

- supports addition
- Verify: supports addition
   - Expected: c.value equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports addition")
step("Verify: supports addition")
val a = Temperature(value: 1.5)
val b = Temperature(value: 2.5)
val c = a + b
expect(c.value).to_equal(4.0)
```

</details>

#### supports subtraction

- supports subtraction
- Verify: supports subtraction
   - Expected: c.value equals `7.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports subtraction")
step("Verify: supports subtraction")
val a = Temperature(value: 10.5)
val b = Temperature(value: 3.5)
val c = a - b
expect(c.value).to_equal(7.0)
```

</details>

#### supports multiplication

- supports multiplication
- Verify: supports multiplication
   - Expected: c.value equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports multiplication")
step("Verify: supports multiplication")
val a = Temperature(value: 2.5)
val b = Temperature(value: 4.0)
val c = a * b
expect(c.value).to_equal(10.0)
```

</details>

#### supports division

- supports division
- Verify: supports division
   - Expected: c.value equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports division")
step("Verify: supports division")
val a = Temperature(value: 9.0)
val b = Temperature(value: 3.0)
val c = a / b
expect(c.value).to_equal(3.0)
```

</details>

### comparison

#### supports equality

- supports equality
- Verify: supports equality
   - Expected: a equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports equality")
step("Verify: supports equality")
val a = Temperature(value: 36.6)
val b = Temperature(value: 36.6)
expect(a).to_equal(b)
```

</details>

#### supports less than

- supports less than
- Verify: supports less than
   - Expected: a < b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports less than")
step("Verify: supports less than")
val a = Temperature(value: 20.0)
val b = Temperature(value: 30.0)
expect(a < b).to_equal(true)
```

</details>

#### supports greater than

- supports greater than
- Verify: supports greater than
   - Expected: a > b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports greater than")
step("Verify: supports greater than")
val a = Temperature(value: 30.0)
val b = Temperature(value: 20.0)
expect(a > b).to_equal(true)
```

</details>

### edge cases

#### handles zero values

- handles zero values
- Verify: handles zero values
   - Expected: c.value equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero values")
step("Verify: handles zero values")
val a = Temperature(value: 0.0)
val b = Temperature(value: 0.0)
val c = a + b
expect(c.value).to_equal(0.0)
```

</details>

#### handles negative values

- handles negative values
- Verify: handles negative values
   - Expected: c.value equals `-5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles negative values")
step("Verify: handles negative values")
val a = Temperature(value: -10.5)
val b = Temperature(value: 5.5)
val c = a + b
expect(c.value).to_equal(-5.0)
```

</details>

### newtype type safety

#### Width operations produce Width

- Width operations produce Width
- Verify: Width operations produce Width
   - Expected: c.value equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Width operations produce Width")
step("Verify: Width operations produce Width")
val a = Width(value: 3)
val b = Width(value: 4)
val c = a + b
expect(c.value).to_equal(7)
```

</details>

#### Height operations produce Height

- Height operations produce Height
- Verify: Height operations produce Height
   - Expected: c.value equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Height operations produce Height")
step("Verify: Height operations produce Height")
val a = Height(value: 10)
val b = Height(value: 5)
val c = a + b
expect(c.value).to_equal(15)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-NEWTYPE-I64-OPERATORS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd18007c9f6785924c5b1e9eef0788e86fbc20457a8f514b42862384f1019e54`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd18007c9f6785924c5b1e9eef0788e86fbc20457a8f514b42862384f1019e54`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd18007c9f6785924c5b1e9eef0788e86fbc20457a8f514b42862384f1019e54`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/newtype_ops_spec.spl
mirror: doc/06_spec/unit/compiler/newtype_ops_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/newtype_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/newtype_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/newtype_ops_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/newtype_ops_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/newtype_ops_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/newtype_ops_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
