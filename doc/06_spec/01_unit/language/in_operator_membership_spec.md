# In Operator Membership Specification

> Tests covering in operator membership, not in operator membership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# In Operator Membership Specification

## Scenarios

### in operator membership

#### finds an i64 element at the first position

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds an i64 element at the first position


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds an i64 element at the first position")
val a: [i64] = [10, 20, 30]
assert_true(10 in a)
```

</details>

#### finds an i64 element in the middle

- finds an i64 element in the middle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds an i64 element in the middle")
val a: [i64] = [10, 20, 30]
assert_true(20 in a)
```

</details>

#### finds an i64 element at the last position

- finds an i64 element at the last position


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds an i64 element at the last position")
val a: [i64] = [10, 20, 30]
assert_true(30 in a)
```

</details>

#### rejects an absent i64 element

- rejects an absent i64 element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an absent i64 element")
val a: [i64] = [10, 20, 30]
assert_false(99 in a)
```

</details>

#### finds an i64 element held in a variable

- finds an i64 element held in a variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds an i64 element held in a variable")
val a: [i64] = [10, 20, 30]
val needle = 20
assert_true(needle in a)
```

</details>

#### agrees with contains on i64 presence

- agrees with contains on i64 presence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with contains on i64 presence")
val a: [i64] = [10, 20, 30]
assert_equal(20 in a, a.contains(20))
assert_equal(99 in a, a.contains(99))
```

</details>

#### finds a zero element, which a shifted-tag compare matches by accident

- finds a zero element, which a shifted-tag compare matches by accident


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a zero element, which a shifted-tag compare matches by accident")
val z: [i64] = [0, 0, 0]
assert_true(0 in z)
```

</details>

#### finds an f64 element

- finds an f64 element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds an f64 element")
val f: [f64] = [1.5, 2.5]
assert_true(2.5 in f)
assert_false(9.5 in f)
```

</details>

#### finds a bool element

- finds a bool element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a bool element")
val b: [bool] = [true, false]
assert_true(true in b)
```

</details>

#### finds a text element by value, not identity

- finds a text element by value, not identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a text element by value, not identity")
val t: [text] = ["alpha", "beta"]
val needle = "be" + "ta"
assert_true(needle in t)
assert_false("gamma" in t)
```

</details>

#### finds an i64 dict key

- finds an i64 dict key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds an i64 dict key")
val d = {1: 10, 2: 20}
assert_true(1 in d)
assert_false(7 in d)
```

</details>

#### finds a text dict key built at runtime

- finds a text dict key built at runtime


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a text dict key built at runtime")
val d = {"k1": 10, "k2": 20}
val k = "k" + "1"
assert_true(k in d)
assert_false("zz" in d)
```

</details>

#### finds a substring in text

- finds a substring in text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a substring in text")
val hay = "hello world"
assert_true("world" in hay)
assert_false("zzz" in hay)
```

</details>

#### finds a substring when both sides are built at runtime

- finds a substring when both sides are built at runtime


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a substring when both sides are built at runtime")
val hay = "hello" + " world"
val needle = "wor" + "ld"
assert_true(needle in hay)
```

</details>

### not in operator membership

#### is true for an absent text needle

- is true for an absent text needle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is true for an absent text needle")
val hay = "hello world"
assert_true("zzz" not in hay)
```

</details>

#### is false for a present text needle

- is false for a present text needle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is false for a present text needle")
val hay = "hello world"
assert_false("world" not in hay)
```

</details>

#### is true for an absent i64 element

- is true for an absent i64 element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is true for an absent i64 element")
val a: [i64] = [10, 20, 30]
assert_true(99 not in a)
```

</details>

#### is false for a present i64 element

- is false for a present i64 element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is false for a present i64 element")
val a: [i64] = [10, 20, 30]
assert_false(20 not in a)
```

</details>

#### renders as a bool, not as a decoded heap handle

- renders as a bool, not as a decoded heap handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders as a bool, not as a decoded heap handle")
val hay = "hello world"
val absent = "zzz" not in hay
assert_equal(absent.to_text(), "true")
val present = "world" not in hay
assert_equal(present.to_text(), "false")
```

</details>

#### is the exact negation of in

- is the exact negation of in


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is the exact negation of in")
val a: [i64] = [10, 20, 30]
assert_equal(20 not in a, not (20 in a))
assert_equal(99 not in a, not (99 in a))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/in_operator_membership_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering in operator membership, not in operator membership.
- in operator membership
- not in operator membership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `f44c5540ca6e516762fe54a523cc744aeccd3411af616fa7553b1b93be8ae6b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f44c5540ca6e516762fe54a523cc744aeccd3411af616fa7553b1b93be8ae6b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f44c5540ca6e516762fe54a523cc744aeccd3411af616fa7553b1b93be8ae6b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/language/in_operator_membership_spec.spl
mirror: doc/06_spec/01_unit/language/in_operator_membership_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/in_operator_membership_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/in_operator_membership_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/in_operator_membership_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds an i64 element at the first position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/in_operator_membership_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds an i64 element in the middle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/in_operator_membership_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds an i64 element at the last position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
