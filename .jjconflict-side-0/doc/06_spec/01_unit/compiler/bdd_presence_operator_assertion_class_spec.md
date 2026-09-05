# Bdd Presence Operator Assertion Class Specification

> Tests covering presence operator across every assertion position.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bdd Presence Operator Assertion Class Specification

## Scenarios

### presence operator across every assertion position

#### bare subject is true for a present value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bare subject is true for a present value
   - Expected: present.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare subject is true for a present value")
val present = "x"
expect(present.?).to_equal(true)
```

</details>

#### bare subject is false for nil

- bare subject is false for nil
   - Expected: absent.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare subject is false for nil")
val absent = nil
expect(absent.?).to_equal(false)
```

</details>

#### left operand of == compares as a bool

- left operand of == compares as a bool
   - Expected: present2.? == true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("left operand of == compares as a bool")
val present2 = 7
expect(present2.? == true).to_equal(true)
```

</details>

#### right operand of == compares as a bool

- right operand of == compares as a bool
   - Expected: false == absent2.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("right operand of == compares as a bool")
val absent2 = nil
expect(false == absent2.?).to_equal(true)
```

</details>

#### != against a bool literal works

- != against a bool literal works
   - Expected: present3.? != false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("!= against a bool literal works")
val present3 = "y"
expect(present3.? != false).to_equal(true)
```

</details>

#### empty string counts as absent

- empty string counts as absent
   - Expected: empty.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string counts as absent")
val empty = ""
expect(empty.?).to_equal(false)
```

</details>

#### empty array counts as absent

- empty array counts as absent
   - Expected: empty_arr.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty array counts as absent")
val empty_arr = []
expect(empty_arr.?).to_equal(false)
```

</details>

#### non-empty array counts as present

- non-empty array counts as present
   - Expected: arr.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-empty array counts as present")
val arr = [1, 2]
expect(arr.?).to_equal(true)
```

</details>

#### zero is a present payload, not absence

- zero is a present payload, not absence
   - Expected: zero.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero is a present payload, not absence")
val zero = 0
expect(zero.?).to_equal(true)
```

</details>

#### false is a present payload, not absence

- false is a present payload, not absence
   - Expected: flag.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false is a present payload, not absence")
val flag = false
expect(flag.?).to_equal(true)
```

</details>

#### dict miss is absent and dict hit is present

- dict miss is absent and dict hit is present
   - Expected: d.get("zzz").? is false
   - Expected: d.get("a").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict miss is absent and dict hit is present")
val d = {"a": 1}
expect(d.get("zzz").?).to_equal(false)
expect(d.get("a").?).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bdd_presence_operator_assertion_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering presence operator across every assertion position.
- presence operator across every assertion position

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `a3f97869fd3c52ad23efbfd9b64206a1be21cd54452f0c095c9a96cb4d6688c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3f97869fd3c52ad23efbfd9b64206a1be21cd54452f0c095c9a96cb4d6688c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3f97869fd3c52ad23efbfd9b64206a1be21cd54452f0c095c9a96cb4d6688c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bdd_presence_operator_assertion_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/bdd_presence_operator_assertion_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bdd_presence_operator_assertion_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bdd_presence_operator_assertion_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bdd_presence_operator_assertion_class_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bare subject is true for a present value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_presence_operator_assertion_class_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bare subject is false for nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_presence_operator_assertion_class_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'left operand of == compares as a bool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
