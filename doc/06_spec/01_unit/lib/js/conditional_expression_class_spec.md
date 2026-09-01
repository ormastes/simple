# Conditional Expression Class Specification

> Tests covering JS parser must not silently truncate conditional expressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Conditional Expression Class Specification

## Scenarios

### JS parser must not silently truncate conditional expressions

#### does not degrade a ternary to its condition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not degrade a ternary to its condition
   - Expected: eval_str("5 < 2 ? 100 : 200") equals `200`
   - Expected: eval_str("5 > 2 ? 100 : 200") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not degrade a ternary to its condition")
# The signature symptom of the class: the answer is the CONDITION's
# value ("false"/"true") rather than either branch.
expect(eval_str("5 < 2 ? 100 : 200")).to_equal("200")
expect(eval_str("5 > 2 ? 100 : 200")).to_equal("100")
```

</details>

#### keeps the ternary below || and && in precedence

- keeps the ternary below || and && in precedence
   - Expected: eval_str("0 || 0 ? 11 : 22") equals `22`
   - Expected: eval_str("1 && 1 ? 11 : 22") equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the ternary below || and && in precedence")
expect(eval_str("0 || 0 ? 11 : 22")).to_equal("22")
expect(eval_str("1 && 1 ? 11 : 22")).to_equal("11")
```

</details>

#### keeps the ternary above comparison and arithmetic

- keeps the ternary above comparison and arithmetic
   - Expected: eval_str("1 + 2 > 2 ? 3 * 3 : 4 + 4") equals `9`
   - Expected: eval_str("1 + 2 > 9 ? 3 * 3 : 4 + 4") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the ternary above comparison and arithmetic")
expect(eval_str("1 + 2 > 2 ? 3 * 3 : 4 + 4")).to_equal("9")
expect(eval_str("1 + 2 > 9 ? 3 * 3 : 4 + 4")).to_equal("8")
```

</details>

#### keeps the ternary below assignment

- keeps the ternary below assignment
   - Expected: eval_str("var a = 0; a = 1 ? 7 : 8; a") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the ternary below assignment")
expect(eval_str("var a = 0; a = 1 ? 7 : 8; a")).to_equal("7")
```

</details>

#### parses a ternary nested in either branch

- parses a ternary nested in either branch
   - Expected: eval_str("0 ? 1 : 0 ? 2 : 3") equals `3`
   - Expected: eval_str("1 ? 0 ? 7 : 8 : 9") equals `8`
   - Expected: eval_str("1 ? 1 ? 7 : 8 : 9") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a ternary nested in either branch")
expect(eval_str("0 ? 1 : 0 ? 2 : 3")).to_equal("3")
expect(eval_str("1 ? 0 ? 7 : 8 : 9")).to_equal("8")
expect(eval_str("1 ? 1 ? 7 : 8 : 9")).to_equal("7")
```

</details>

#### parses a ternary inside call arguments

- parses a ternary inside call arguments
   - Expected: eval_str("var id = x => x; id(1 < 2 ? 'yes' : 'no')") equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a ternary inside call arguments")
expect(eval_str("var id = x => x; id(1 < 2 ? 'yes' : 'no')")).to_equal("yes")
```

</details>

#### parses a ternary inside an array literal and indexes the result

- parses a ternary inside an array literal and indexes the result
   - Expected: eval_str("var a = [1 > 0 ? 5 : 6, 7]; a[0]") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a ternary inside an array literal and indexes the result")
expect(eval_str("var a = [1 > 0 ? 5 : 6, 7]; a[0]")).to_equal("5")
```

</details>

#### parses a ternary whose branches are parenthesised

- parses a ternary whose branches are parenthesised
   - Expected: eval_str("(1 > 0) ? (2 + 3) : (4 + 5)") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a ternary whose branches are parenthesised")
expect(eval_str("(1 > 0) ? (2 + 3) : (4 + 5)")).to_equal("5")
```

</details>

#### does not treat ?? or ?. as a conditional

- does not treat ?? or ?. as a conditional
   - Expected: eval_str("null ?? 5") equals `5`
   - Expected: eval_str("var a = 0; a ?? 9") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat ?? or ?. as a conditional")
expect(eval_str("null ?? 5")).to_equal("5")
expect(eval_str("var a = 0; a ?? 9")).to_equal("0")
```

</details>

#### does not treat a ? or : inside a string literal as an operator

- does not treat a ? or : inside a string literal as an operator
   - Expected: eval_str("1 > 0 ? 'a?b:c' : 'z'") equals `a?b:c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat a ? or : inside a string literal as an operator")
expect(eval_str("1 > 0 ? 'a?b:c' : 'z'")).to_equal("a?b:c")
```

</details>

#### does not treat an object literal colon as a ternary colon

- does not treat an object literal colon as a ternary colon
   - Expected: eval_str("var o = 1 > 0 ? 4 : 5; o") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat an object literal colon as a ternary colon")
expect(eval_str("var o = 1 > 0 ? 4 : 5; o")).to_equal("4")
```

</details>

#### evaluates only the taken branch operand chain

- evaluates only the taken branch operand chain
   - Expected: eval_str("var n = 3; n > 2 ? n * 10 : n * 100") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates only the taken branch operand chain")
expect(eval_str("var n = 3; n > 2 ? n * 10 : n * 100")).to_equal("30")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/js/conditional_expression_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS parser must not silently truncate conditional expressions.
- JS parser must not silently truncate conditional expressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `fa418f25a5e8a17ad8da2c4af2658961611b82af63e7b9ffcbcd125a52db36c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa418f25a5e8a17ad8da2c4af2658961611b82af63e7b9ffcbcd125a52db36c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa418f25a5e8a17ad8da2c4af2658961611b82af63e7b9ffcbcd125a52db36c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/js/conditional_expression_class_spec.spl
mirror: doc/06_spec/01_unit/lib/js/conditional_expression_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/js/conditional_expression_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/js/conditional_expression_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/js/conditional_expression_class_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not degrade a ternary to its condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/conditional_expression_class_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the ternary below || and && in precedence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/conditional_expression_class_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the ternary above comparison and arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
