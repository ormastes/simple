# Interpreter Sample Programs

> Tests the Simple language interpreter with representative sample programs covering arithmetic operations, comparison operators, boolean logic, and string handling. Verifies that complete programs execute correctly in interpreted mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Sample Programs

Tests the Simple language interpreter with representative sample programs covering arithmetic operations, comparison operators, boolean logic, and string handling. Verifies that complete programs execute correctly in interpreted mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/interpreter_sample_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Simple language interpreter with representative sample programs covering
arithmetic operations, comparison operators, boolean logic, and string handling.
Verifies that complete programs execute correctly in interpreted mode.

## Scenarios

### Simple Interpreter

#### when evaluating expressions

#### handles arithmetic operations

- handles arithmetic operations
   - Expected: 1 + 1 equals `2`
   - Expected: 10 - 3 equals `7`
   - Expected: 4 * 5 equals `20`
   - Expected: 15 / 3 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles arithmetic operations")
expect(1 + 1).to_equal(2)
expect(10 - 3).to_equal(7)
expect(4 * 5).to_equal(20)
expect(15 / 3).to_equal(5)
```

</details>

#### handles comparison operations

- handles comparison operations
   - Expected: 5 > 3 is true
   - Expected: 2 < 10 is true
   - Expected: 5 equals `5`
   - Expected: 3 != 4 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles comparison operations")
expect(5 > 3).to_equal(true)
expect(2 < 10).to_equal(true)
expect(5).to_equal(5)
expect(3 != 4).to_equal(true)
```

</details>

#### handles boolean operations

- handles boolean operations
   - Expected: true and true is true
   - Expected: true and false is false
   - Expected: true or false is true
   - Expected: not false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles boolean operations")
expect(true and true).to_equal(true)
expect(true and false).to_equal(false)
expect(true or false).to_equal(true)
expect(not false).to_equal(true)
```

</details>

#### when working with strings

#### supports string concatenation

- supports string concatenation
   - Expected: s equals `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports string concatenation")
val s = "Hello" + " " + "World"
expect(s).to_equal("Hello World")
```

</details>

#### supports string interpolation

- supports string interpolation
   - Expected: msg equals `Name: Alice, Age: 30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports string interpolation")
val name = "Alice"
val age = 30
val msg = "Name: {name}, Age: {age}"
expect(msg).to_equal("Name: Alice, Age: 30")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c8c316f613b534cdce79f39e4afd9502923c6d504d787e714e1405f5c036225`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c8c316f613b534cdce79f39e4afd9502923c6d504d787e714e1405f5c036225`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c8c316f613b534cdce79f39e4afd9502923c6d504d787e714e1405f5c036225`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/interpreter/interpreter_sample_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/interpreter_sample_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/interpreter_sample_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/interpreter_sample_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/interpreter_sample_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/interpreter/interpreter_sample_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles arithmetic operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/interpreter_sample_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles comparison operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/interpreter_sample_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles boolean operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
