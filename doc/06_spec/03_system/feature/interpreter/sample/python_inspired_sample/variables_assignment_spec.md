# Variables and Assignment (Interpreter)

> Tests variable declaration and assignment in the interpreter including val/var bindings, walrus operator, and scope rules. Verifies that variable mutations are correctly tracked and that immutability constraints are enforced.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Variables and Assignment (Interpreter)

Tests variable declaration and assignment in the interpreter including val/var bindings, walrus operator, and scope rules. Verifies that variable mutations are correctly tracked and that immutability constraints are enforced.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests variable declaration and assignment in the interpreter including val/var
bindings, walrus operator, and scope rules. Verifies that variable mutations
are correctly tracked and that immutability constraints are enforced.

## Scenarios

### Variables and Assignment

#### val declarations

#### creates immutable binding with inferred type

- creates immutable binding with inferred type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates immutable binding with inferred type")
val x = 42
expect x == 42
```

</details>

#### creates immutable binding with explicit type

- creates immutable binding with explicit type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates immutable binding with explicit type")
val name: text = "Alice"
expect name == "Alice"
```

</details>

#### var declarations

#### allows reassignment of mutable binding

- allows reassignment of mutable binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows reassignment of mutable binding")
var count = 0
count = count + 1
expect count == 1
```

</details>

#### supports compound assignment

- supports compound assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports compound assignment")
var total = 10
total = total + 5
expect total == 15
```

</details>

#### type inference

#### infers integer type

- infers integer type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers integer type")
val num = 100
expect num == 100
```

</details>

#### infers string type

- infers string type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers string type")
val msg = "hello"
expect msg == "hello"
```

</details>

#### infers boolean type

- infers boolean type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers boolean type")
val flag = true
expect flag == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `900fdc4f5f6544c7a47d3fb5822f61e435ea0f970c715c15dd4b4dd94bed8ab0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `900fdc4f5f6544c7a47d3fb5822f61e435ea0f970c715c15dd4b4dd94bed8ab0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `900fdc4f5f6544c7a47d3fb5822f61e435ea0f970c715c15dd4b4dd94bed8ab0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates immutable binding with inferred type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates immutable binding with explicit type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows reassignment of mutable binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
