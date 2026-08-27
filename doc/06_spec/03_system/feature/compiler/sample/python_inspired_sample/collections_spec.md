# Collections (Python-Inspired Sample)

> Tests compilation of collection types inspired by Python including lists, maps, and iteration patterns. Verifies that collection literals, comprehensions, and standard collection operations compile correctly through the native pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collections (Python-Inspired Sample)

Tests compilation of collection types inspired by Python including lists, maps, and iteration patterns. Verifies that collection literals, comprehensions, and standard collection operations compile correctly through the native pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/collections_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of collection types inspired by Python including lists, maps,
and iteration patterns. Verifies that collection literals, comprehensions, and
standard collection operations compile correctly through the native pipeline.

## Scenarios

### Collections

#### list operations

#### creates list literal

- creates list literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates list literal")
val numbers = [1, 2, 3, 4, 5]
expect numbers.len() == 5
```

</details>

#### accesses elements by index

- accesses elements by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses elements by index")
val items = [10, 20, 30]
expect items[0] == 10
expect items[2] == 30
```

</details>

#### iterates over list

- iterates over list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates over list")
val numbers = [1, 2, 3]
var sum = 0
for n in numbers:
    sum = sum + n
expect sum == 6
```

</details>

#### dict operations

#### creates dict literal

- creates dict literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates dict literal")
val person = {"name": "Alice", "age": 30}
expect person["name"] == "Alice"
```

</details>

#### adds and retrieves values

- adds and retrieves values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds and retrieves values")
var m = {}
m["key"] = "value"
expect m["key"] == "value"
```

</details>

#### checks key existence

- checks key existence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks key existence")
val m = {"a": 1}
expect m.has("a")
expect not m.has("b")
```

</details>

#### list comprehensions

#### creates list with comprehension

- creates list with comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates list with comprehension")
val squares = [for x in [1, 2, 3, 4]: x * x]
expect squares[0] == 1
expect squares.len() == 4
expect squares[3] == 16
```

</details>

#### filters with comprehension

- filters with comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with comprehension")
val evens = [for x in [1, 2, 3, 4, 5, 6] if x % 2 == 0: x]
expect evens.len() == 3
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `00c8ca35c882648d1ea67e4ddc6081f6cb8eea8a5b0257dbe7ca5fa44ee856e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00c8ca35c882648d1ea67e4ddc6081f6cb8eea8a5b0257dbe7ca5fa44ee856e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00c8ca35c882648d1ea67e4ddc6081f6cb8eea8a5b0257dbe7ca5fa44ee856e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/compiler/sample/python_inspired_sample/collections_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/collections_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/collections_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/collections_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/sample/python_inspired_sample/collections_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates list literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/collections_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accesses elements by index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/collections_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'iterates over list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
