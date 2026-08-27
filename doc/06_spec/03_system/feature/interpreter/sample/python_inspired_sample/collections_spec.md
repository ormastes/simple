# Collections (Interpreter)

> Tests collection type handling in the interpreter including lists, maps, and iteration. Verifies that collection operations produce correct results when executed in interpreted mode with proper element access and mutation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collections (Interpreter)

Tests collection type handling in the interpreter including lists, maps, and iteration. Verifies that collection operations produce correct results when executed in interpreted mode with proper element access and mutation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/collections_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests collection type handling in the interpreter including lists, maps, and
iteration. Verifies that collection operations produce correct results when
executed in interpreted mode with proper element access and mutation.

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
val items = [1, 2, 3]
expect items.len() == 3
```

</details>

#### accesses by index

- accesses by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses by index")
val items = ["a", "b", "c"]
expect items[0] == "a"
expect items[2] == "c"
```

</details>

#### supports negative indexing

- supports negative indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports negative indexing")
val items = [10, 20, 30]
expect items[-1] == 30
```

</details>

#### slices list

- slices list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slices list")
val items = [1, 2, 3, 4, 5]
expect items[1:4] == [2, 3, 4]
```

</details>

#### dictionary operations

#### creates dict literal

- creates dict literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates dict literal")
val ages = {"alice": 30, "bob": 25}
expect ages["alice"] == 30
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
val data = {"key": "value"}
expect data.has("key") == true
expect data.has("missing") == false
```

</details>

#### collection methods

#### maps over list

- maps over list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps over list")
val nums = [1, 2, 3]
val doubled = nums.map(_ * 2)
expect doubled == [2, 4, 6]
```

</details>

#### filters list

- filters list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters list")
val nums = [1, 2, 3, 4, 5]
val evens = nums.filter(_ % 2 == 0)
expect evens == [2, 4]
```

</details>

#### list comprehensions

#### creates list with comprehension

- creates list with comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates list with comprehension")
val squares = [for x in 0..5: x * x]
expect squares == [0, 1, 4, 9, 16]
```

</details>

#### filters in comprehension

- filters in comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters in comprehension")
val evens = [for x in 0..10 if x % 2 == 0: x]
expect evens == [0, 2, 4, 6, 8]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `9b51d15165983d4b2e4f7c912504936defee3c56faedad07af284ab8529e6f0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b51d15165983d4b2e4f7c912504936defee3c56faedad07af284ab8529e6f0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b51d15165983d4b2e4f7c912504936defee3c56faedad07af284ab8529e6f0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/interpreter/sample/python_inspired_sample/collections_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/collections_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/collections_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/collections_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/sample/python_inspired_sample/collections_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates list literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/collections_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accesses by index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/collections_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports negative indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
