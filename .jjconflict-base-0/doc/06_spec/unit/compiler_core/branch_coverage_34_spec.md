# Branch Coverage 34 Specification

> Tests covering Struct Arrays, Nested Arrays, Arrays of Optional Types, Complex Nested Structures, Array Element Type Extraction, Array Literal Initialization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 34 Specification

## Scenarios

### Struct Arrays

#### array of simple structs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- array of simple structs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array of simple structs")
struct Point:
    x: i64
    y: i64

val points = [Point(x: 1, y: 2), Point(x: 3, y: 4)]
check(points.len() == 2)
check(points[0].x == 1)
check(points[1].y == 4)
```

</details>

#### array of structs with multiple fields

- array of structs with multiple fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array of structs with multiple fields")
struct Data:
    id: i64
    value: i64
    active: bool

val items = [
    Data(id: 1, value: 100, active: true),
    Data(id: 2, value: 200, active: false)
]
check(items.len() == 2)
check(items[0].active)
check(not items[1].active)
```

</details>

#### empty struct array

- empty struct array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty struct array")
struct Empty:
    pass

val arr: [Empty] = []
check(arr.len() == 0)
```

</details>

### Nested Arrays

#### 2d integer array

- 2d integer array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2d integer array")
val arr2d: [[i64]] = [[1, 2], [3, 4], [5, 6]]
check(arr2d.len() == 3)
check(arr2d[0].len() == 2)
check(arr2d[0][0] == 1)
check(arr2d[2][1] == 6)
```

</details>

#### 3d array

- 3d array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3d array")
val arr3d: [[[i64]]] = [[[1, 2]], [[3, 4]]]
check(arr3d.len() == 2)
check(arr3d[0][0][0] == 1)
```

</details>

#### jagged arrays

- jagged arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jagged arrays")
val jagged = [[1], [2, 3], [4, 5, 6]]
check(jagged[0].len() == 1)
check(jagged[1].len() == 2)
check(jagged[2].len() == 3)
```

</details>

#### nested array of strings

- nested array of strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested array of strings")
val strs: [[text]] = [["a", "b"], ["c", "d"]]
check(strs[0][0] == "a")
check(strs[1][1] == "d")
```

</details>

### Arrays of Optional Types

#### optional integer array

- optional integer array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional integer array")
val opts: [i64?] = [Some(1), nil, Some(3)]
check(opts.len() == 3)
check(opts[0].?)
check(not opts[1].?)
check(opts[2].?)
```

</details>

#### optional struct array

- optional struct array


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional struct array")
struct Value:
    n: i64

val items: [Value?] = [Some(Value(n: 1)), nil]
check(items[0].?)
check(not items[1].?)
```

</details>

### Complex Nested Structures

#### array of arrays of optionals

- array of arrays of optionals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array of arrays of optionals")
val complex: [[i64?]] = [[Some(1), nil], [Some(2), Some(3)]]
check(complex[0][0].?)
check(not complex[0][1].?)
```

</details>

#### struct containing arrays

- struct containing arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct containing arrays")
struct Container:
    values: [i64]

val c = Container(values: [1, 2, 3])
check(c.values.len() == 3)
```

</details>

#### nested struct array

- nested struct array


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested struct array")
struct Inner:
    x: i64

struct Outer:
    inner: Inner

val items = [Outer(inner: Inner(x: 1)), Outer(inner: Inner(x: 2))]
check(items[0].inner.x == 1)
```

</details>

### Array Element Type Extraction

#### simple type arrays

- simple type arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple type arrays")
val ints: [i64] = [1, 2, 3]
val floats: [f64] = [1.0, 2.0]
val bools: [bool] = [true, false]
check(ints.len() > 0)
check(floats.len() > 0)
check(bools.len() > 0)
```

</details>

#### text arrays

- text arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text arrays")
val texts: [text] = ["a", "b", "c"]
check(texts[0] == "a")
```

</details>

### Array Literal Initialization

#### mixed expressions in array

- mixed expressions in array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixed expressions in array")
val x = 5
val arr = [x, x + 1, x + 2, x * 2]
check(arr[0] == 5)
check(arr[1] == 6)
check(arr[3] == 10)
```

</details>

#### nested literals

- nested literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested literals")
val nested = [
    [1, 2, 3],
    [4, 5, 6],
    [7, 8, 9]
]
check(nested[1][1] == 5)
```

</details>

#### deep nesting

- deep nesting


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep nesting")
val deep = [
    [[1, 2], [3, 4]],
    [[5, 6], [7, 8]]
]
check(deep[0][0][0] == 1)
check(deep[1][1][1] == 8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/branch_coverage_34_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Struct Arrays, Nested Arrays, Arrays of Optional Types, Complex Nested Structures, Array Element Type Extraction, Array Literal Initialization.
- Struct Arrays
- Nested Arrays
- Arrays of Optional Types
- Complex Nested Structures
- Array Element Type Extraction
- Array Literal Initialization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `db31b7b9893f06f748a2889eb3d1d6824f18e1ac2fcdf57bb0b8c19f93644ffc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db31b7b9893f06f748a2889eb3d1d6824f18e1ac2fcdf57bb0b8c19f93644ffc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db31b7b9893f06f748a2889eb3d1d6824f18e1ac2fcdf57bb0b8c19f93644ffc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/branch_coverage_34_spec.spl
mirror: doc/06_spec/unit/compiler_core/branch_coverage_34_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/branch_coverage_34_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/branch_coverage_34_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/branch_coverage_34_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'array of simple structs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_34_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'array of structs with multiple fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_34_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty struct array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
