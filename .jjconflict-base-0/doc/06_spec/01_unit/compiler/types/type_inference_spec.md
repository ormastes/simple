# Type Inference Specification

> Tests covering Integer Type Inference, Float Type Inference, Boolean Type Inference, String Type Inference, Array Type Inference, Option Type Inference, Function Return Type Inference, Generic Type Inference.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Inference Specification

## Scenarios

### Integer Type Inference

#### infer i64 from integer literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- infer i64 from integer literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer i64 from integer literal")
val x = 42
check(x == 42)
```

</details>

#### infer i64 from negative literal

- infer i64 from negative literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer i64 from negative literal")
val x = -5
check(x == -5)
```

</details>

#### infer i64 from zero

- infer i64 from zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer i64 from zero")
val x = 0
check(x == 0)
```

</details>

#### infer i64 from large number

- infer i64 from large number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer i64 from large number")
val x = 1000000
check(x == 1000000)
```

</details>

#### infer from arithmetic expression

- infer from arithmetic expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer from arithmetic expression")
val x = 3 + 4
check(x == 7)
```

</details>

### Float Type Inference

#### infer f64 from float literal

- infer f64 from float literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer f64 from float literal")
val x = 3.14
check(x > 3.0)
```

</details>

#### infer f64 from negative float

- infer f64 from negative float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer f64 from negative float")
val x = -2.5
check(x < 0.0)
```

</details>

#### infer f64 from float arithmetic

- infer f64 from float arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer f64 from float arithmetic")
val x = 1.5 + 2.5
check(x > 3.9 and x < 4.1)
```

</details>

### Boolean Type Inference

#### infer bool from true

- infer bool from true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer bool from true")
val x = true
check(x)
```

</details>

#### infer bool from false

- infer bool from false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer bool from false")
val x = false
check(not x)
```

</details>

#### infer bool from comparison

- infer bool from comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer bool from comparison")
val x = 5 > 3
check(x)
```

</details>

#### infer bool from logical

- infer bool from logical


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer bool from logical")
val x = true and false
check(not x)
```

</details>

### String Type Inference

#### infer text from string literal

- infer text from string literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer text from string literal")
val x = "hello"
check(x == "hello")
```

</details>

#### infer text from interpolation

- infer text from interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer text from interpolation")
val name = "world"
val x = "hello {name}"
check(x.contains("world"))
```

</details>

#### infer text from concatenation

- infer text from concatenation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer text from concatenation")
val x = "a" + "b"
check(x == "ab")
```

</details>

### Array Type Inference

#### infer array of i64

- infer array of i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer array of i64")
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### infer array of text

- infer array of text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer array of text")
val arr = ["a", "b", "c"]
check(arr.len() == 3)
```

</details>

#### infer empty array

- infer empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer empty array")
val arr: [i64] = []
check(arr.len() == 0)
```

</details>

#### infer nested array

- infer nested array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer nested array")
val arr = [[1, 2], [3, 4]]
check(arr.len() == 2)
```

</details>

### Option Type Inference

#### infer Some variant

- infer Some variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer Some variant")
val x = Some(42)
check(x != nil)
```

</details>

#### infer nil

- infer nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer nil")
val x = nil
check(x == nil)
```

</details>

#### infer from optional chaining

- infer from optional chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer from optional chaining")
val x = Some(42)
val y = x ?? 0
check(y == 42)
```

</details>

#### nil coalescing with default

- nil coalescing with default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil coalescing with default")
val x = nil
val y = x ?? 99
check(y == 99)
```

</details>

### Function Return Type Inference

#### infer return type from body

- infer return type from body


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer return type from body")
fn double(x: i64) -> i64:
    x * 2
check(double(21) == 42)
```

</details>

#### infer return type from if-else

- infer return type from if-else


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer return type from if-else")
fn sign(x: i64) -> i64:
    if x > 0:
        1
    elif x < 0:
        -1
    else:
        0
check(sign(5) == 1)
check(sign(-3) == -1)
check(sign(0) == 0)
```

</details>

#### infer return type from match

- infer return type from match


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer return type from match")
fn describe_num(x: i64) -> text:
    match x:
        0: "zero"
        1: "one"
        _: "other"
check(describe_num(0) == "zero")
check(describe_num(1) == "one")
check(describe_num(99) == "other")
```

</details>

### Generic Type Inference

#### infer generic from usage

- infer generic from usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer generic from usage")
fn first(arr: [i64]) -> i64:
    arr[0]
check(first([10, 20]) == 10)
```

</details>

#### infer generic map result

- infer generic map result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer generic map result")
val arr = [1, 2, 3]
val doubled = arr.map(_1 * 2)
check(doubled[0] == 2)
check(doubled[1] == 4)
```

</details>

#### infer generic filter result

- infer generic filter result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer generic filter result")
val arr = [1, 2, 3, 4, 5]
val evens = arr.filter(_1 % 2 == 0)
check(evens.len() == 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/types/type_inference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Integer Type Inference, Float Type Inference, Boolean Type Inference, String Type Inference, Array Type Inference, Option Type Inference, Function Return Type Inference, Generic Type Inference.
- Integer Type Inference
- Float Type Inference
- Boolean Type Inference
- String Type Inference
- Array Type Inference
- Option Type Inference
- Function Return Type Inference
- Generic Type Inference

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `ef5067c5f028c1f9252e69142ef4102d93fbda3a4d8897afd50753bb8a255bed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef5067c5f028c1f9252e69142ef4102d93fbda3a4d8897afd50753bb8a255bed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef5067c5f028c1f9252e69142ef4102d93fbda3a4d8897afd50753bb8a255bed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/types/type_inference_spec.spl
mirror: doc/06_spec/01_unit/compiler/types/type_inference_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/types/type_inference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/types/type_inference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/types/type_inference_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infer i64 from integer literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/type_inference_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infer i64 from negative literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/type_inference_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infer i64 from zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
