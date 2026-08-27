# Static Fn Specification

> Tests covering Static Function Methods, Static Method Return Types, Static Method Patterns, Static Method Edge Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Fn Specification

## Scenarios

### Static Function Methods

#### basic static method invocation

#### can call static fn new on CallEventRecorder

- can call static fn new on CallEventRecorder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("can call static fn new on CallEventRecorder")
val recorder = CallEventRecorder.new()
expect recorder.events.len() == 0
```

</details>

#### calls CallEventRecorder factory with initial event

- calls CallEventRecorder factory with initial event


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("calls CallEventRecorder factory with initial event")
val recorder = CallEventRecorder.with_initial_event("startup")
expect recorder.events.len() == 1
```

</details>

#### Point factory methods

#### creates origin point

- creates origin point


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates origin point")
val p = Point.origin()
expect p.x == 0
expect p.y == 0
```

</details>

#### creates point from pair

- creates point from pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates point from pair")
val p = Point.from_pair((5, 10))
expect p.x == 5
expect p.y == 10
```

</details>

#### creates diagonal point

- creates diagonal point


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates diagonal point")
val p = Point.on_diagonal(7)
expect p.x == 7
expect p.y == 7
```

</details>

#### creates unit x vector

- creates unit x vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates unit x vector")
val p = Point.unit_x()
expect p.x == 1
expect p.y == 0
```

</details>

#### creates unit y vector

- creates unit y vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates unit y vector")
val p = Point.unit_y()
expect p.x == 0
expect p.y == 1
```

</details>

#### Color factory methods

#### creates black color

- creates black color


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates black color")
val c = Color.black()
expect c.r == 0
expect c.g == 0
expect c.b == 0
```

</details>

#### creates white color

- creates white color


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates white color")
val c = Color.white()
expect c.r == 255
expect c.g == 255
expect c.b == 255
```

</details>

#### creates red color

- creates red color


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates red color")
val c = Color.red()
expect c.r == 255
expect c.g == 0
expect c.b == 0
```

</details>

#### Direction factory methods

#### creates northeast direction

- creates northeast direction


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates northeast direction")
val d = Direction.northeast()
match d:
    case Direction.Custom(deg):
        expect deg == 45
    case _:
        expect false
```

</details>

#### creates southeast direction

- creates southeast direction


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates southeast direction")
val d = Direction.southeast()
match d:
    case Direction.Custom(deg):
        expect deg == 135
    case _:
        expect false
```

</details>

#### creates southwest direction

- creates southwest direction


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates southwest direction")
val d = Direction.southwest()
match d:
    case Direction.Custom(deg):
        expect deg == 225
    case _:
        expect false
```

</details>

#### creates northwest direction

- creates northwest direction


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates northwest direction")
val d = Direction.northwest()
match d:
    case Direction.Custom(deg):
        expect deg == 315
    case _:
        expect false
```

</details>

### Static Method Return Types

#### return type inference

#### returns correct instance type

- returns correct instance type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns correct instance type")
val p = Point.origin()
expect p.x == 0
```

</details>

#### returns multiple instances correctly

- returns multiple instances correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("returns multiple instances correctly")
val p1 = Point.origin()
val p2 = Point.unit_x()
expect p1.x == 0
expect p2.x == 1
```

</details>

#### color factory returns Color type

- color factory returns Color type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("color factory returns Color type")
val black = Color.black()
val white = Color.white()
expect black.r == 0
expect white.r == 255
```

</details>

### Static Method Patterns

#### factory pattern

#### provides specialized factory for common case

- provides specialized factory for common case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("provides specialized factory for common case")
val origin = Point.origin()
expect origin.x == 0 && origin.y == 0
```

</details>

#### provides multiple factories for different cases

- provides multiple factories for different cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("provides multiple factories for different cases")
val origin = Point.origin()
val unit_x = Point.unit_x()
val unit_y = Point.unit_y()
expect origin.x == 0
expect unit_x.x == 1
expect unit_y.y == 1
```

</details>

#### named constructor pattern

#### uses descriptive factory name

- uses descriptive factory name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("uses descriptive factory name")
val diagonal = Point.on_diagonal(5)
expect diagonal.x == 5
expect diagonal.y == 5
```

</details>

#### stacks multiple named constructors

- stacks multiple named constructors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("stacks multiple named constructors")
val p1 = Point.origin()
val p2 = Point.unit_x()
val p3 = Point.from_pair((3, 4))
expect [p1.x, p2.x, p3.x] == [0, 1, 3]
```

</details>

#### color factory variations

#### provides named color factories

- provides named color factories


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("provides named color factories")
val black = Color.black()
val white = Color.white()
val red = Color.red()
expect black.r == 0
expect white.r == 255
expect red.r == 255
```

</details>

### Static Method Edge Cases

#### parameterless static methods

#### calls static method with no parameters

- calls static method with no parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("calls static method with no parameters")
val p = Point.origin()
expect true
```

</details>

#### multiple calls to same parameterless factory

- multiple calls to same parameterless factory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("multiple calls to same parameterless factory")
val p1 = Point.origin()
val p2 = Point.origin()
expect p1.x == p2.x && p1.y == p2.y
```

</details>

#### multiple instances

#### creates independent instances

- creates independent instances


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("creates independent instances")
val p1 = Point.origin()
val p2 = Point.unit_x()
expect p1.x != p2.x || p1.y != p2.y
```

</details>

#### records instances independently

- records instances independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("records instances independently")
val r1 = CallEventRecorder.new()
val r2 = CallEventRecorder.with_initial_event("test")
expect r1.events.len() == 0
expect r2.events.len() == 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/control_flow/static_fn_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Static Function Methods, Static Method Return Types, Static Method Patterns, Static Method Edge Cases.
- Static Function Methods
- Static Method Return Types
- Static Method Patterns
- Static Method Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SHARED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87df7dab985dce6d0957db8fc29ad8c9af743c8f38131d9458621b1cd110eb2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87df7dab985dce6d0957db8fc29ad8c9af743c8f38131d9458621b1cd110eb2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87df7dab985dce6d0957db8fc29ad8c9af743c8f38131d9458621b1cd110eb2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/shared/control_flow/static_fn_spec.spl
mirror: doc/06_spec/shared/control_flow/static_fn_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/control_flow/static_fn_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/control_flow/static_fn_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/control_flow/static_fn_spec.spl:164:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can call static fn new on CallEventRecorder' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/shared/control_flow/static_fn_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can call static fn new on CallEventRecorder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/control_flow/static_fn_spec.spl:170:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls CallEventRecorder factory with initial event' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/control_flow/static_fn_spec.spl:177:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates origin point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
