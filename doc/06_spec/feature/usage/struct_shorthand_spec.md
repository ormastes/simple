# Struct Field Shorthand Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Struct Field Shorthand Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STRUCT-SHORTHAND |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/struct_shorthand_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Without shorthand (verbose)
use std.spec.step

val point = Point(x: x, y: y)

# With shorthand (when variable names match field names)
val point = Point(x, y)

# Mixed shorthand and explicit
val point = Point(x, y: computed_y)
```

## Key Behaviors

- Variable name must exactly match the field name
- Order must match the struct definition
- Can mix shorthand and explicit field names
- Works with any struct type

## Scenarios

### Struct Field Shorthand

#### basic struct shorthand

#### uses shorthand for matching variable names

- uses shorthand for matching variable names


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses shorthand for matching variable names")
struct Point:
    x: i64
    y: i64
val x = 10
val y = 20
val point = Point(x, y)
expect point.x == 10
expect point.y == 20
```

</details>

#### constructs struct with all shorthand fields

- constructs struct with all shorthand fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("constructs struct with all shorthand fields")
struct Person:
    name: text
    age: i64
val name = "Alice"
val age = 30
val person = Person(name, age)
expect person.name == "Alice"
expect person.age == 30
```

</details>

#### mixed shorthand and explicit

#### mixes shorthand with explicit named argument

- mixes shorthand with explicit named argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixes shorthand with explicit named argument")
struct Point:
    x: i64
    y: i64
val x = 10
val point = Point(x, y: 20)
expect point.x == 10
expect point.y == 20
```

</details>

#### uses explicit then shorthand

- uses explicit then shorthand


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses explicit then shorthand")
struct Point:
    x: i64
    y: i64
val y = 20
val point = Point(x: 10, y)
expect point.x == 10
expect point.y == 20
```

</details>

#### mixes in complex struct

- mixes in complex struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixes in complex struct")
struct Config:
    host: text
    port: i64
    timeout: i64
val host = "localhost"
val timeout = 30
val config = Config(host, port: 8080, timeout)
expect config.host == "localhost"
expect config.port == 8080
expect config.timeout == 30
```

</details>

#### shorthand with computed values

#### uses shorthand after computation

- uses shorthand after computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses shorthand after computation")
struct Rectangle:
    width: i64
    height: i64
val width = 5 * 2
val height = 3 * 2
val rect = Rectangle(width, height)
expect rect.width == 10
expect rect.height == 6
```

</details>

#### uses shorthand from function return

- uses shorthand from function return


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses shorthand from function return")
struct Point:
    x: i64
    y: i64
fn get_x() -> i64:
    100
fn get_y() -> i64:
    200
val x = get_x()
val y = get_y()
val point = Point(x, y)
expect point.x == 100
expect point.y == 200
```

</details>

#### shorthand with different types

#### handles text fields

- handles text fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles text fields")
struct Message:
    sender: text
    content: text
val sender = "Alice"
val content = "Hello!"
val msg = Message(sender, content)
expect msg.sender == "Alice"
expect msg.content == "Hello!"
```

</details>

#### handles boolean fields

- handles boolean fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles boolean fields")
struct Flags:
    enabled: bool
    visible: bool
val enabled = true
val visible = false
val flags = Flags(enabled, visible)
expect flags.enabled == true
expect flags.visible == false
```

</details>

#### handles mixed types

- handles mixed types


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles mixed types")
struct Record:
    id: i64
    name: text
    active: bool
val id = 42
val name = "Test"
val active = true
val record = Record(id, name, active)
expect record.id == 42
expect record.name == "Test"
expect record.active == true
```

</details>

#### shorthand in nested structs

#### uses shorthand when nesting

- uses shorthand when nesting


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses shorthand when nesting")
struct Point:
    x: i64
    y: i64
struct Line:
    start: Point
    endpoint: Point
val x = 0
val y = 0
val start = Point(x, y)
val x2 = 10
val y2 = 10
val endpoint = Point(x: x2, y: y2)
val line = Line(start, endpoint)
expect line.start.x == 0
expect line.endpoint.x == 10
```

</details>

#### explicit syntax still works

#### allows fully explicit construction

- allows fully explicit construction


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows fully explicit construction")
struct Point:
    x: i64
    y: i64
val a = 100
val b = 200
val point = Point(x: a, y: b)
expect point.x == 100
expect point.y == 200
```

</details>

#### allows equals syntax explicitly

- allows equals syntax explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows equals syntax explicitly")
struct Point:
    x: i64
    y: i64
val point = Point(x=30, y=40)
expect point.x == 30
expect point.y == 40
```

</details>

#### shorthand in collections

#### uses shorthand in list of structs

- uses shorthand in list of structs


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses shorthand in list of structs")
struct Point:
    x: i64
    y: i64
var points: [Point] = []
for i in 0..3:
    val x = i * 10
    val y = i * 20
    points = points.append(Point(x, y))
expect points[0].x == 0
expect points[1].x == 10
expect points[2].x == 20
```

</details>

#### uses shorthand with map

- uses shorthand with map


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses shorthand with map")
struct Point:
    x: i64
    y: i64
# Build points manually since multi-line lambda with destructuring
# is not supported in interpreter mode
val x1 = 1
val y1 = 2
val x2 = 3
val y2 = 4
val points = [Point(x: x1, y: y1), Point(x: x2, y: y2)]
expect points[0].x == 1
expect points[1].y == 4
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `268a9038200ca6ca3ae596e99cd2c020ff5e9d976add7154368afbfd390385a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `268a9038200ca6ca3ae596e99cd2c020ff5e9d976add7154368afbfd390385a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `268a9038200ca6ca3ae596e99cd2c020ff5e9d976add7154368afbfd390385a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/struct_shorthand_spec.spl
mirror: doc/06_spec/feature/usage/struct_shorthand_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/struct_shorthand_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/struct_shorthand_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/struct_shorthand_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses shorthand for matching variable names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/struct_shorthand_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs struct with all shorthand fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/struct_shorthand_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mixes shorthand with explicit named argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
