# Static Function Method Specification

> class Point:

<!-- sdn-diagram:id=static_fn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_fn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_fn_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_fn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Function Method Specification

class Point:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STATIC-FN, #FACTORY-METHODS |
| Category | Language Features |
| Status | Implemented |
| Source | `test/shared/control_flow/static_fn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
class Point:
x: i64
y: i64

impl Point:
static fn origin() -> Point:
Point(x: 0, y: 0)

static fn from_pair(pair: (i64, i64)) -> Point:
val (x, y) = pair
Point(x: x, y: y)

# Usage:
val p = Point.origin()
val q = Point.from_pair((5, 10))
```

## Key Behaviors

- Static functions are called on the class/enum name, not instances
- Return type is automatically inferred to be the containing class
- Can call other static or instance methods
- No implicit self parameter in the parameter list
- Useful for factory patterns and special constructors

## Scenarios

### Static Function Methods

#### basic static method invocation

#### can call static fn new on CallEventRecorder

1. expect recorder events len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallEventRecorder.new()
expect recorder.events.len() == 0
```

</details>

#### calls CallEventRecorder factory with initial event

1. expect recorder events len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallEventRecorder.with_initial_event("startup")
expect recorder.events.len() == 1
```

</details>

#### Point factory methods

#### creates origin point

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point.origin()
expect p.x == 0
expect p.y == 0
```

</details>

#### creates point from pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point.from_pair((5, 10))
expect p.x == 5
expect p.y == 10
```

</details>

#### creates diagonal point

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point.on_diagonal(7)
expect p.x == 7
expect p.y == 7
```

</details>

#### creates unit x vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point.unit_x()
expect p.x == 1
expect p.y == 0
```

</details>

#### creates unit y vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point.unit_y()
expect p.x == 0
expect p.y == 1
```

</details>

#### Color factory methods

#### creates black color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.black()
expect c.r == 0
expect c.g == 0
expect c.b == 0
```

</details>

#### creates white color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.white()
expect c.r == 255
expect c.g == 255
expect c.b == 255
```

</details>

#### creates red color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.red()
expect c.r == 255
expect c.g == 0
expect c.b == 0
```

</details>

#### Direction factory methods

#### creates northeast direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Direction.northeast()
match d:
    case Direction.Custom(deg):
        expect deg == 45
    case _:
        expect false
```

</details>

#### creates southeast direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Direction.southeast()
match d:
    case Direction.Custom(deg):
        expect deg == 135
    case _:
        expect false
```

</details>

#### creates southwest direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Direction.southwest()
match d:
    case Direction.Custom(deg):
        expect deg == 225
    case _:
        expect false
```

</details>

#### creates northwest direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point.origin()
expect p.x == 0
```

</details>

#### returns multiple instances correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = Point.origin()
val p2 = Point.unit_x()
expect p1.x == 0
expect p2.x == 1
```

</details>

#### color factory returns Color type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val black = Color.black()
val white = Color.white()
expect black.r == 0
expect white.r == 255
```

</details>

### Static Method Patterns

#### factory pattern

#### provides specialized factory for common case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val origin = Point.origin()
expect origin.x == 0 && origin.y == 0
```

</details>

#### provides multiple factories for different cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagonal = Point.on_diagonal(5)
expect diagonal.x == 5
expect diagonal.y == 5
```

</details>

#### stacks multiple named constructors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = Point.origin()
val p2 = Point.unit_x()
val p3 = Point.from_pair((3, 4))
expect [p1.x, p2.x, p3.x] == [0, 1, 3]
```

</details>

#### color factory variations

#### provides named color factories

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point.origin()
expect true
```

</details>

#### multiple calls to same parameterless factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = Point.origin()
val p2 = Point.origin()
expect p1.x == p2.x && p1.y == p2.y
```

</details>

#### multiple instances

#### creates independent instances

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = Point.origin()
val p2 = Point.unit_x()
expect p1.x != p2.x || p1.y != p2.y
```

</details>

#### records instances independently

1. expect r1 events len
2. expect r2 events len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = CallEventRecorder.new()
val r2 = CallEventRecorder.with_initial_event("test")
expect r1.events.len() == 0
expect r2.events.len() == 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
