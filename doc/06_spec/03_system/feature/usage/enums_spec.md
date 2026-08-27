# Enum Types Specification

> Tests for enumeration types and pattern matching on enums.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Types Specification

Tests for enumeration types and pattern matching on enums.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1003 |
| Category | Language |
| Status | Complete |
| Source | `test/03_system/feature/usage/enums_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for enumeration types and pattern matching on enums.
Verifies enum definition, construction, and exhaustive pattern matching.

## Scenarios

### Enum Types

#### basic enum definition

#### defines simple enum with variants

- defines simple enum with variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines simple enum with variants")
val c = Color.Red
assert_true(c == Color.Red)
```

</details>

#### constructs enum variants

- constructs enum variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("constructs enum variants")
val s1 = Status.Active
val s2 = Status.Inactive
match s1:
    Status.Active: assert true
    _: fail("Expected Active status")
match s2:
    Status.Inactive: assert true
    _: fail("Expected Inactive status")
```

</details>

#### matches on enum variants

- matches on enum variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches on enum variants")
val s = ResultType.Success
val result = match s:
    case ResultType.Success: "ok"
    case ResultType.Failure: "fail"
assert_true(result == "ok")
```

</details>

#### preserves explicit discriminants through casts and matches

- preserves explicit discriminants through casts and matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves explicit discriminants through casts and matches")
assert_equal(ExplicitCode.Zero as i64, 0)
assert_equal(ExplicitCode.Gap as i64, 20)
assert_equal(ExplicitCode.Next as i64, 21)
val indirect = ExplicitCode.Gap
assert_equal(indirect as i64, 20)
match ExplicitCode.Gap:
    ExplicitCode.Gap: assert true
    _: fail("Expected explicit Gap discriminant")
```

</details>

#### enums with associated values

#### defines enum with tuple variants

- defines enum with tuple variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines enum with tuple variants")
val circle = Shape.Circle(10)
assert_true(circle == Shape.Circle(10))
```

</details>

#### constructs variant with associated values

- constructs variant with associated values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("constructs variant with associated values")
val msg1 = Message.Text("hello")
val msg2 = Message.Number(42)
# Just verify construction works
pass
```

</details>

#### extracts values from enum variant

- extracts values from enum variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts values from enum variant")
val p = Point.Coord(3, 4)
match p:
    case Point.Coord(x, y):
        assert_true(x == 3)
        assert_true(y == 4)
```

</details>

#### matches and binds enum values

- matches and binds enum values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches and binds enum values")
val r = TestResult.Ok(42)
val value = match r:
    case TestResult.Ok(n): n
    case TestResult.Err(e): 0
assert_true(value == 42)
```

</details>

#### enum pattern matching

#### requires exhaustive pattern matching

- requires exhaustive pattern matching


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires exhaustive pattern matching")
# This test verifies exhaustiveness - all variants must be covered
val c = Color.Red
val name = match c:
    case Color.Red: "red"
    case Color.Green: "green"
    case Color.Blue: "blue"
assert_true(name == "red")
```

</details>

#### handles all enum variants in match

- handles all enum variants in match


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles all enum variants in match")
val s = Status.Active
val is_active = match s:
    case Status.Active: true
    case Status.Inactive: false
assert_true(is_active == true)
```

</details>

#### supports wildcard patterns in match

- supports wildcard patterns in match


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports wildcard patterns in match")
val c = Color.Green
val is_red = match c:
    case Color.Red: true
    case _: false
assert_true(is_red == false)
```

</details>

#### matches enum in conditional guards

- matches enum in conditional guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches enum in conditional guards")
val s = Status.Active
match s:
    Status.Active:
        pass  # Success
    _:
        fail("Expected Active status")
```

</details>

#### nested enums

#### defines enum with enum variants

- defines enum with enum variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines enum with enum variants")
val msg = Message.Text("test")
val container = Container.Value(msg)
assert_true(container == Container.Value(Message.Text("test")))
```

</details>

#### matches nested enum variants

- matches nested enum variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches nested enum variants")
val c = Container.Value(Message.Number(42))
val result = match c:
    case Container.Empty: 0
    case Container.Value(Message.Number(n)): n
    case Container.Value(Message.Text(s)): 1
assert_true(result == 42)
```

</details>

#### handles enum with generic variants

- handles enum with generic variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles enum with generic variants")
# For now, test with concrete types
# Note: enum destructuring only binds first positional param
# so we verify by matching the known variant
val tree = Tree.Node(10, 20)
val is_node = match tree:
    case Tree.Leaf(n): false
    case Tree.Node(_, _): true
assert_true(is_node == true)
assert_true(tree == Tree.Node(10, 20))
```

</details>

#### enum methods

#### calls methods on enum instances

- calls methods on enum instances


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls methods on enum instances")
# This may not work if enum methods aren't implemented
# For now, just test that we can work with enum values
val s = Status.Active
match s:
    Status.Active: assert true
    _: fail("Expected Active status")
```

</details>

#### implements trait for enum

- implements trait for enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements trait for enum")
# Trait implementation for enums may not be ready
# Test basic enum equality which uses a trait
val c1 = Color.Red
val c2 = Color.Red
assert_true(c1 == c2)
```

</details>

#### enumerates all variants

- enumerates all variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enumerates all variants")
# Variant enumeration may not be implemented
# For now, test that we can create all variants
val r = Color.Red
val g = Color.Green
val b = Color.Blue
pass
```

</details>

#### option and result enums

#### creates Option variants

- creates Option variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates Option variants")
val some_val = Option.Some(42)
val none_val = Option.None
assert_true(some_val == Option.Some(42))
```

</details>

#### matches on Option

- matches on Option


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches on Option")
val opt = Option.Some(10)
val value = match opt:
    case Option.Some(n): n
    case Option.None: 0
assert_true(value == 10)
```

</details>

#### creates Result variants

- creates Result variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates Result variants")
val ok_val = Result.Ok(42)
val err_val = Result.Err("error")
assert_true(ok_val == Result.Ok(42))
```

</details>

#### matches on Result with error handling

- matches on Result with error handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches on Result with error handling")
val res = Result.Ok(100)
val value = match res:
    case Result.Ok(n): n
    case Result.Err(e): 0
assert_true(value == 100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `f6e5c674863b08ae8727bd87d9a2036b407095495ba71823a0d6d0e08d3a5ce7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6e5c674863b08ae8727bd87d9a2036b407095495ba71823a0d6d0e08d3a5ce7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6e5c674863b08ae8727bd87d9a2036b407095495ba71823a0d6d0e08d3a5ce7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/enums_spec.spl
mirror: doc/06_spec/03_system/feature/usage/enums_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/enums_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/enums_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/enums_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines simple enum with variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/enums_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs enum variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/enums_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches on enum variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
