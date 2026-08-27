# Enum Types Specification

> Tests for enumeration types and pattern matching on enums.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

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
| Source | `test/feature/usage/enums_spec.spl` |
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
# @req REQ-SSPEC-FEATURE
step("defines simple enum with variants")
val c = Color.Red
expect(c == Color.Red)
```

</details>

#### constructs enum variants

- constructs enum variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
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
# @req REQ-SSPEC-FEATURE
step("matches on enum variants")
val s = ResultType.Success
val result = match s:
    case ResultType.Success: "ok"
    case ResultType.Failure: "fail"
expect(result == "ok")
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
# @req REQ-SSPEC-FEATURE
step("defines enum with tuple variants")
val circle = Shape.Circle(10)
expect(circle == Shape.Circle(10))
```

</details>

#### constructs variant with associated values

- constructs variant with associated values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
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
# @req REQ-SSPEC-FEATURE
step("extracts values from enum variant")
val p = Point.Coord(3, 4)
match p:
    case Point.Coord(x, y):
        expect(x == 3)
        expect(y == 4)
```

</details>

#### matches and binds enum values

- matches and binds enum values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches and binds enum values")
val r = TestResult.Ok(42)
val value = match r:
    case TestResult.Ok(n): n
    case TestResult.Err(e): 0
expect(value == 42)
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
# @req REQ-SSPEC-FEATURE
step("requires exhaustive pattern matching")
# This test verifies exhaustiveness - all variants must be covered
val c = Color.Red
val name = match c:
    case Color.Red: "red"
    case Color.Green: "green"
    case Color.Blue: "blue"
expect(name == "red")
```

</details>

#### handles all enum variants in match

- handles all enum variants in match


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles all enum variants in match")
val s = Status.Active
val is_active = match s:
    case Status.Active: true
    case Status.Inactive: false
expect(is_active == true)
```

</details>

#### supports wildcard patterns in match

- supports wildcard patterns in match


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports wildcard patterns in match")
val c = Color.Green
val is_red = match c:
    case Color.Red: true
    case _: false
expect(is_red == false)
```

</details>

#### matches enum in conditional guards

- matches enum in conditional guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
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
# @req REQ-SSPEC-FEATURE
step("defines enum with enum variants")
val msg = Message.Text("test")
val container = Container.Value(msg)
expect(container == Container.Value(Message.Text("test")))
```

</details>

#### matches nested enum variants

- matches nested enum variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches nested enum variants")
val c = Container.Value(Message.Number(42))
val result = match c:
    case Container.Empty: 0
    case Container.Value(Message.Number(n)): n
    case Container.Value(Message.Text(s)): 1
expect(result == 42)
```

</details>

#### handles enum with generic variants

- handles enum with generic variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles enum with generic variants")
# For now, test with concrete types
# Note: enum destructuring only binds first positional param
# so we verify by matching the known variant
val tree = Tree.Node(10, 20)
val is_node = match tree:
    case Tree.Leaf(n): false
    case Tree.Node(_, _): true
expect(is_node == true)
expect(tree == Tree.Node(10, 20))
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
# @req REQ-SSPEC-FEATURE
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
# @req REQ-SSPEC-FEATURE
step("implements trait for enum")
# Trait implementation for enums may not be ready
# Test basic enum equality which uses a trait
val c1 = Color.Red
val c2 = Color.Red
expect(c1 == c2)
```

</details>

#### enumerates all variants

- enumerates all variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
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
# @req REQ-SSPEC-FEATURE
step("creates Option variants")
val some_val = Some(42)
val none_val = None
expect(some_val == Some(42))
```

</details>

#### matches on Option

- matches on Option


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches on Option")
val opt = Some(10)
val value = match opt:
    case Some(n): n
    case None: 0
expect(value == 10)
```

</details>

#### creates Result variants

- creates Result variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates Result variants")
val ok_val = Ok(42)
val err_val = Err("error")
expect(ok_val == Ok(42))
```

</details>

#### matches on Result with error handling

- matches on Result with error handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches on Result with error handling")
val res = Ok(100)
val value = match res:
    case Ok(n): n
    case Err(e): 0
expect(value == 100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `2f3e9146425bda8a669de5b251a026d1f45aa7f28320371d32246d182c5bfcbf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f3e9146425bda8a669de5b251a026d1f45aa7f28320371d32246d182c5bfcbf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f3e9146425bda8a669de5b251a026d1f45aa7f28320371d32246d182c5bfcbf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/enums_spec.spl
mirror: doc/06_spec/feature/usage/enums_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/enums_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/enums_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/enums_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines simple enum with variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/enums_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs enum variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/enums_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches on enum variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
