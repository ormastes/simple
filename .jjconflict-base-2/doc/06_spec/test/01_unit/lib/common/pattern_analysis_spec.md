# Pattern Analysis Specification

> <details>

<!-- sdn-diagram:id=pattern_analysis_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pattern_analysis_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pattern_analysis_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pattern_analysis_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pattern Analysis Specification

## Scenarios

### Exhaustiveness checking

#### detects non-exhaustive enum matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that enum pattern matching works
val c = Color.Red
val result = match c:
    case Color.Red: 1
    case Color.Green: 2
    case Color.Blue: 3

expect(result).to_equal(1)
```

</details>

#### accepts exhaustive enum matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test exhaustive match with all cases
val s = Status.Success
val result = match s:
    case Status.Success: true
    case Status.Failure: false

expect(result).to_equal(true)
```

</details>

#### handles wildcard patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test wildcard pattern matching
val opt = MyOption.Some(42)
val result = match opt:
    case MyOption.Some(v): v
    case _: 0

expect(result).to_equal(42)
```

</details>

### Unreachable pattern detection

#### detects unreachable patterns after wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that wildcard catches remaining cases
val x = 5
val result = match x:
    case 1: "one"
    case 2: "two"
    case _: "other"

expect(result).to_equal("other")
```

</details>

#### detects duplicate patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test pattern specificity
val v = Value.Int(10)
val result = match v:
    case Value.Int(n): n
    case Value.Float(f): 0

expect(result).to_equal(10)
```

</details>

#### handles nested patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test nested pattern matching
val n = Nested.Inner(42)
val result = match n:
    case Nested.Inner(v): v
    case Nested.Outer: 0

expect(result).to_equal(42)
```

</details>

### Pattern guards

#### evaluates guard conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test pattern matching with conditionals
val x = 10
val result = if x > 5:
    "big"
else:
    "small"

expect(result).to_equal("big")
```

</details>

#### allows overlapping patterns with guards

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test multiple pattern branches
val x = 3
val result = match x:
    case 1: "one"
    case 2: "two"
    case 3: "three"
    case _: "many"

expect(result).to_equal("three")
```

</details>

### Or patterns

#### matches multiple alternatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test matching multiple values
val x = 2
val result = if x == 1 or x == 2 or x == 3:
    "low"
else:
    "high"

expect(result).to_equal("low")
```

</details>

#### binds variables consistently

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test variable binding in patterns
val e = Either.Left(42)
val result = match e:
    case Either.Left(v): v
    case Either.Right(v): v

expect(result).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pattern_analysis_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Exhaustiveness checking
- Unreachable pattern detection
- Pattern guards
- Or patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
