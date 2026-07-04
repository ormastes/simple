# Guard Clause Specification

> match value:

<!-- sdn-diagram:id=guard_clause_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=guard_clause_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

guard_clause_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=guard_clause_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guard Clause Specification

match value:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUARD-CLAUSE |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/guard_clause_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
match value:
case pattern if condition:
body
```

## Key Behaviors

- Guard conditions are evaluated after pattern matching succeeds
- Variables bound in the pattern are available in the guard condition
- If the guard evaluates to false, matching continues to the next arm
- Guards can reference external variables from the enclosing scope

## Scenarios

### Guard Clauses

#### basic integer guards

#### matches when guard is true

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> text:
    match x:
        case n if n > 10:
            "large"
        case n if n > 0:
            "small"
        case _:
            "non-positive"
expect classify(15) == "large"
```

</details>

#### falls through when guard is false

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> text:
    match x:
        case n if n > 10:
            "large"
        case n if n > 0:
            "small"
        case _:
            "non-positive"
expect classify(5) == "small"
```

</details>

#### reaches default case when all guards fail

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> text:
    match x:
        case n if n > 10:
            "large"
        case n if n > 0:
            "small"
        case _:
            "non-positive"
expect classify(-5) == "non-positive"
```

</details>

#### guards with equality checks

#### matches exact value via guard

1. fn identify
2. expect identify
3. expect identify
4. expect identify


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identify(x: i64) -> text:
    match x:
        case n if n == 0:
            "zero"
        case n if n == 42:
            "answer"
        case _:
            "other"
expect identify(0) == "zero"
expect identify(42) == "answer"
expect identify(99) == "other"
```

</details>

#### guards with tuple patterns

#### uses bound variables in guard

1. fn check sum
2. expect check sum
3. expect check sum
4. expect check sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn check_sum(pair: (i64, i64)) -> text:
    match pair:
        case (a, b) if a + b > 100:
            "big sum"
        case (a, b) if a == b:
            "equal"
        case _:
            "other"
expect check_sum((60, 50)) == "big sum"
expect check_sum((5, 5)) == "equal"
expect check_sum((1, 2)) == "other"
```

</details>

#### guards with multiple comparisons

1. fn check range
2. expect check range
3. expect check range
4. expect check range


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn check_range(pair: (i64, i64)) -> text:
    match pair:
        case (a, b) if a > 0 && b > 0:
            "both positive"
        case (a, b) if a < 0 && b < 0:
            "both negative"
        case _:
            "mixed"
expect check_range((5, 10)) == "both positive"
expect check_range((-5, -10)) == "both negative"
expect check_range((5, -10)) == "mixed"
```

</details>

#### guards with enum patterns

#### filters enum payload with guard

1. fn categorize
2. expect categorize
3. expect categorize
4. expect categorize
5. expect categorize


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn categorize(v: GuardValue) -> text:
    match v:
        case GuardValue.Num(n) if n > 100:
            "large number"
        case GuardValue.Num(n) if n > 0:
            "small number"
        case GuardValue.Num(n):
            "non-positive"
        case GuardValue.Empty:
            "empty"
expect categorize(GuardValue.Num(200)) == "large number"
expect categorize(GuardValue.Num(50)) == "small number"
expect categorize(GuardValue.Num(-5)) == "non-positive"
expect categorize(GuardValue.Empty) == "empty"
```

</details>

#### guards with external variables

#### references variables from outer scope

1. fn above threshold
2. expect above threshold
3. expect above threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn above_threshold(x: i64, threshold: i64) -> bool:
    match x:
        case n if n > threshold:
            true
        case _:
            false
expect above_threshold(75, 50) == true
expect above_threshold(25, 50) == false
```

</details>

#### guards with complex expressions

#### uses modulo in guard

1. fn parity
2. expect parity
3. expect parity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn parity(x: i64) -> text:
    match x:
        case n if n % 2 == 0:
            "even"
        case _:
            "odd"
expect parity(10) == "even"
expect parity(7) == "odd"
```

</details>

#### uses logical or in guard

1. fn is special
2. expect is special
3. expect is special
4. expect is special
5. expect is special


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn is_special(x: i64) -> bool:
    match x:
        case n if n == 1 || n == 42 || n == 100:
            true
        case _:
            false
expect is_special(1) == true
expect is_special(42) == true
expect is_special(100) == true
expect is_special(50) == false
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
