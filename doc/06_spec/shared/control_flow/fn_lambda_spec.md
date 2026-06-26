# Lambda Syntax fn() Specification

> @platform: all

<!-- sdn-diagram:id=fn_lambda_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fn_lambda_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fn_lambda_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fn_lambda_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lambda Syntax fn() Specification

@platform: all

## At a Glance

| Field | Value |
|-------|-------|
| Category | Syntax |
| Status | Implemented |
| Source | `test/shared/control_flow/fn_lambda_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@platform: all
Tests for fn() lambda syntax and its interchangeability with the \\ operator.
The fn() syntax provides an alternative way to define lambdas and is compatible
with BDD framework blocks like describe/context/it.

## Scenarios

### fn() Lambda Syntax

### basic inline lambdas

#### supports fn() with no parameters

1. fn call it
2. f


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn call_it(f) -> i64:
    f()

val result = call_it(fn(): 42)
expect result == 42
```

</details>

#### supports fn(x) with single parameter

1. fn apply
2. f


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(x: i64, f) -> i64:
    f(x)

val result = apply(5, fn(n): n * 2)
expect result == 10
```

</details>

#### supports fn(x, y) with multiple parameters

1. fn apply2
2. f


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply2(x: i64, y: i64, f) -> i64:
    f(x, y)

val result = apply2(3, 4, fn(a, b): a + b)
expect result == 7
```

</details>

### block lambdas

#### supports fn() with indented block

1. fn execute
2. f
3. fn sum xy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn execute(f) -> i64:
    f()

fn sum_xy() -> i64:
    val x = 10
    val y = 20
    x + y

val result = execute(sum_xy)
expect result == 30
```

</details>

#### supports fn(x) with parameter and block

1. fn transform
2. f
3. fn compute square


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn transform(x: i64, f) -> i64:
    f(x)

fn compute_square(n) -> i64:
    val doubled = n * 2
    val squared = doubled * doubled
    squared

val result = transform(5, compute_square)
expect result == 100
```

</details>

### nested lambdas

#### supports nested fn() lambdas

1. fn outer
2. fn inner
3. g


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer(f):
    f

fn inner(g) -> i64:
    g()

val result = inner(outer(fn(): 99))
expect result == 99
```

</details>

### compatibility with backslash operator

#### fn() and \\ are interchangeable

1. fn test sum
2. f1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_sum(f1, f2) -> i64:
    f1() + f2()

# Mix both syntaxes
val result = test_sum(fn(): 10, \: 20)
expect result == 30
```

</details>

### used in BDD framework

#### works with context/it blocks

1. fn mock context
2. block
3. fn set executed
4. mock context


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false

fn mock_context(name: text, block):
    block()

fn set_executed():
    executed = true

mock_context("test", set_executed)

expect executed == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
