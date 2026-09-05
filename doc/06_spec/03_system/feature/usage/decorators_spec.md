# Decorators Specification

> Decorators are functions that transform other functions, enabling aspect-oriented programming patterns like logging, caching, and validation.

<!-- sdn-diagram:id=decorators_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=decorators_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

decorators_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=decorators_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Decorators Specification

Decorators are functions that transform other functions, enabling aspect-oriented programming patterns like logging, caching, and validation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DECO-001 |
| Category | Language \| Functions |
| Status | Implemented |
| Source | `test/03_system/feature/usage/decorators_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Decorators are functions that transform other functions, enabling
aspect-oriented programming patterns like logging, caching, and validation.

## Syntax

```simple
# Basic decorator
@double_result
fn add_one(x):
return x + 1

# Decorator with arguments
@multiply_by(3)
fn increment(x):
return x + 1
```

## Scenarios

### Decorators

#### applies basic decorator

1. fn double result
2. fn wrapper
3. fn add one
4. expect add one


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double_result(f):
    fn wrapper(x):
        return f(x) * 2
    return wrapper

@double_result
fn add_one(x):
    return x + 1

expect add_one(5) == 12
```

</details>

#### applies decorator with arguments

1. fn multiply by
2. fn decorator
3. fn wrapper
4. fn increment
5. expect increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multiply_by(factor):
    fn decorator(f):
        fn wrapper(x):
            return f(x) * factor
        return wrapper
    return decorator

@multiply_by(3)
fn increment(x):
    return x + 1

expect increment(10) == 33
```

</details>

#### stacks multiple decorators

1. fn add ten
2. fn wrapper
3. fn double
4. fn wrapper
5. fn identity
6. expect identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add_ten(f):
    fn wrapper(x):
        return f(x) + 10
    return wrapper

fn double(f):
    fn wrapper(x):
        return f(x) * 2
    return wrapper

@add_ten
@double
fn identity(x):
    return x

expect identity(5) == 20  # 5 -> double -> 10 -> add_ten -> 20
```

</details>

#### uses decorator without parentheses

1. fn add five
2. fn wrapper
3. fn square
4. expect square


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add_five(f):
    fn wrapper(x):
        return f(x) + 5
    return wrapper

@add_five
fn square(x):
    return x * x

expect square(4) == 21  # 16 + 5
```

</details>

### Attributes

#### uses inline attribute

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@inline
fn add(a, b):
    return a + b
expect add(3, 4) == 7
```

</details>

#### uses deprecated attribute

1. fn old api
2. expect old api


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@deprecated
fn old_api(x):
    return x * 2
expect old_api(10) == 20
```

</details>

#### uses deprecated with message

1. fn legacy
2. expect legacy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@deprecated("use new_api instead")
fn legacy(x):
    return x + 1
expect legacy(5) == 6
```

</details>

#### stacks multiple attributes

1. fn double
2. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@inline
@deprecated
fn double(x):
    return x * 2
expect double(21) == 42
```

</details>

### Context Managers

#### executes basic with block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = 0
with 42:
    counter = 1
expect counter == 1
```

</details>

#### binds value with as clause

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
with 42 as x:
    val value = x + 1
expect value == 43
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
